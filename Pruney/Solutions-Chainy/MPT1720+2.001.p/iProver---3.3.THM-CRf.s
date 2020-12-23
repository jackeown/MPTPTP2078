%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:07 EST 2020

% Result     : Theorem 51.39s
% Output     : CNFRefutation 51.39s
% Verified   : 
% Statistics : Number of formulae       :  268 (16561 expanded)
%              Number of clauses        :  198 (4038 expanded)
%              Number of leaves         :   18 (5692 expanded)
%              Depth                    :   28
%              Number of atoms          : 1255 (150360 expanded)
%              Number of equality atoms :  580 (6090 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f42,f41,f40,f39])).

fof(f64,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
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

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_952,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_954,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | k1_tsep_1(X1,X2,X0) = k1_tsep_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_970,plain,
    ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2151,plain,
    ( k1_tsep_1(sK0,sK2,X0) = k1_tsep_1(sK0,X0,sK2)
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_954,c_970])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_28,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_30,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_33,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8684,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | k1_tsep_1(sK0,sK2,X0) = k1_tsep_1(sK0,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2151,c_28,c_30,c_33])).

cnf(c_8685,plain,
    ( k1_tsep_1(sK0,sK2,X0) = k1_tsep_1(sK0,X0,sK2)
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_8684])).

cnf(c_8692,plain,
    ( k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2)
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_8685])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_7716,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | ~ m1_pre_topc(sK1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0)
    | k1_tsep_1(X0,sK2,sK1) = k1_tsep_1(X0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7719,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_7716])).

cnf(c_9196,plain,
    ( k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8692,c_27,c_25,c_24,c_23,c_22,c_21,c_7719])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_956,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2150,plain,
    ( k1_tsep_1(sK0,sK3,X0) = k1_tsep_1(sK0,X0,sK3)
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_956,c_970])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_35,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7821,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | k1_tsep_1(sK0,sK3,X0) = k1_tsep_1(sK0,X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2150,c_28,c_30,c_35])).

cnf(c_7822,plain,
    ( k1_tsep_1(sK0,sK3,X0) = k1_tsep_1(sK0,X0,sK3)
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7821])).

cnf(c_7831,plain,
    ( k1_tsep_1(sK0,sK3,sK1) = k1_tsep_1(sK0,sK1,sK3)
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_952,c_7822])).

cnf(c_1699,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | k1_tsep_1(sK0,sK3,sK1) = k1_tsep_1(sK0,sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_8168,plain,
    ( k1_tsep_1(sK0,sK3,sK1) = k1_tsep_1(sK0,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7831,c_27,c_25,c_24,c_23,c_20,c_19,c_1699])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X3),k1_tsep_1(X1,X2,X4))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_963,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X3,X4) != iProver_top
    | m1_pre_topc(X4,X1) != iProver_top
    | m1_pre_topc(X3,X1) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1,X0,X3),k1_tsep_1(X1,X2,X4)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8173,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,X0,X1)) = iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8168,c_963])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_29,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_31,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_32,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_36,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_149650,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,X0,X1)) = iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8173,c_28,c_29,c_30,c_31,c_32,c_35,c_36])).

cnf(c_149651,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,X0,X1)) = iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_149650])).

cnf(c_149665,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_9196,c_149651])).

cnf(c_13,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_962,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_967,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9198,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9196,c_967])).

cnf(c_34,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_78366,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9198,c_28,c_29,c_30,c_31,c_32,c_33,c_34])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_961,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_78374,plain,
    ( m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_78366,c_961])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_969,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_972,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2130,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(k1_tsep_1(X1,X0,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_969,c_972])).

cnf(c_11467,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9196,c_2130])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_971,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2131,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k1_tsep_1(X1,X0,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_969,c_971])).

cnf(c_11748,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9196,c_2131])).

cnf(c_78724,plain,
    ( m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_78374,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_11467,c_11748])).

cnf(c_78731,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_962,c_78724])).

cnf(c_78749,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_78731,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_9198,c_11748])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_974,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_78753,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = u1_struct_0(sK2)
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_78749,c_974])).

cnf(c_44,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_46,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_1298,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK2,X1)
    | ~ m1_pre_topc(sK2,X0)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1303,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1298])).

cnf(c_1305,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1303])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_964,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1844,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_954,c_964])).

cnf(c_4048,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1844,c_28,c_29,c_30,c_33])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_973,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_960,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) = iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1607,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_973,c_960])).

cnf(c_67,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2845,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(X0,X0) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1607,c_44,c_67])).

cnf(c_2846,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2845])).

cnf(c_2856,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_954,c_2846])).

cnf(c_1155,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_4,c_21])).

cnf(c_1156,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1155])).

cnf(c_1945,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1950,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1945])).

cnf(c_3127,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2856,c_30,c_1156,c_1950])).

cnf(c_3134,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,sK2,sK2)
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3127,c_964])).

cnf(c_1639,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_3,c_21])).

cnf(c_1640,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1639])).

cnf(c_3869,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3134,c_29,c_30,c_33,c_1156,c_1640])).

cnf(c_4052,plain,
    ( k1_tsep_1(sK2,sK2,sK2) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_4048,c_3869])).

cnf(c_30672,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK2)) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4052,c_967])).

cnf(c_31928,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30672,c_29,c_30,c_33,c_1156,c_1640,c_1950])).

cnf(c_31936,plain,
    ( m1_pre_topc(X0,k1_tsep_1(sK0,sK2,sK2)) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) != iProver_top
    | v2_pre_topc(k1_tsep_1(sK0,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_31928,c_961])).

cnf(c_2262,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_pre_topc(X3,k1_tsep_1(X1,X0,X2)) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X3)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k1_tsep_1(X1,X0,X2)) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(k1_tsep_1(X1,X0,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_961])).

cnf(c_12980,plain,
    ( v2_pre_topc(X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_pre_topc(X3,k1_tsep_1(X1,X0,X2)) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X3)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2262,c_2130,c_2131])).

cnf(c_12981,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_pre_topc(X3,k1_tsep_1(X1,X0,X2)) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X3)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_12980])).

cnf(c_30668,plain,
    ( m1_pre_topc(X0,k1_tsep_1(sK0,sK2,sK2)) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4052,c_12981])).

cnf(c_32807,plain,
    ( m1_pre_topc(X0,k1_tsep_1(sK0,sK2,sK2)) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31936,c_29,c_30,c_33,c_1156,c_1640,c_1950,c_30668])).

cnf(c_32814,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK2)) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(k1_tsep_1(sK0,sK2,sK2))) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_962,c_32807])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_958,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2147,plain,
    ( k1_tsep_1(X0,X0,X1) = k1_tsep_1(X0,X1,X0)
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_962,c_970])).

cnf(c_4203,plain,
    ( k1_tsep_1(sK2,sK3,sK2) = k1_tsep_1(sK2,sK2,sK3)
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_958,c_2147])).

cnf(c_4432,plain,
    ( k1_tsep_1(sK2,sK3,sK2) = k1_tsep_1(sK2,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4203,c_30,c_33,c_35,c_1156])).

cnf(c_4434,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK2,sK3,sK2)) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4432,c_967])).

cnf(c_38,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16535,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK2,sK3,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4434,c_29,c_30,c_33,c_35,c_38,c_1156,c_1640,c_1950])).

cnf(c_16544,plain,
    ( k1_tsep_1(k1_tsep_1(sK2,sK3,sK2),sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | v2_struct_0(k1_tsep_1(sK2,sK3,sK2)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK2,sK3,sK2)) != iProver_top
    | v2_pre_topc(k1_tsep_1(sK2,sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16535,c_964])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_968,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(k1_tsep_1(X1,X0,X2)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4436,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(k1_tsep_1(sK2,sK3,sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4432,c_968])).

cnf(c_4435,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK2),sK2) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4432,c_969])).

cnf(c_1334,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | m1_pre_topc(k1_tsep_1(sK2,X0,X1),sK2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1944,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | m1_pre_topc(k1_tsep_1(sK2,X0,sK2),sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1334])).

cnf(c_3994,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK2),sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1944])).

cnf(c_3995,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK2),sK2) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3994])).

cnf(c_9415,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK2),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4435,c_30,c_33,c_35,c_38,c_1156,c_1950,c_3995])).

cnf(c_9424,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(k1_tsep_1(sK2,sK3,sK2)) = iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9415,c_972])).

cnf(c_9425,plain,
    ( l1_pre_topc(k1_tsep_1(sK2,sK3,sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9415,c_971])).

cnf(c_20512,plain,
    ( k1_tsep_1(k1_tsep_1(sK2,sK3,sK2),sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16544,c_29,c_30,c_33,c_35,c_38,c_1156,c_1640,c_1950,c_4436,c_9424,c_9425])).

cnf(c_20529,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),k1_tsep_1(sK2,sK3,sK2)) = iProver_top
    | m1_pre_topc(sK2,k1_tsep_1(sK2,sK3,sK2)) != iProver_top
    | v2_struct_0(k1_tsep_1(sK2,sK3,sK2)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK2,sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20512,c_969])).

cnf(c_21729,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),k1_tsep_1(sK2,sK3,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20529,c_29,c_30,c_33,c_35,c_38,c_1156,c_1640,c_1950,c_4434,c_4436,c_9425])).

cnf(c_21746,plain,
    ( l1_pre_topc(k1_tsep_1(sK2,sK3,sK2)) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_21729,c_971])).

cnf(c_458,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2981,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k1_tsep_1(X1,X0,X0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v2_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_11,c_458])).

cnf(c_2695,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k1_tsep_1(X1,X0,X2)) ),
    inference(resolution,[status(thm)],[c_6,c_4])).

cnf(c_7871,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v2_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_2981,c_2695])).

cnf(c_15707,plain,
    ( v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_7871,c_21])).

cnf(c_15708,plain,
    ( v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15707])).

cnf(c_21800,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21746,c_28,c_29,c_30,c_33,c_15708])).

cnf(c_21808,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4048,c_21800])).

cnf(c_33019,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(k1_tsep_1(sK0,sK2,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32814,c_29,c_30,c_33,c_1156,c_1640,c_1950,c_21808,c_30672])).

cnf(c_33023,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = u1_struct_0(sK2)
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK2,sK2)),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_33019,c_974])).

cnf(c_30673,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK2) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4052,c_969])).

cnf(c_31877,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30673,c_30,c_33,c_1156,c_1950])).

cnf(c_31885,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),X0) != iProver_top
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK2,sK2)),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_31877,c_961])).

cnf(c_32498,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),X0) != iProver_top
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK2,sK2)),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31885,c_29,c_30,c_1156,c_1640])).

cnf(c_3133,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3127,c_961])).

cnf(c_6792,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3133,c_29,c_30,c_1156,c_1640])).

cnf(c_6798,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK2)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6792,c_974])).

cnf(c_32508,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = u1_struct_0(sK2)
    | m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK2) != iProver_top
    | m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK2)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_32498,c_6798])).

cnf(c_33031,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33023,c_29,c_30,c_33,c_1156,c_1640,c_1950,c_30672,c_30673,c_32508])).

cnf(c_9199,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9196,c_969])).

cnf(c_16055,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9199,c_28,c_30,c_31,c_32,c_33,c_34])).

cnf(c_16063,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0) != iProver_top
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16055,c_961])).

cnf(c_16318,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0) != iProver_top
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16063,c_29,c_30])).

cnf(c_33045,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK2)) != iProver_top
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_33031,c_16318])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_957,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_965,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X2,X0)
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2285,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,X0,sK2)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_954,c_965])).

cnf(c_17055,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,X0,sK2)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2285,c_28,c_29,c_30,c_33])).

cnf(c_17064,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2)
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_957,c_17055])).

cnf(c_2783,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(sK2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(X1,X0,sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_5145,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | ~ m1_pre_topc(sK1,X0)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(X0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2783])).

cnf(c_5147,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_5145])).

cnf(c_17227,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17064,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_18,c_5147])).

cnf(c_31937,plain,
    ( k1_tsep_1(k1_tsep_1(sK0,sK2,sK2),sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK2,sK2)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) != iProver_top
    | v2_pre_topc(k1_tsep_1(sK0,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_31928,c_964])).

cnf(c_20530,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK2,sK3,sK2)) != iProver_top
    | v2_struct_0(k1_tsep_1(sK2,sK3,sK2)) = iProver_top
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK2,sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20512,c_968])).

cnf(c_20831,plain,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20530,c_29,c_30,c_33,c_35,c_38,c_1156,c_1640,c_1950,c_4434,c_4436,c_9425])).

cnf(c_20839,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4048,c_20831])).

cnf(c_21745,plain,
    ( l1_pre_topc(k1_tsep_1(sK2,sK3,sK2)) != iProver_top
    | v2_pre_topc(k1_tsep_1(sK2,sK3,sK2)) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_21729,c_972])).

cnf(c_456,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2980,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k1_tsep_1(X1,X0,X0))
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(resolution,[status(thm)],[c_11,c_456])).

cnf(c_2696,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k1_tsep_1(X1,X0,X2)) ),
    inference(resolution,[status(thm)],[c_6,c_3])).

cnf(c_7853,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(resolution,[status(thm)],[c_2980,c_2696])).

cnf(c_15527,plain,
    ( v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_7853,c_21])).

cnf(c_15528,plain,
    ( v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15527])).

cnf(c_21943,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21745,c_28,c_29,c_30,c_33,c_15528])).

cnf(c_21951,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4048,c_21943])).

cnf(c_33491,plain,
    ( k1_tsep_1(k1_tsep_1(sK0,sK2,sK2),sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31937,c_33,c_20839,c_21808,c_21951])).

cnf(c_33508,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),k1_tsep_1(sK0,sK2,sK2)) = iProver_top
    | m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK2)) != iProver_top
    | v2_struct_0(k1_tsep_1(sK0,sK2,sK2)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_33491,c_969])).

cnf(c_35217,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),k1_tsep_1(sK0,sK2,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33508,c_29,c_30,c_33,c_1156,c_1640,c_1950,c_20839,c_21808,c_30672])).

cnf(c_35221,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_17227,c_35217])).

cnf(c_33081,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),X1) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_33031,c_960])).

cnf(c_45967,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),X0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_969,c_33081])).

cnf(c_45976,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_45967])).

cnf(c_79282,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_78753,c_28,c_29,c_30,c_33,c_34,c_46,c_1305,c_33045,c_35221,c_45976])).

cnf(c_8171,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8168,c_969])).

cnf(c_1422,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1425,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1422])).

cnf(c_15380,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8171,c_28,c_30,c_31,c_32,c_35,c_36,c_1425])).

cnf(c_15388,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0) != iProver_top
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15380,c_961])).

cnf(c_15834,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0) != iProver_top
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15388,c_29,c_30])).

cnf(c_79324,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_79282,c_15834])).

cnf(c_2854,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_957,c_2846])).

cnf(c_1079,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK2,X0)
    | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1080,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1079])).

cnf(c_1082,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1080])).

cnf(c_16,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_39,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_149665,c_79324,c_9199,c_2854,c_1425,c_1156,c_1082,c_39,c_38,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:03:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 51.39/6.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.39/6.99  
% 51.39/6.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.39/6.99  
% 51.39/6.99  ------  iProver source info
% 51.39/6.99  
% 51.39/6.99  git: date: 2020-06-30 10:37:57 +0100
% 51.39/6.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.39/6.99  git: non_committed_changes: false
% 51.39/6.99  git: last_make_outside_of_git: false
% 51.39/6.99  
% 51.39/6.99  ------ 
% 51.39/6.99  ------ Parsing...
% 51.39/6.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.39/6.99  
% 51.39/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 51.39/6.99  
% 51.39/6.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.39/6.99  
% 51.39/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.39/6.99  ------ Proving...
% 51.39/6.99  ------ Problem Properties 
% 51.39/6.99  
% 51.39/6.99  
% 51.39/6.99  clauses                                 27
% 51.39/6.99  conjectures                             12
% 51.39/6.99  EPR                                     16
% 51.39/6.99  Horn                                    19
% 51.39/6.99  unary                                   13
% 51.39/6.99  binary                                  1
% 51.39/6.99  lits                                    104
% 51.39/6.99  lits eq                                 5
% 51.39/6.99  fd_pure                                 0
% 51.39/6.99  fd_pseudo                               0
% 51.39/6.99  fd_cond                                 0
% 51.39/6.99  fd_pseudo_cond                          1
% 51.39/6.99  AC symbols                              0
% 51.39/6.99  
% 51.39/6.99  ------ Input Options Time Limit: Unbounded
% 51.39/6.99  
% 51.39/6.99  
% 51.39/6.99  ------ 
% 51.39/6.99  Current options:
% 51.39/6.99  ------ 
% 51.39/6.99  
% 51.39/6.99  
% 51.39/6.99  
% 51.39/6.99  
% 51.39/6.99  ------ Proving...
% 51.39/6.99  
% 51.39/6.99  
% 51.39/6.99  % SZS status Theorem for theBenchmark.p
% 51.39/6.99  
% 51.39/6.99  % SZS output start CNFRefutation for theBenchmark.p
% 51.39/6.99  
% 51.39/6.99  fof(f12,conjecture,(
% 51.39/6.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 51.39/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.39/6.99  
% 51.39/6.99  fof(f13,negated_conjecture,(
% 51.39/6.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 51.39/6.99    inference(negated_conjecture,[],[f12])).
% 51.39/6.99  
% 51.39/6.99  fof(f33,plain,(
% 51.39/6.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 51.39/6.99    inference(ennf_transformation,[],[f13])).
% 51.39/6.99  
% 51.39/6.99  fof(f34,plain,(
% 51.39/6.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 51.39/6.99    inference(flattening,[],[f33])).
% 51.39/6.99  
% 51.39/6.99  fof(f42,plain,(
% 51.39/6.99    ( ! [X2,X0,X1] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(X0,X1,sK3),X2) & m1_pre_topc(sK3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 51.39/6.99    introduced(choice_axiom,[])).
% 51.39/6.99  
% 51.39/6.99  fof(f41,plain,(
% 51.39/6.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(X1,sK2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 51.39/6.99    introduced(choice_axiom,[])).
% 51.39/6.99  
% 51.39/6.99  fof(f40,plain,(
% 51.39/6.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 51.39/6.99    introduced(choice_axiom,[])).
% 51.39/6.99  
% 51.39/6.99  fof(f39,plain,(
% 51.39/6.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 51.39/6.99    introduced(choice_axiom,[])).
% 51.39/6.99  
% 51.39/6.99  fof(f43,plain,(
% 51.39/6.99    (((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 51.39/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f42,f41,f40,f39])).
% 51.39/6.99  
% 51.39/6.99  fof(f64,plain,(
% 51.39/6.99    m1_pre_topc(sK1,sK0)),
% 51.39/6.99    inference(cnf_transformation,[],[f43])).
% 51.39/6.99  
% 51.39/6.99  fof(f66,plain,(
% 51.39/6.99    m1_pre_topc(sK2,sK0)),
% 51.39/6.99    inference(cnf_transformation,[],[f43])).
% 51.39/6.99  
% 51.39/6.99  fof(f4,axiom,(
% 51.39/6.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1))),
% 51.39/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.39/6.99  
% 51.39/6.99  fof(f18,plain,(
% 51.39/6.99    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 51.39/6.99    inference(ennf_transformation,[],[f4])).
% 51.39/6.99  
% 51.39/6.99  fof(f19,plain,(
% 51.39/6.99    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 51.39/6.99    inference(flattening,[],[f18])).
% 51.39/6.99  
% 51.39/6.99  fof(f49,plain,(
% 51.39/6.99    ( ! [X2,X0,X1] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.39/6.99    inference(cnf_transformation,[],[f19])).
% 51.39/6.99  
% 51.39/6.99  fof(f60,plain,(
% 51.39/6.99    ~v2_struct_0(sK0)),
% 51.39/6.99    inference(cnf_transformation,[],[f43])).
% 51.39/6.99  
% 51.39/6.99  fof(f62,plain,(
% 51.39/6.99    l1_pre_topc(sK0)),
% 51.39/6.99    inference(cnf_transformation,[],[f43])).
% 51.39/6.99  
% 51.39/6.99  fof(f65,plain,(
% 51.39/6.99    ~v2_struct_0(sK2)),
% 51.39/6.99    inference(cnf_transformation,[],[f43])).
% 51.39/6.99  
% 51.39/6.99  fof(f63,plain,(
% 51.39/6.99    ~v2_struct_0(sK1)),
% 51.39/6.99    inference(cnf_transformation,[],[f43])).
% 51.39/6.99  
% 51.39/6.99  fof(f68,plain,(
% 51.39/6.99    m1_pre_topc(sK3,sK0)),
% 51.39/6.99    inference(cnf_transformation,[],[f43])).
% 51.39/6.99  
% 51.39/6.99  fof(f67,plain,(
% 51.39/6.99    ~v2_struct_0(sK3)),
% 51.39/6.99    inference(cnf_transformation,[],[f43])).
% 51.39/6.99  
% 51.39/6.99  fof(f9,axiom,(
% 51.39/6.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))))))))),
% 51.39/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.39/6.99  
% 51.39/6.99  fof(f28,plain,(
% 51.39/6.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) | (~m1_pre_topc(X3,X4) | ~m1_pre_topc(X1,X2))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.39/6.99    inference(ennf_transformation,[],[f9])).
% 51.39/6.99  
% 51.39/6.99  fof(f29,plain,(
% 51.39/6.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.39/6.99    inference(flattening,[],[f28])).
% 51.39/6.99  
% 51.39/6.99  fof(f56,plain,(
% 51.39/6.99    ( ! [X4,X2,X0,X3,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.39/6.99    inference(cnf_transformation,[],[f29])).
% 51.39/6.99  
% 51.39/6.99  fof(f61,plain,(
% 51.39/6.99    v2_pre_topc(sK0)),
% 51.39/6.99    inference(cnf_transformation,[],[f43])).
% 51.39/6.99  
% 51.39/6.99  fof(f10,axiom,(
% 51.39/6.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 51.39/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.39/6.99  
% 51.39/6.99  fof(f30,plain,(
% 51.39/6.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 51.39/6.99    inference(ennf_transformation,[],[f10])).
% 51.39/6.99  
% 51.39/6.99  fof(f57,plain,(
% 51.39/6.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 51.39/6.99    inference(cnf_transformation,[],[f30])).
% 51.39/6.99  
% 51.39/6.99  fof(f6,axiom,(
% 51.39/6.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 51.39/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.39/6.99  
% 51.39/6.99  fof(f22,plain,(
% 51.39/6.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.39/6.99    inference(ennf_transformation,[],[f6])).
% 51.39/6.99  
% 51.39/6.99  fof(f23,plain,(
% 51.39/6.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.39/6.99    inference(flattening,[],[f22])).
% 51.39/6.99  
% 51.39/6.99  fof(f52,plain,(
% 51.39/6.99    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.39/6.99    inference(cnf_transformation,[],[f23])).
% 51.39/6.99  
% 51.39/6.99  fof(f11,axiom,(
% 51.39/6.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 51.39/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.39/6.99  
% 51.39/6.99  fof(f31,plain,(
% 51.39/6.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 51.39/6.99    inference(ennf_transformation,[],[f11])).
% 51.39/6.99  
% 51.39/6.99  fof(f32,plain,(
% 51.39/6.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 51.39/6.99    inference(flattening,[],[f31])).
% 51.39/6.99  
% 51.39/6.99  fof(f38,plain,(
% 51.39/6.99    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 51.39/6.99    inference(nnf_transformation,[],[f32])).
% 51.39/6.99  
% 51.39/6.99  fof(f59,plain,(
% 51.39/6.99    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 51.39/6.99    inference(cnf_transformation,[],[f38])).
% 51.39/6.99  
% 51.39/6.99  fof(f5,axiom,(
% 51.39/6.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 51.39/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.39/6.99  
% 51.39/6.99  fof(f14,plain,(
% 51.39/6.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 51.39/6.99    inference(pure_predicate_removal,[],[f5])).
% 51.39/6.99  
% 51.39/6.99  fof(f20,plain,(
% 51.39/6.99    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 51.39/6.99    inference(ennf_transformation,[],[f14])).
% 51.39/6.99  
% 51.39/6.99  fof(f21,plain,(
% 51.39/6.99    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 51.39/6.99    inference(flattening,[],[f20])).
% 51.39/6.99  
% 51.39/6.99  fof(f51,plain,(
% 51.39/6.99    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.39/6.99    inference(cnf_transformation,[],[f21])).
% 51.39/6.99  
% 51.39/6.99  fof(f2,axiom,(
% 51.39/6.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 51.39/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.39/6.99  
% 51.39/6.99  fof(f15,plain,(
% 51.39/6.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 51.39/6.99    inference(ennf_transformation,[],[f2])).
% 51.39/6.99  
% 51.39/6.99  fof(f16,plain,(
% 51.39/6.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 51.39/6.99    inference(flattening,[],[f15])).
% 51.39/6.99  
% 51.39/6.99  fof(f47,plain,(
% 51.39/6.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 51.39/6.99    inference(cnf_transformation,[],[f16])).
% 51.39/6.99  
% 51.39/6.99  fof(f3,axiom,(
% 51.39/6.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 51.39/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.39/6.99  
% 51.39/6.99  fof(f17,plain,(
% 51.39/6.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 51.39/6.99    inference(ennf_transformation,[],[f3])).
% 51.39/6.99  
% 51.39/6.99  fof(f48,plain,(
% 51.39/6.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 51.39/6.99    inference(cnf_transformation,[],[f17])).
% 51.39/6.99  
% 51.39/6.99  fof(f1,axiom,(
% 51.39/6.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 51.39/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.39/6.99  
% 51.39/6.99  fof(f35,plain,(
% 51.39/6.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.39/6.99    inference(nnf_transformation,[],[f1])).
% 51.39/6.99  
% 51.39/6.99  fof(f36,plain,(
% 51.39/6.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.39/6.99    inference(flattening,[],[f35])).
% 51.39/6.99  
% 51.39/6.99  fof(f46,plain,(
% 51.39/6.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 51.39/6.99    inference(cnf_transformation,[],[f36])).
% 51.39/6.99  
% 51.39/6.99  fof(f8,axiom,(
% 51.39/6.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 51.39/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.39/6.99  
% 51.39/6.99  fof(f26,plain,(
% 51.39/6.99    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.39/6.99    inference(ennf_transformation,[],[f8])).
% 51.39/6.99  
% 51.39/6.99  fof(f27,plain,(
% 51.39/6.99    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.39/6.99    inference(flattening,[],[f26])).
% 51.39/6.99  
% 51.39/6.99  fof(f55,plain,(
% 51.39/6.99    ( ! [X0,X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.39/6.99    inference(cnf_transformation,[],[f27])).
% 51.39/6.99  
% 51.39/6.99  fof(f44,plain,(
% 51.39/6.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 51.39/6.99    inference(cnf_transformation,[],[f36])).
% 51.39/6.99  
% 51.39/6.99  fof(f73,plain,(
% 51.39/6.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 51.39/6.99    inference(equality_resolution,[],[f44])).
% 51.39/6.99  
% 51.39/6.99  fof(f58,plain,(
% 51.39/6.99    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 51.39/6.99    inference(cnf_transformation,[],[f38])).
% 51.39/6.99  
% 51.39/6.99  fof(f70,plain,(
% 51.39/6.99    m1_pre_topc(sK3,sK2)),
% 51.39/6.99    inference(cnf_transformation,[],[f43])).
% 51.39/6.99  
% 51.39/6.99  fof(f50,plain,(
% 51.39/6.99    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.39/6.99    inference(cnf_transformation,[],[f21])).
% 51.39/6.99  
% 51.39/6.99  fof(f69,plain,(
% 51.39/6.99    m1_pre_topc(sK1,sK2)),
% 51.39/6.99    inference(cnf_transformation,[],[f43])).
% 51.39/6.99  
% 51.39/6.99  fof(f7,axiom,(
% 51.39/6.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))),
% 51.39/6.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.39/6.99  
% 51.39/6.99  fof(f24,plain,(
% 51.39/6.99    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.39/6.99    inference(ennf_transformation,[],[f7])).
% 51.39/6.99  
% 51.39/6.99  fof(f25,plain,(
% 51.39/6.99    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.39/6.99    inference(flattening,[],[f24])).
% 51.39/6.99  
% 51.39/6.99  fof(f37,plain,(
% 51.39/6.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.39/6.99    inference(nnf_transformation,[],[f25])).
% 51.39/6.99  
% 51.39/6.99  fof(f53,plain,(
% 51.39/6.99    ( ! [X2,X0,X1] : (k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.39/6.99    inference(cnf_transformation,[],[f37])).
% 51.39/6.99  
% 51.39/6.99  fof(f71,plain,(
% 51.39/6.99    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 51.39/6.99    inference(cnf_transformation,[],[f43])).
% 51.39/6.99  
% 51.39/6.99  cnf(c_23,negated_conjecture,
% 51.39/6.99      ( m1_pre_topc(sK1,sK0) ),
% 51.39/6.99      inference(cnf_transformation,[],[f64]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_952,plain,
% 51.39/6.99      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_21,negated_conjecture,
% 51.39/6.99      ( m1_pre_topc(sK2,sK0) ),
% 51.39/6.99      inference(cnf_transformation,[],[f66]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_954,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_5,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.39/6.99      | ~ m1_pre_topc(X2,X1)
% 51.39/6.99      | v2_struct_0(X1)
% 51.39/6.99      | v2_struct_0(X0)
% 51.39/6.99      | v2_struct_0(X2)
% 51.39/6.99      | ~ l1_pre_topc(X1)
% 51.39/6.99      | k1_tsep_1(X1,X2,X0) = k1_tsep_1(X1,X0,X2) ),
% 51.39/6.99      inference(cnf_transformation,[],[f49]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_970,plain,
% 51.39/6.99      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
% 51.39/6.99      | m1_pre_topc(X2,X0) != iProver_top
% 51.39/6.99      | m1_pre_topc(X1,X0) != iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top
% 51.39/6.99      | v2_struct_0(X2) = iProver_top
% 51.39/6.99      | v2_struct_0(X1) = iProver_top
% 51.39/6.99      | l1_pre_topc(X0) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_2151,plain,
% 51.39/6.99      ( k1_tsep_1(sK0,sK2,X0) = k1_tsep_1(sK0,X0,sK2)
% 51.39/6.99      | m1_pre_topc(X0,sK0) != iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | v2_struct_0(sK0) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK0) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_954,c_970]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_27,negated_conjecture,
% 51.39/6.99      ( ~ v2_struct_0(sK0) ),
% 51.39/6.99      inference(cnf_transformation,[],[f60]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_28,plain,
% 51.39/6.99      ( v2_struct_0(sK0) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_25,negated_conjecture,
% 51.39/6.99      ( l1_pre_topc(sK0) ),
% 51.39/6.99      inference(cnf_transformation,[],[f62]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_30,plain,
% 51.39/6.99      ( l1_pre_topc(sK0) = iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_22,negated_conjecture,
% 51.39/6.99      ( ~ v2_struct_0(sK2) ),
% 51.39/6.99      inference(cnf_transformation,[],[f65]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_33,plain,
% 51.39/6.99      ( v2_struct_0(sK2) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_8684,plain,
% 51.39/6.99      ( v2_struct_0(X0) = iProver_top
% 51.39/6.99      | m1_pre_topc(X0,sK0) != iProver_top
% 51.39/6.99      | k1_tsep_1(sK0,sK2,X0) = k1_tsep_1(sK0,X0,sK2) ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_2151,c_28,c_30,c_33]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_8685,plain,
% 51.39/6.99      ( k1_tsep_1(sK0,sK2,X0) = k1_tsep_1(sK0,X0,sK2)
% 51.39/6.99      | m1_pre_topc(X0,sK0) != iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top ),
% 51.39/6.99      inference(renaming,[status(thm)],[c_8684]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_8692,plain,
% 51.39/6.99      ( k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2)
% 51.39/6.99      | v2_struct_0(sK1) = iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_952,c_8685]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_24,negated_conjecture,
% 51.39/6.99      ( ~ v2_struct_0(sK1) ),
% 51.39/6.99      inference(cnf_transformation,[],[f63]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_7716,plain,
% 51.39/6.99      ( ~ m1_pre_topc(sK2,X0)
% 51.39/6.99      | ~ m1_pre_topc(sK1,X0)
% 51.39/6.99      | v2_struct_0(X0)
% 51.39/6.99      | v2_struct_0(sK2)
% 51.39/6.99      | v2_struct_0(sK1)
% 51.39/6.99      | ~ l1_pre_topc(X0)
% 51.39/6.99      | k1_tsep_1(X0,sK2,sK1) = k1_tsep_1(X0,sK1,sK2) ),
% 51.39/6.99      inference(instantiation,[status(thm)],[c_5]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_7719,plain,
% 51.39/6.99      ( ~ m1_pre_topc(sK2,sK0)
% 51.39/6.99      | ~ m1_pre_topc(sK1,sK0)
% 51.39/6.99      | v2_struct_0(sK2)
% 51.39/6.99      | v2_struct_0(sK1)
% 51.39/6.99      | v2_struct_0(sK0)
% 51.39/6.99      | ~ l1_pre_topc(sK0)
% 51.39/6.99      | k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2) ),
% 51.39/6.99      inference(instantiation,[status(thm)],[c_7716]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_9196,plain,
% 51.39/6.99      ( k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2) ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_8692,c_27,c_25,c_24,c_23,c_22,c_21,c_7719]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_19,negated_conjecture,
% 51.39/6.99      ( m1_pre_topc(sK3,sK0) ),
% 51.39/6.99      inference(cnf_transformation,[],[f68]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_956,plain,
% 51.39/6.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_2150,plain,
% 51.39/6.99      ( k1_tsep_1(sK0,sK3,X0) = k1_tsep_1(sK0,X0,sK3)
% 51.39/6.99      | m1_pre_topc(X0,sK0) != iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top
% 51.39/6.99      | v2_struct_0(sK3) = iProver_top
% 51.39/6.99      | v2_struct_0(sK0) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK0) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_956,c_970]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_20,negated_conjecture,
% 51.39/6.99      ( ~ v2_struct_0(sK3) ),
% 51.39/6.99      inference(cnf_transformation,[],[f67]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_35,plain,
% 51.39/6.99      ( v2_struct_0(sK3) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_7821,plain,
% 51.39/6.99      ( v2_struct_0(X0) = iProver_top
% 51.39/6.99      | m1_pre_topc(X0,sK0) != iProver_top
% 51.39/6.99      | k1_tsep_1(sK0,sK3,X0) = k1_tsep_1(sK0,X0,sK3) ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_2150,c_28,c_30,c_35]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_7822,plain,
% 51.39/6.99      ( k1_tsep_1(sK0,sK3,X0) = k1_tsep_1(sK0,X0,sK3)
% 51.39/6.99      | m1_pre_topc(X0,sK0) != iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top ),
% 51.39/6.99      inference(renaming,[status(thm)],[c_7821]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_7831,plain,
% 51.39/6.99      ( k1_tsep_1(sK0,sK3,sK1) = k1_tsep_1(sK0,sK1,sK3)
% 51.39/6.99      | v2_struct_0(sK1) = iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_952,c_7822]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_1699,plain,
% 51.39/6.99      ( ~ m1_pre_topc(sK3,sK0)
% 51.39/6.99      | ~ m1_pre_topc(sK1,sK0)
% 51.39/6.99      | v2_struct_0(sK3)
% 51.39/6.99      | v2_struct_0(sK1)
% 51.39/6.99      | v2_struct_0(sK0)
% 51.39/6.99      | ~ l1_pre_topc(sK0)
% 51.39/6.99      | k1_tsep_1(sK0,sK3,sK1) = k1_tsep_1(sK0,sK1,sK3) ),
% 51.39/6.99      inference(instantiation,[status(thm)],[c_5]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_8168,plain,
% 51.39/6.99      ( k1_tsep_1(sK0,sK3,sK1) = k1_tsep_1(sK0,sK1,sK3) ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_7831,c_27,c_25,c_24,c_23,c_20,c_19,c_1699]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_12,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.39/6.99      | ~ m1_pre_topc(X2,X1)
% 51.39/6.99      | ~ m1_pre_topc(X0,X2)
% 51.39/6.99      | ~ m1_pre_topc(X3,X4)
% 51.39/6.99      | ~ m1_pre_topc(X4,X1)
% 51.39/6.99      | ~ m1_pre_topc(X3,X1)
% 51.39/6.99      | m1_pre_topc(k1_tsep_1(X1,X0,X3),k1_tsep_1(X1,X2,X4))
% 51.39/6.99      | v2_struct_0(X1)
% 51.39/6.99      | v2_struct_0(X0)
% 51.39/6.99      | v2_struct_0(X2)
% 51.39/6.99      | v2_struct_0(X3)
% 51.39/6.99      | v2_struct_0(X4)
% 51.39/6.99      | ~ l1_pre_topc(X1)
% 51.39/6.99      | ~ v2_pre_topc(X1) ),
% 51.39/6.99      inference(cnf_transformation,[],[f56]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_963,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X2,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X0,X2) != iProver_top
% 51.39/6.99      | m1_pre_topc(X3,X4) != iProver_top
% 51.39/6.99      | m1_pre_topc(X4,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X3,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(k1_tsep_1(X1,X0,X3),k1_tsep_1(X1,X2,X4)) = iProver_top
% 51.39/6.99      | v2_struct_0(X1) = iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top
% 51.39/6.99      | v2_struct_0(X2) = iProver_top
% 51.39/6.99      | v2_struct_0(X3) = iProver_top
% 51.39/6.99      | v2_struct_0(X4) = iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top
% 51.39/6.99      | v2_pre_topc(X1) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_8173,plain,
% 51.39/6.99      ( m1_pre_topc(X0,sK0) != iProver_top
% 51.39/6.99      | m1_pre_topc(X1,sK0) != iProver_top
% 51.39/6.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,X0,X1)) = iProver_top
% 51.39/6.99      | m1_pre_topc(sK3,X0) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK1,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 51.39/6.99      | v2_struct_0(X1) = iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top
% 51.39/6.99      | v2_struct_0(sK3) = iProver_top
% 51.39/6.99      | v2_struct_0(sK1) = iProver_top
% 51.39/6.99      | v2_struct_0(sK0) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK0) != iProver_top
% 51.39/6.99      | v2_pre_topc(sK0) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_8168,c_963]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_26,negated_conjecture,
% 51.39/6.99      ( v2_pre_topc(sK0) ),
% 51.39/6.99      inference(cnf_transformation,[],[f61]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_29,plain,
% 51.39/6.99      ( v2_pre_topc(sK0) = iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_31,plain,
% 51.39/6.99      ( v2_struct_0(sK1) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_32,plain,
% 51.39/6.99      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_36,plain,
% 51.39/6.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_149650,plain,
% 51.39/6.99      ( v2_struct_0(X0) = iProver_top
% 51.39/6.99      | v2_struct_0(X1) = iProver_top
% 51.39/6.99      | m1_pre_topc(sK3,X0) != iProver_top
% 51.39/6.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,X0,X1)) = iProver_top
% 51.39/6.99      | m1_pre_topc(X1,sK0) != iProver_top
% 51.39/6.99      | m1_pre_topc(X0,sK0) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK1,X1) != iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_8173,c_28,c_29,c_30,c_31,c_32,c_35,c_36]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_149651,plain,
% 51.39/6.99      ( m1_pre_topc(X0,sK0) != iProver_top
% 51.39/6.99      | m1_pre_topc(X1,sK0) != iProver_top
% 51.39/6.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,X0,X1)) = iProver_top
% 51.39/6.99      | m1_pre_topc(sK3,X0) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK1,X1) != iProver_top
% 51.39/6.99      | v2_struct_0(X1) = iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top ),
% 51.39/6.99      inference(renaming,[status(thm)],[c_149650]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_149665,plain,
% 51.39/6.99      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK3,sK2) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK1,sK1) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | v2_struct_0(sK1) = iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_9196,c_149651]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_13,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 51.39/6.99      inference(cnf_transformation,[],[f57]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_962,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X0) = iProver_top
% 51.39/6.99      | l1_pre_topc(X0) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_8,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.39/6.99      | ~ m1_pre_topc(X2,X1)
% 51.39/6.99      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
% 51.39/6.99      | v2_struct_0(X1)
% 51.39/6.99      | v2_struct_0(X0)
% 51.39/6.99      | v2_struct_0(X2)
% 51.39/6.99      | ~ l1_pre_topc(X1)
% 51.39/6.99      | ~ v2_pre_topc(X1) ),
% 51.39/6.99      inference(cnf_transformation,[],[f52]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_967,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X2,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2)) = iProver_top
% 51.39/6.99      | v2_struct_0(X1) = iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top
% 51.39/6.99      | v2_struct_0(X2) = iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top
% 51.39/6.99      | v2_pre_topc(X1) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_9198,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | v2_struct_0(sK1) = iProver_top
% 51.39/6.99      | v2_struct_0(sK0) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK0) != iProver_top
% 51.39/6.99      | v2_pre_topc(sK0) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_9196,c_967]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_34,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_78366,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_9198,c_28,c_29,c_30,c_31,c_32,c_33,c_34]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_14,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.39/6.99      | ~ m1_pre_topc(X2,X1)
% 51.39/6.99      | ~ m1_pre_topc(X0,X2)
% 51.39/6.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 51.39/6.99      | ~ l1_pre_topc(X1)
% 51.39/6.99      | ~ v2_pre_topc(X1) ),
% 51.39/6.99      inference(cnf_transformation,[],[f59]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_961,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X2,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X0,X2) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top
% 51.39/6.99      | v2_pre_topc(X1) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_78374,plain,
% 51.39/6.99      ( m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,X0) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 51.39/6.99      | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 51.39/6.99      | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_78366,c_961]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_6,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.39/6.99      | ~ m1_pre_topc(X2,X1)
% 51.39/6.99      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 51.39/6.99      | v2_struct_0(X1)
% 51.39/6.99      | v2_struct_0(X0)
% 51.39/6.99      | v2_struct_0(X2)
% 51.39/6.99      | ~ l1_pre_topc(X1) ),
% 51.39/6.99      inference(cnf_transformation,[],[f51]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_969,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X2,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1) = iProver_top
% 51.39/6.99      | v2_struct_0(X1) = iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top
% 51.39/6.99      | v2_struct_0(X2) = iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_3,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.39/6.99      | ~ l1_pre_topc(X1)
% 51.39/6.99      | ~ v2_pre_topc(X1)
% 51.39/6.99      | v2_pre_topc(X0) ),
% 51.39/6.99      inference(cnf_transformation,[],[f47]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_972,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top
% 51.39/6.99      | v2_pre_topc(X1) != iProver_top
% 51.39/6.99      | v2_pre_topc(X0) = iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_2130,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X2,X1) != iProver_top
% 51.39/6.99      | v2_struct_0(X1) = iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top
% 51.39/6.99      | v2_struct_0(X2) = iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top
% 51.39/6.99      | v2_pre_topc(X1) != iProver_top
% 51.39/6.99      | v2_pre_topc(k1_tsep_1(X1,X0,X2)) = iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_969,c_972]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_11467,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,sK0) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | v2_struct_0(sK1) = iProver_top
% 51.39/6.99      | v2_struct_0(sK0) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK0) != iProver_top
% 51.39/6.99      | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 51.39/6.99      | v2_pre_topc(sK0) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_9196,c_2130]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_4,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 51.39/6.99      inference(cnf_transformation,[],[f48]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_971,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top
% 51.39/6.99      | l1_pre_topc(X0) = iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_2131,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X2,X1) != iProver_top
% 51.39/6.99      | v2_struct_0(X1) = iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top
% 51.39/6.99      | v2_struct_0(X2) = iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top
% 51.39/6.99      | l1_pre_topc(k1_tsep_1(X1,X0,X2)) = iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_969,c_971]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_11748,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,sK0) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | v2_struct_0(sK1) = iProver_top
% 51.39/6.99      | v2_struct_0(sK0) = iProver_top
% 51.39/6.99      | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK0) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_9196,c_2131]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_78724,plain,
% 51.39/6.99      ( m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,X0) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_78374,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_11467,
% 51.39/6.99                 c_11748]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_78731,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) = iProver_top
% 51.39/6.99      | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_962,c_78724]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_78749,plain,
% 51.39/6.99      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_78731,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_9198,
% 51.39/6.99                 c_11748]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_0,plain,
% 51.39/6.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 51.39/6.99      inference(cnf_transformation,[],[f46]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_974,plain,
% 51.39/6.99      ( X0 = X1
% 51.39/6.99      | r1_tarski(X0,X1) != iProver_top
% 51.39/6.99      | r1_tarski(X1,X0) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_78753,plain,
% 51.39/6.99      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = u1_struct_0(sK2)
% 51.39/6.99      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2)) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_78749,c_974]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_44,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X0) = iProver_top
% 51.39/6.99      | l1_pre_topc(X0) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_46,plain,
% 51.39/6.99      ( m1_pre_topc(sK0,sK0) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK0) != iProver_top ),
% 51.39/6.99      inference(instantiation,[status(thm)],[c_44]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_1298,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.39/6.99      | ~ m1_pre_topc(sK2,X1)
% 51.39/6.99      | ~ m1_pre_topc(sK2,X0)
% 51.39/6.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 51.39/6.99      | ~ l1_pre_topc(X1)
% 51.39/6.99      | ~ v2_pre_topc(X1) ),
% 51.39/6.99      inference(instantiation,[status(thm)],[c_14]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_1303,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,X0) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,X1) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top
% 51.39/6.99      | v2_pre_topc(X1) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_1298]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_1305,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,sK0) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0)) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK0) != iProver_top
% 51.39/6.99      | v2_pre_topc(sK0) != iProver_top ),
% 51.39/6.99      inference(instantiation,[status(thm)],[c_1303]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_11,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.39/6.99      | v2_struct_0(X1)
% 51.39/6.99      | v2_struct_0(X0)
% 51.39/6.99      | ~ l1_pre_topc(X1)
% 51.39/6.99      | ~ v2_pre_topc(X1)
% 51.39/6.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 51.39/6.99      inference(cnf_transformation,[],[f55]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_964,plain,
% 51.39/6.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
% 51.39/6.99      | m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | v2_struct_0(X1) = iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top
% 51.39/6.99      | v2_pre_topc(X1) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_1844,plain,
% 51.39/6.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | v2_struct_0(sK0) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK0) != iProver_top
% 51.39/6.99      | v2_pre_topc(sK0) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_954,c_964]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_4048,plain,
% 51.39/6.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_1844,c_28,c_29,c_30,c_33]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_2,plain,
% 51.39/6.99      ( r1_tarski(X0,X0) ),
% 51.39/6.99      inference(cnf_transformation,[],[f73]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_973,plain,
% 51.39/6.99      ( r1_tarski(X0,X0) = iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_15,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.39/6.99      | ~ m1_pre_topc(X2,X1)
% 51.39/6.99      | m1_pre_topc(X0,X2)
% 51.39/6.99      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 51.39/6.99      | ~ l1_pre_topc(X1)
% 51.39/6.99      | ~ v2_pre_topc(X1) ),
% 51.39/6.99      inference(cnf_transformation,[],[f58]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_960,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X2,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X0,X2) = iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top
% 51.39/6.99      | v2_pre_topc(X1) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_1607,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X0,X0) = iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top
% 51.39/6.99      | v2_pre_topc(X1) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_973,c_960]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_67,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top
% 51.39/6.99      | l1_pre_topc(X0) = iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_2845,plain,
% 51.39/6.99      ( l1_pre_topc(X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X0,X0) = iProver_top
% 51.39/6.99      | m1_pre_topc(X0,X1) != iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_1607,c_44,c_67]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_2846,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X0,X0) = iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top ),
% 51.39/6.99      inference(renaming,[status(thm)],[c_2845]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_2856,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,sK2) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK0) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_954,c_2846]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_1155,plain,
% 51.39/6.99      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK0) ),
% 51.39/6.99      inference(resolution,[status(thm)],[c_4,c_21]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_1156,plain,
% 51.39/6.99      ( l1_pre_topc(sK2) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK0) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_1155]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_1945,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 51.39/6.99      inference(instantiation,[status(thm)],[c_13]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_1950,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,sK2) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK2) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_1945]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_3127,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,sK2) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_2856,c_30,c_1156,c_1950]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_3134,plain,
% 51.39/6.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,sK2,sK2)
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK2) != iProver_top
% 51.39/6.99      | v2_pre_topc(sK2) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_3127,c_964]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_1639,plain,
% 51.39/6.99      ( ~ l1_pre_topc(sK0) | v2_pre_topc(sK2) | ~ v2_pre_topc(sK0) ),
% 51.39/6.99      inference(resolution,[status(thm)],[c_3,c_21]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_1640,plain,
% 51.39/6.99      ( l1_pre_topc(sK0) != iProver_top
% 51.39/6.99      | v2_pre_topc(sK2) = iProver_top
% 51.39/6.99      | v2_pre_topc(sK0) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_1639]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_3869,plain,
% 51.39/6.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK2,sK2,sK2) ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_3134,c_29,c_30,c_33,c_1156,c_1640]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_4052,plain,
% 51.39/6.99      ( k1_tsep_1(sK2,sK2,sK2) = k1_tsep_1(sK0,sK2,sK2) ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_4048,c_3869]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_30672,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK2)) = iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK2) != iProver_top
% 51.39/6.99      | v2_pre_topc(sK2) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_4052,c_967]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_31928,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK2)) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_30672,c_29,c_30,c_33,c_1156,c_1640,c_1950]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_31936,plain,
% 51.39/6.99      ( m1_pre_topc(X0,k1_tsep_1(sK0,sK2,sK2)) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,X0) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 51.39/6.99      | l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) != iProver_top
% 51.39/6.99      | v2_pre_topc(k1_tsep_1(sK0,sK2,sK2)) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_31928,c_961]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_2262,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X2,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X0,X3) != iProver_top
% 51.39/6.99      | m1_pre_topc(X3,k1_tsep_1(X1,X0,X2)) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X3)) = iProver_top
% 51.39/6.99      | v2_struct_0(X1) = iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top
% 51.39/6.99      | v2_struct_0(X2) = iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top
% 51.39/6.99      | l1_pre_topc(k1_tsep_1(X1,X0,X2)) != iProver_top
% 51.39/6.99      | v2_pre_topc(X1) != iProver_top
% 51.39/6.99      | v2_pre_topc(k1_tsep_1(X1,X0,X2)) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_967,c_961]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_12980,plain,
% 51.39/6.99      ( v2_pre_topc(X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X2,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X0,X3) != iProver_top
% 51.39/6.99      | m1_pre_topc(X3,k1_tsep_1(X1,X0,X2)) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X3)) = iProver_top
% 51.39/6.99      | v2_struct_0(X1) = iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top
% 51.39/6.99      | v2_struct_0(X2) = iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_2262,c_2130,c_2131]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_12981,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X2,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X0,X3) != iProver_top
% 51.39/6.99      | m1_pre_topc(X3,k1_tsep_1(X1,X0,X2)) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X3)) = iProver_top
% 51.39/6.99      | v2_struct_0(X1) = iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top
% 51.39/6.99      | v2_struct_0(X2) = iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top
% 51.39/6.99      | v2_pre_topc(X1) != iProver_top ),
% 51.39/6.99      inference(renaming,[status(thm)],[c_12980]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_30668,plain,
% 51.39/6.99      ( m1_pre_topc(X0,k1_tsep_1(sK0,sK2,sK2)) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,X0) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK2) != iProver_top
% 51.39/6.99      | v2_pre_topc(sK2) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_4052,c_12981]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_32807,plain,
% 51.39/6.99      ( m1_pre_topc(X0,k1_tsep_1(sK0,sK2,sK2)) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,X0) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_31936,c_29,c_30,c_33,c_1156,c_1640,c_1950,c_30668]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_32814,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK2)) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(k1_tsep_1(sK0,sK2,sK2))) = iProver_top
% 51.39/6.99      | l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_962,c_32807]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_17,negated_conjecture,
% 51.39/6.99      ( m1_pre_topc(sK3,sK2) ),
% 51.39/6.99      inference(cnf_transformation,[],[f70]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_958,plain,
% 51.39/6.99      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_2147,plain,
% 51.39/6.99      ( k1_tsep_1(X0,X0,X1) = k1_tsep_1(X0,X1,X0)
% 51.39/6.99      | m1_pre_topc(X1,X0) != iProver_top
% 51.39/6.99      | v2_struct_0(X1) = iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top
% 51.39/6.99      | l1_pre_topc(X0) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_962,c_970]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_4203,plain,
% 51.39/6.99      ( k1_tsep_1(sK2,sK3,sK2) = k1_tsep_1(sK2,sK2,sK3)
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | v2_struct_0(sK3) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK2) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_958,c_2147]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_4432,plain,
% 51.39/6.99      ( k1_tsep_1(sK2,sK3,sK2) = k1_tsep_1(sK2,sK2,sK3) ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_4203,c_30,c_33,c_35,c_1156]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_4434,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,k1_tsep_1(sK2,sK3,sK2)) = iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK3,sK2) != iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | v2_struct_0(sK3) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK2) != iProver_top
% 51.39/6.99      | v2_pre_topc(sK2) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_4432,c_967]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_38,plain,
% 51.39/6.99      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_16535,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,k1_tsep_1(sK2,sK3,sK2)) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_4434,c_29,c_30,c_33,c_35,c_38,c_1156,c_1640,c_1950]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_16544,plain,
% 51.39/6.99      ( k1_tsep_1(k1_tsep_1(sK2,sK3,sK2),sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 51.39/6.99      | v2_struct_0(k1_tsep_1(sK2,sK3,sK2)) = iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | l1_pre_topc(k1_tsep_1(sK2,sK3,sK2)) != iProver_top
% 51.39/6.99      | v2_pre_topc(k1_tsep_1(sK2,sK3,sK2)) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_16535,c_964]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_7,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.39/6.99      | ~ m1_pre_topc(X2,X1)
% 51.39/6.99      | v2_struct_0(X1)
% 51.39/6.99      | v2_struct_0(X0)
% 51.39/6.99      | v2_struct_0(X2)
% 51.39/6.99      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 51.39/6.99      | ~ l1_pre_topc(X1) ),
% 51.39/6.99      inference(cnf_transformation,[],[f50]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_968,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X2,X1) != iProver_top
% 51.39/6.99      | v2_struct_0(X1) = iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top
% 51.39/6.99      | v2_struct_0(X2) = iProver_top
% 51.39/6.99      | v2_struct_0(k1_tsep_1(X1,X0,X2)) != iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_4436,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,sK2) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK3,sK2) != iProver_top
% 51.39/6.99      | v2_struct_0(k1_tsep_1(sK2,sK3,sK2)) != iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | v2_struct_0(sK3) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK2) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_4432,c_968]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_4435,plain,
% 51.39/6.99      ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK2),sK2) = iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK3,sK2) != iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | v2_struct_0(sK3) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK2) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_4432,c_969]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_1334,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,sK2)
% 51.39/6.99      | ~ m1_pre_topc(X1,sK2)
% 51.39/6.99      | m1_pre_topc(k1_tsep_1(sK2,X0,X1),sK2)
% 51.39/6.99      | v2_struct_0(X0)
% 51.39/6.99      | v2_struct_0(X1)
% 51.39/6.99      | v2_struct_0(sK2)
% 51.39/6.99      | ~ l1_pre_topc(sK2) ),
% 51.39/6.99      inference(instantiation,[status(thm)],[c_6]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_1944,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,sK2)
% 51.39/6.99      | m1_pre_topc(k1_tsep_1(sK2,X0,sK2),sK2)
% 51.39/6.99      | ~ m1_pre_topc(sK2,sK2)
% 51.39/6.99      | v2_struct_0(X0)
% 51.39/6.99      | v2_struct_0(sK2)
% 51.39/6.99      | ~ l1_pre_topc(sK2) ),
% 51.39/6.99      inference(instantiation,[status(thm)],[c_1334]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_3994,plain,
% 51.39/6.99      ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK2),sK2)
% 51.39/6.99      | ~ m1_pre_topc(sK2,sK2)
% 51.39/6.99      | ~ m1_pre_topc(sK3,sK2)
% 51.39/6.99      | v2_struct_0(sK2)
% 51.39/6.99      | v2_struct_0(sK3)
% 51.39/6.99      | ~ l1_pre_topc(sK2) ),
% 51.39/6.99      inference(instantiation,[status(thm)],[c_1944]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_3995,plain,
% 51.39/6.99      ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK2),sK2) = iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK3,sK2) != iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | v2_struct_0(sK3) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK2) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_3994]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_9415,plain,
% 51.39/6.99      ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK2),sK2) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_4435,c_30,c_33,c_35,c_38,c_1156,c_1950,c_3995]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_9424,plain,
% 51.39/6.99      ( l1_pre_topc(sK2) != iProver_top
% 51.39/6.99      | v2_pre_topc(k1_tsep_1(sK2,sK3,sK2)) = iProver_top
% 51.39/6.99      | v2_pre_topc(sK2) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_9415,c_972]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_9425,plain,
% 51.39/6.99      ( l1_pre_topc(k1_tsep_1(sK2,sK3,sK2)) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK2) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_9415,c_971]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_20512,plain,
% 51.39/6.99      ( k1_tsep_1(k1_tsep_1(sK2,sK3,sK2),sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_16544,c_29,c_30,c_33,c_35,c_38,c_1156,c_1640,c_1950,
% 51.39/6.99                 c_4436,c_9424,c_9425]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_20529,plain,
% 51.39/6.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),k1_tsep_1(sK2,sK3,sK2)) = iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,k1_tsep_1(sK2,sK3,sK2)) != iProver_top
% 51.39/6.99      | v2_struct_0(k1_tsep_1(sK2,sK3,sK2)) = iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | l1_pre_topc(k1_tsep_1(sK2,sK3,sK2)) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_20512,c_969]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_21729,plain,
% 51.39/6.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),k1_tsep_1(sK2,sK3,sK2)) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_20529,c_29,c_30,c_33,c_35,c_38,c_1156,c_1640,c_1950,
% 51.39/6.99                 c_4434,c_4436,c_9425]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_21746,plain,
% 51.39/6.99      ( l1_pre_topc(k1_tsep_1(sK2,sK3,sK2)) != iProver_top
% 51.39/6.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_21729,c_971]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_458,plain,
% 51.39/6.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 51.39/6.99      theory(equality) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_2981,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.39/6.99      | v2_struct_0(X0)
% 51.39/6.99      | v2_struct_0(X1)
% 51.39/6.99      | ~ l1_pre_topc(X1)
% 51.39/6.99      | ~ l1_pre_topc(k1_tsep_1(X1,X0,X0))
% 51.39/6.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 51.39/6.99      | ~ v2_pre_topc(X1) ),
% 51.39/6.99      inference(resolution,[status(thm)],[c_11,c_458]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_2695,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.39/6.99      | ~ m1_pre_topc(X2,X1)
% 51.39/6.99      | v2_struct_0(X0)
% 51.39/6.99      | v2_struct_0(X1)
% 51.39/6.99      | v2_struct_0(X2)
% 51.39/6.99      | ~ l1_pre_topc(X1)
% 51.39/6.99      | l1_pre_topc(k1_tsep_1(X1,X0,X2)) ),
% 51.39/6.99      inference(resolution,[status(thm)],[c_6,c_4]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_7871,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.39/6.99      | v2_struct_0(X0)
% 51.39/6.99      | v2_struct_0(X1)
% 51.39/6.99      | ~ l1_pre_topc(X1)
% 51.39/6.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 51.39/6.99      | ~ v2_pre_topc(X1) ),
% 51.39/6.99      inference(resolution,[status(thm)],[c_2981,c_2695]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_15707,plain,
% 51.39/6.99      ( v2_struct_0(sK2)
% 51.39/6.99      | v2_struct_0(sK0)
% 51.39/6.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 51.39/6.99      | ~ l1_pre_topc(sK0)
% 51.39/6.99      | ~ v2_pre_topc(sK0) ),
% 51.39/6.99      inference(resolution,[status(thm)],[c_7871,c_21]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_15708,plain,
% 51.39/6.99      ( v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | v2_struct_0(sK0) = iProver_top
% 51.39/6.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK0) != iProver_top
% 51.39/6.99      | v2_pre_topc(sK0) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_15707]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_21800,plain,
% 51.39/6.99      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_21746,c_28,c_29,c_30,c_33,c_15708]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_21808,plain,
% 51.39/6.99      ( l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) = iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_4048,c_21800]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_33019,plain,
% 51.39/6.99      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(k1_tsep_1(sK0,sK2,sK2))) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_32814,c_29,c_30,c_33,c_1156,c_1640,c_1950,c_21808,
% 51.39/6.99                 c_30672]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_33023,plain,
% 51.39/6.99      ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = u1_struct_0(sK2)
% 51.39/6.99      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK2,sK2)),u1_struct_0(sK2)) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_33019,c_974]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_30673,plain,
% 51.39/6.99      ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK2) = iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,sK2) != iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK2) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_4052,c_969]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_31877,plain,
% 51.39/6.99      ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK2) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_30673,c_30,c_33,c_1156,c_1950]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_31885,plain,
% 51.39/6.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 51.39/6.99      | m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),X0) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK2,sK2)),u1_struct_0(X0)) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK2) != iProver_top
% 51.39/6.99      | v2_pre_topc(sK2) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_31877,c_961]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_32498,plain,
% 51.39/6.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 51.39/6.99      | m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),X0) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK2,sK2)),u1_struct_0(X0)) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_31885,c_29,c_30,c_1156,c_1640]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_3133,plain,
% 51.39/6.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,X0) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK2) != iProver_top
% 51.39/6.99      | v2_pre_topc(sK2) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_3127,c_961]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_6792,plain,
% 51.39/6.99      ( m1_pre_topc(X0,sK2) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,X0) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_3133,c_29,c_30,c_1156,c_1640]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_6798,plain,
% 51.39/6.99      ( u1_struct_0(X0) = u1_struct_0(sK2)
% 51.39/6.99      | m1_pre_topc(X0,sK2) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,X0) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_6792,c_974]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_32508,plain,
% 51.39/6.99      ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = u1_struct_0(sK2)
% 51.39/6.99      | m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK2) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK2)) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,sK2) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_32498,c_6798]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_33031,plain,
% 51.39/6.99      ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = u1_struct_0(sK2) ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_33023,c_29,c_30,c_33,c_1156,c_1640,c_1950,c_30672,
% 51.39/6.99                 c_30673,c_32508]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_9199,plain,
% 51.39/6.99      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) = iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.39/6.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | v2_struct_0(sK1) = iProver_top
% 51.39/6.99      | v2_struct_0(sK0) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK0) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_9196,c_969]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_16055,plain,
% 51.39/6.99      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_9199,c_28,c_30,c_31,c_32,c_33,c_34]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_16063,plain,
% 51.39/6.99      ( m1_pre_topc(X0,sK0) != iProver_top
% 51.39/6.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK0) != iProver_top
% 51.39/6.99      | v2_pre_topc(sK0) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_16055,c_961]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_16318,plain,
% 51.39/6.99      ( m1_pre_topc(X0,sK0) != iProver_top
% 51.39/6.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(X0)) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_16063,c_29,c_30]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_33045,plain,
% 51.39/6.99      ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0) != iProver_top
% 51.39/6.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK2)) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),u1_struct_0(sK2)) = iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_33031,c_16318]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_18,negated_conjecture,
% 51.39/6.99      ( m1_pre_topc(sK1,sK2) ),
% 51.39/6.99      inference(cnf_transformation,[],[f69]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_957,plain,
% 51.39/6.99      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_10,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.39/6.99      | ~ m1_pre_topc(X2,X1)
% 51.39/6.99      | ~ m1_pre_topc(X0,X2)
% 51.39/6.99      | v2_struct_0(X1)
% 51.39/6.99      | v2_struct_0(X0)
% 51.39/6.99      | v2_struct_0(X2)
% 51.39/6.99      | ~ l1_pre_topc(X1)
% 51.39/6.99      | ~ v2_pre_topc(X1)
% 51.39/6.99      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X1,X0,X2) ),
% 51.39/6.99      inference(cnf_transformation,[],[f53]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_965,plain,
% 51.39/6.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X2,X0)
% 51.39/6.99      | m1_pre_topc(X2,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(X2,X0) != iProver_top
% 51.39/6.99      | v2_struct_0(X1) = iProver_top
% 51.39/6.99      | v2_struct_0(X2) = iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top
% 51.39/6.99      | v2_pre_topc(X1) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_2285,plain,
% 51.39/6.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,X0,sK2)
% 51.39/6.99      | m1_pre_topc(X0,sK2) != iProver_top
% 51.39/6.99      | m1_pre_topc(X0,sK0) != iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | v2_struct_0(sK0) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK0) != iProver_top
% 51.39/6.99      | v2_pre_topc(sK0) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_954,c_965]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_17055,plain,
% 51.39/6.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,X0,sK2)
% 51.39/6.99      | m1_pre_topc(X0,sK2) != iProver_top
% 51.39/6.99      | m1_pre_topc(X0,sK0) != iProver_top
% 51.39/6.99      | v2_struct_0(X0) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_2285,c_28,c_29,c_30,c_33]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_17064,plain,
% 51.39/6.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2)
% 51.39/6.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 51.39/6.99      | v2_struct_0(sK1) = iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_957,c_17055]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_2783,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.39/6.99      | ~ m1_pre_topc(X0,sK2)
% 51.39/6.99      | ~ m1_pre_topc(sK2,X1)
% 51.39/6.99      | v2_struct_0(X0)
% 51.39/6.99      | v2_struct_0(X1)
% 51.39/6.99      | v2_struct_0(sK2)
% 51.39/6.99      | ~ l1_pre_topc(X1)
% 51.39/6.99      | ~ v2_pre_topc(X1)
% 51.39/6.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(X1,X0,sK2) ),
% 51.39/6.99      inference(instantiation,[status(thm)],[c_10]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_5145,plain,
% 51.39/6.99      ( ~ m1_pre_topc(sK2,X0)
% 51.39/6.99      | ~ m1_pre_topc(sK1,X0)
% 51.39/6.99      | ~ m1_pre_topc(sK1,sK2)
% 51.39/6.99      | v2_struct_0(X0)
% 51.39/6.99      | v2_struct_0(sK2)
% 51.39/6.99      | v2_struct_0(sK1)
% 51.39/6.99      | ~ l1_pre_topc(X0)
% 51.39/6.99      | ~ v2_pre_topc(X0)
% 51.39/6.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(X0,sK1,sK2) ),
% 51.39/6.99      inference(instantiation,[status(thm)],[c_2783]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_5147,plain,
% 51.39/6.99      ( ~ m1_pre_topc(sK2,sK0)
% 51.39/6.99      | ~ m1_pre_topc(sK1,sK2)
% 51.39/6.99      | ~ m1_pre_topc(sK1,sK0)
% 51.39/6.99      | v2_struct_0(sK2)
% 51.39/6.99      | v2_struct_0(sK1)
% 51.39/6.99      | v2_struct_0(sK0)
% 51.39/6.99      | ~ l1_pre_topc(sK0)
% 51.39/6.99      | ~ v2_pre_topc(sK0)
% 51.39/6.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2) ),
% 51.39/6.99      inference(instantiation,[status(thm)],[c_5145]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_17227,plain,
% 51.39/6.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2) ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_17064,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_18,c_5147]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_31937,plain,
% 51.39/6.99      ( k1_tsep_1(k1_tsep_1(sK0,sK2,sK2),sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 51.39/6.99      | v2_struct_0(k1_tsep_1(sK0,sK2,sK2)) = iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) != iProver_top
% 51.39/6.99      | v2_pre_topc(k1_tsep_1(sK0,sK2,sK2)) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_31928,c_964]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_20530,plain,
% 51.39/6.99      ( m1_pre_topc(sK2,k1_tsep_1(sK2,sK3,sK2)) != iProver_top
% 51.39/6.99      | v2_struct_0(k1_tsep_1(sK2,sK3,sK2)) = iProver_top
% 51.39/6.99      | v2_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | l1_pre_topc(k1_tsep_1(sK2,sK3,sK2)) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_20512,c_968]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_20831,plain,
% 51.39/6.99      ( v2_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_20530,c_29,c_30,c_33,c_35,c_38,c_1156,c_1640,c_1950,
% 51.39/6.99                 c_4434,c_4436,c_9425]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_20839,plain,
% 51.39/6.99      ( v2_struct_0(k1_tsep_1(sK0,sK2,sK2)) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_4048,c_20831]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_21745,plain,
% 51.39/6.99      ( l1_pre_topc(k1_tsep_1(sK2,sK3,sK2)) != iProver_top
% 51.39/6.99      | v2_pre_topc(k1_tsep_1(sK2,sK3,sK2)) != iProver_top
% 51.39/6.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_21729,c_972]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_456,plain,
% 51.39/6.99      ( ~ v2_pre_topc(X0) | v2_pre_topc(X1) | X1 != X0 ),
% 51.39/6.99      theory(equality) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_2980,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.39/6.99      | v2_struct_0(X0)
% 51.39/6.99      | v2_struct_0(X1)
% 51.39/6.99      | ~ l1_pre_topc(X1)
% 51.39/6.99      | ~ v2_pre_topc(X1)
% 51.39/6.99      | ~ v2_pre_topc(k1_tsep_1(X1,X0,X0))
% 51.39/6.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 51.39/6.99      inference(resolution,[status(thm)],[c_11,c_456]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_2696,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.39/6.99      | ~ m1_pre_topc(X2,X1)
% 51.39/6.99      | v2_struct_0(X0)
% 51.39/6.99      | v2_struct_0(X1)
% 51.39/6.99      | v2_struct_0(X2)
% 51.39/6.99      | ~ l1_pre_topc(X1)
% 51.39/6.99      | ~ v2_pre_topc(X1)
% 51.39/6.99      | v2_pre_topc(k1_tsep_1(X1,X0,X2)) ),
% 51.39/6.99      inference(resolution,[status(thm)],[c_6,c_3]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_7853,plain,
% 51.39/6.99      ( ~ m1_pre_topc(X0,X1)
% 51.39/6.99      | v2_struct_0(X0)
% 51.39/6.99      | v2_struct_0(X1)
% 51.39/6.99      | ~ l1_pre_topc(X1)
% 51.39/6.99      | ~ v2_pre_topc(X1)
% 51.39/6.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 51.39/6.99      inference(resolution,[status(thm)],[c_2980,c_2696]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_15527,plain,
% 51.39/6.99      ( v2_struct_0(sK2)
% 51.39/6.99      | v2_struct_0(sK0)
% 51.39/6.99      | ~ l1_pre_topc(sK0)
% 51.39/6.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 51.39/6.99      | ~ v2_pre_topc(sK0) ),
% 51.39/6.99      inference(resolution,[status(thm)],[c_7853,c_21]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_15528,plain,
% 51.39/6.99      ( v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | v2_struct_0(sK0) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK0) != iProver_top
% 51.39/6.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 51.39/6.99      | v2_pre_topc(sK0) != iProver_top ),
% 51.39/6.99      inference(predicate_to_equality,[status(thm)],[c_15527]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_21943,plain,
% 51.39/6.99      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_21745,c_28,c_29,c_30,c_33,c_15528]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_21951,plain,
% 51.39/6.99      ( v2_pre_topc(k1_tsep_1(sK0,sK2,sK2)) = iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_4048,c_21943]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_33491,plain,
% 51.39/6.99      ( k1_tsep_1(k1_tsep_1(sK0,sK2,sK2),sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_31937,c_33,c_20839,c_21808,c_21951]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_33508,plain,
% 51.39/6.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),k1_tsep_1(sK0,sK2,sK2)) = iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,k1_tsep_1(sK0,sK2,sK2)) != iProver_top
% 51.39/6.99      | v2_struct_0(k1_tsep_1(sK0,sK2,sK2)) = iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | l1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_33491,c_969]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_35217,plain,
% 51.39/6.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),k1_tsep_1(sK0,sK2,sK2)) = iProver_top ),
% 51.39/6.99      inference(global_propositional_subsumption,
% 51.39/6.99                [status(thm)],
% 51.39/6.99                [c_33508,c_29,c_30,c_33,c_1156,c_1640,c_1950,c_20839,
% 51.39/6.99                 c_21808,c_30672]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_35221,plain,
% 51.39/6.99      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),k1_tsep_1(sK0,sK2,sK2)) = iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_17227,c_35217]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_33081,plain,
% 51.39/6.99      ( m1_pre_topc(X0,X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),X1) != iProver_top
% 51.39/6.99      | m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),X0) = iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 51.39/6.99      | l1_pre_topc(X1) != iProver_top
% 51.39/6.99      | v2_pre_topc(X1) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_33031,c_960]) ).
% 51.39/6.99  
% 51.39/6.99  cnf(c_45967,plain,
% 51.39/6.99      ( m1_pre_topc(X0,sK0) != iProver_top
% 51.39/6.99      | m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),X0) = iProver_top
% 51.39/6.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.39/6.99      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 51.39/6.99      | v2_struct_0(sK2) = iProver_top
% 51.39/6.99      | v2_struct_0(sK0) = iProver_top
% 51.39/6.99      | l1_pre_topc(sK0) != iProver_top
% 51.39/6.99      | v2_pre_topc(sK0) != iProver_top ),
% 51.39/6.99      inference(superposition,[status(thm)],[c_969,c_33081]) ).
% 51.39/7.00  
% 51.39/7.00  cnf(c_45976,plain,
% 51.39/7.00      ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),sK0) = iProver_top
% 51.39/7.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.39/7.00      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.39/7.00      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0)) != iProver_top
% 51.39/7.00      | v2_struct_0(sK2) = iProver_top
% 51.39/7.00      | v2_struct_0(sK0) = iProver_top
% 51.39/7.00      | l1_pre_topc(sK0) != iProver_top
% 51.39/7.00      | v2_pre_topc(sK0) != iProver_top ),
% 51.39/7.00      inference(instantiation,[status(thm)],[c_45967]) ).
% 51.39/7.00  
% 51.39/7.00  cnf(c_79282,plain,
% 51.39/7.00      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = u1_struct_0(sK2) ),
% 51.39/7.00      inference(global_propositional_subsumption,
% 51.39/7.00                [status(thm)],
% 51.39/7.00                [c_78753,c_28,c_29,c_30,c_33,c_34,c_46,c_1305,c_33045,
% 51.39/7.00                 c_35221,c_45976]) ).
% 51.39/7.00  
% 51.39/7.00  cnf(c_8171,plain,
% 51.39/7.00      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top
% 51.39/7.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.39/7.00      | m1_pre_topc(sK1,sK0) != iProver_top
% 51.39/7.00      | v2_struct_0(sK3) = iProver_top
% 51.39/7.00      | v2_struct_0(sK1) = iProver_top
% 51.39/7.00      | v2_struct_0(sK0) = iProver_top
% 51.39/7.00      | l1_pre_topc(sK0) != iProver_top ),
% 51.39/7.00      inference(superposition,[status(thm)],[c_8168,c_969]) ).
% 51.39/7.00  
% 51.39/7.00  cnf(c_1422,plain,
% 51.39/7.00      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 51.39/7.00      | ~ m1_pre_topc(sK3,sK0)
% 51.39/7.00      | ~ m1_pre_topc(sK1,sK0)
% 51.39/7.00      | v2_struct_0(sK3)
% 51.39/7.00      | v2_struct_0(sK1)
% 51.39/7.00      | v2_struct_0(sK0)
% 51.39/7.00      | ~ l1_pre_topc(sK0) ),
% 51.39/7.00      inference(instantiation,[status(thm)],[c_6]) ).
% 51.39/7.00  
% 51.39/7.00  cnf(c_1425,plain,
% 51.39/7.00      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top
% 51.39/7.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.39/7.00      | m1_pre_topc(sK1,sK0) != iProver_top
% 51.39/7.00      | v2_struct_0(sK3) = iProver_top
% 51.39/7.00      | v2_struct_0(sK1) = iProver_top
% 51.39/7.00      | v2_struct_0(sK0) = iProver_top
% 51.39/7.00      | l1_pre_topc(sK0) != iProver_top ),
% 51.39/7.00      inference(predicate_to_equality,[status(thm)],[c_1422]) ).
% 51.39/7.00  
% 51.39/7.00  cnf(c_15380,plain,
% 51.39/7.00      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top ),
% 51.39/7.00      inference(global_propositional_subsumption,
% 51.39/7.00                [status(thm)],
% 51.39/7.00                [c_8171,c_28,c_30,c_31,c_32,c_35,c_36,c_1425]) ).
% 51.39/7.00  
% 51.39/7.00  cnf(c_15388,plain,
% 51.39/7.00      ( m1_pre_topc(X0,sK0) != iProver_top
% 51.39/7.00      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0) != iProver_top
% 51.39/7.00      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0)) = iProver_top
% 51.39/7.00      | l1_pre_topc(sK0) != iProver_top
% 51.39/7.00      | v2_pre_topc(sK0) != iProver_top ),
% 51.39/7.00      inference(superposition,[status(thm)],[c_15380,c_961]) ).
% 51.39/7.00  
% 51.39/7.00  cnf(c_15834,plain,
% 51.39/7.00      ( m1_pre_topc(X0,sK0) != iProver_top
% 51.39/7.00      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0) != iProver_top
% 51.39/7.00      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(X0)) = iProver_top ),
% 51.39/7.00      inference(global_propositional_subsumption,
% 51.39/7.00                [status(thm)],
% 51.39/7.00                [c_15388,c_29,c_30]) ).
% 51.39/7.00  
% 51.39/7.00  cnf(c_79324,plain,
% 51.39/7.00      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
% 51.39/7.00      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 51.39/7.00      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) = iProver_top ),
% 51.39/7.00      inference(superposition,[status(thm)],[c_79282,c_15834]) ).
% 51.39/7.00  
% 51.39/7.00  cnf(c_2854,plain,
% 51.39/7.00      ( m1_pre_topc(sK1,sK1) = iProver_top
% 51.39/7.00      | l1_pre_topc(sK2) != iProver_top ),
% 51.39/7.00      inference(superposition,[status(thm)],[c_957,c_2846]) ).
% 51.39/7.00  
% 51.39/7.00  cnf(c_1079,plain,
% 51.39/7.00      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0)
% 51.39/7.00      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
% 51.39/7.00      | ~ m1_pre_topc(sK2,X0)
% 51.39/7.00      | ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))
% 51.39/7.00      | ~ l1_pre_topc(X0)
% 51.39/7.00      | ~ v2_pre_topc(X0) ),
% 51.39/7.00      inference(instantiation,[status(thm)],[c_15]) ).
% 51.39/7.00  
% 51.39/7.00  cnf(c_1080,plain,
% 51.39/7.00      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0) != iProver_top
% 51.39/7.00      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) = iProver_top
% 51.39/7.00      | m1_pre_topc(sK2,X0) != iProver_top
% 51.39/7.00      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) != iProver_top
% 51.39/7.00      | l1_pre_topc(X0) != iProver_top
% 51.39/7.00      | v2_pre_topc(X0) != iProver_top ),
% 51.39/7.00      inference(predicate_to_equality,[status(thm)],[c_1079]) ).
% 51.39/7.00  
% 51.39/7.00  cnf(c_1082,plain,
% 51.39/7.00      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) = iProver_top
% 51.39/7.00      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) != iProver_top
% 51.39/7.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.39/7.00      | r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) != iProver_top
% 51.39/7.00      | l1_pre_topc(sK0) != iProver_top
% 51.39/7.00      | v2_pre_topc(sK0) != iProver_top ),
% 51.39/7.00      inference(instantiation,[status(thm)],[c_1080]) ).
% 51.39/7.00  
% 51.39/7.00  cnf(c_16,negated_conjecture,
% 51.39/7.00      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
% 51.39/7.00      inference(cnf_transformation,[],[f71]) ).
% 51.39/7.00  
% 51.39/7.00  cnf(c_39,plain,
% 51.39/7.00      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) != iProver_top ),
% 51.39/7.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 51.39/7.00  
% 51.39/7.00  cnf(contradiction,plain,
% 51.39/7.00      ( $false ),
% 51.39/7.00      inference(minisat,
% 51.39/7.00                [status(thm)],
% 51.39/7.00                [c_149665,c_79324,c_9199,c_2854,c_1425,c_1156,c_1082,
% 51.39/7.00                 c_39,c_38,c_36,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_28]) ).
% 51.39/7.00  
% 51.39/7.00  
% 51.39/7.00  % SZS output end CNFRefutation for theBenchmark.p
% 51.39/7.00  
% 51.39/7.00  ------                               Statistics
% 51.39/7.00  
% 51.39/7.00  ------ Selected
% 51.39/7.00  
% 51.39/7.00  total_time:                             6.303
% 51.39/7.00  
%------------------------------------------------------------------------------
