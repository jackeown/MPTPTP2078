%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:47 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 524 expanded)
%              Number of clauses        :   77 ( 116 expanded)
%              Number of leaves         :   14 ( 154 expanded)
%              Depth                    :   26
%              Number of atoms          :  638 (4731 expanded)
%              Number of equality atoms :  160 ( 937 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   22 (   3 average)
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
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ~ ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X2))
                         => X3 != X4 )
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => X3 != X4 ) ) ) ) ) ) ),
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
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X1))
                           => X3 != X4 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
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
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => X3 != X5 ) ) ) ) ) ) ),
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => X3 != X5 ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( X3 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) )
          & ! [X5] :
              ( X3 != X5
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
     => ( ! [X4] :
            ( sK4 != X4
            | ~ m1_subset_1(X4,u1_struct_0(X2)) )
        & ! [X5] :
            ( sK4 != X5
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X2)) )
              & ! [X5] :
                  ( X3 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ! [X4] :
                ( X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
            & ! [X5] :
                ( X3 != X5
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,sK3))) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( X3 != X4
                    | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                & ! [X5] :
                    ( X3 != X5
                    | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
                & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,sK2,X2))) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    & ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK1,X1,X2))) )
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ! [X4] :
        ( sK4 != X4
        | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
    & ! [X5] :
        ( sK4 != X5
        | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
    & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f36,f35,f34,f33])).

fof(f63,plain,(
    m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
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
    inference(equality_resolution,[],[f52])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X5] :
      ( sK4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f64])).

fof(f65,plain,(
    ! [X4] :
      ( sK4 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(equality_resolution,[],[f65])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_841,plain,
    ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_851,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2453,plain,
    ( r2_hidden(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top
    | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_841,c_851])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_840,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_838,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f69])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_223,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_18,c_17,c_16])).

cnf(c_224,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(renaming,[status(thm)],[c_223])).

cnf(c_834,plain,
    ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_1410,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_838,c_834])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_28,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_29,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_30,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2061,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1410,c_28,c_29,c_30])).

cnf(c_2062,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2061])).

cnf(c_2070,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_840,c_2062])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1174,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k1_tsep_1(sK1,X0,sK3)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_1610,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1174])).

cnf(c_2127,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2070,c_27,c_26,c_25,c_24,c_23,c_22,c_1610])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_855,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3272,plain,
    ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2127,c_855])).

cnf(c_4671,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2453,c_3272])).

cnf(c_31,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_32,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_33,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1253,plain,
    ( v2_struct_0(k1_tsep_1(sK1,sK2,sK3))
    | ~ l1_struct_0(k1_tsep_1(sK1,sK2,sK3))
    | ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1254,plain,
    ( v2_struct_0(k1_tsep_1(sK1,sK2,sK3)) = iProver_top
    | l1_struct_0(k1_tsep_1(sK1,sK2,sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1253])).

cnf(c_1164,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | m1_pre_topc(k1_tsep_1(sK1,X0,sK3),sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1271,plain,
    ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1164])).

cnf(c_1272,plain,
    ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),sK1) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1271])).

cnf(c_11,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1680,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK1,sK2,sK3))
    | l1_struct_0(k1_tsep_1(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1681,plain,
    ( l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) != iProver_top
    | l1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1680])).

cnf(c_2018,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v2_struct_0(k1_tsep_1(sK1,sK2,sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2019,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | v2_struct_0(k1_tsep_1(sK1,sK2,sK3)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2018])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2745,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2746,plain,
    ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2745])).

cnf(c_2748,plain,
    ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),sK1) != iProver_top
    | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2746])).

cnf(c_6545,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4671,c_28,c_29,c_30,c_31,c_32,c_33,c_1254,c_1272,c_1681,c_2019,c_2748])).

cnf(c_6546,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6545])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_852,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6551,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6546,c_852])).

cnf(c_20,negated_conjecture,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6922,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6551,c_35])).

cnf(c_6928,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6922,c_852])).

cnf(c_19,negated_conjecture,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6996,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6928,c_36])).

cnf(c_848,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7002,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6996,c_848])).

cnf(c_1661,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_12,c_24])).

cnf(c_1772,plain,
    ( l1_pre_topc(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1661,c_26])).

cnf(c_1784,plain,
    ( l1_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_1772,c_11])).

cnf(c_1785,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1784])).

cnf(c_7017,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7002,c_30,c_1785])).

cnf(c_7022,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7017,c_848])).

cnf(c_1659,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_12,c_22])).

cnf(c_1672,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1659,c_26])).

cnf(c_1769,plain,
    ( l1_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_1672,c_11])).

cnf(c_1770,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1769])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7022,c_1770,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.76/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.01  
% 3.76/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.76/1.01  
% 3.76/1.01  ------  iProver source info
% 3.76/1.01  
% 3.76/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.76/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.76/1.01  git: non_committed_changes: false
% 3.76/1.01  git: last_make_outside_of_git: false
% 3.76/1.01  
% 3.76/1.01  ------ 
% 3.76/1.01  ------ Parsing...
% 3.76/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.76/1.01  
% 3.76/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.76/1.01  
% 3.76/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.76/1.01  
% 3.76/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.76/1.01  ------ Proving...
% 3.76/1.01  ------ Problem Properties 
% 3.76/1.01  
% 3.76/1.01  
% 3.76/1.01  clauses                                 27
% 3.76/1.01  conjectures                             9
% 3.76/1.01  EPR                                     12
% 3.76/1.01  Horn                                    18
% 3.76/1.01  unary                                   9
% 3.76/1.01  binary                                  3
% 3.76/1.01  lits                                    85
% 3.76/1.01  lits eq                                 6
% 3.76/1.01  fd_pure                                 0
% 3.76/1.01  fd_pseudo                               0
% 3.76/1.01  fd_cond                                 0
% 3.76/1.01  fd_pseudo_cond                          4
% 3.76/1.01  AC symbols                              0
% 3.76/1.01  
% 3.76/1.01  ------ Input Options Time Limit: Unbounded
% 3.76/1.01  
% 3.76/1.01  
% 3.76/1.01  ------ 
% 3.76/1.01  Current options:
% 3.76/1.01  ------ 
% 3.76/1.01  
% 3.76/1.01  
% 3.76/1.01  
% 3.76/1.01  
% 3.76/1.01  ------ Proving...
% 3.76/1.01  
% 3.76/1.01  
% 3.76/1.01  % SZS status Theorem for theBenchmark.p
% 3.76/1.01  
% 3.76/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.76/1.01  
% 3.76/1.01  fof(f9,conjecture,(
% 3.76/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 3.76/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.01  
% 3.76/1.01  fof(f10,negated_conjecture,(
% 3.76/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 3.76/1.01    inference(negated_conjecture,[],[f9])).
% 3.76/1.01  
% 3.76/1.01  fof(f11,plain,(
% 3.76/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => X3 != X5))))))),
% 3.76/1.01    inference(rectify,[],[f10])).
% 3.76/1.01  
% 3.76/1.01  fof(f12,plain,(
% 3.76/1.01    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => X3 != X5))))))),
% 3.76/1.01    inference(pure_predicate_removal,[],[f11])).
% 3.76/1.01  
% 3.76/1.01  fof(f24,plain,(
% 3.76/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.76/1.01    inference(ennf_transformation,[],[f12])).
% 3.76/1.01  
% 3.76/1.01  fof(f25,plain,(
% 3.76/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.76/1.01    inference(flattening,[],[f24])).
% 3.76/1.01  
% 3.76/1.01  fof(f36,plain,(
% 3.76/1.01    ( ! [X2,X0,X1] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) => (! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2))))) )),
% 3.76/1.01    introduced(choice_axiom,[])).
% 3.76/1.01  
% 3.76/1.01  fof(f35,plain,(
% 3.76/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,sK3)))) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.76/1.01    introduced(choice_axiom,[])).
% 3.76/1.01  
% 3.76/1.01  fof(f34,plain,(
% 3.76/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,sK2,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.76/1.01    introduced(choice_axiom,[])).
% 3.76/1.01  
% 3.76/1.01  fof(f33,plain,(
% 3.76/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK1,X1,X2)))) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.76/1.01    introduced(choice_axiom,[])).
% 3.76/1.01  
% 3.76/1.01  fof(f37,plain,(
% 3.76/1.01    (((! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) & ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.76/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f36,f35,f34,f33])).
% 3.76/1.01  
% 3.76/1.01  fof(f63,plain,(
% 3.76/1.01    m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))),
% 3.76/1.01    inference(cnf_transformation,[],[f37])).
% 3.76/1.01  
% 3.76/1.01  fof(f3,axiom,(
% 3.76/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.76/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.01  
% 3.76/1.01  fof(f14,plain,(
% 3.76/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.76/1.01    inference(ennf_transformation,[],[f3])).
% 3.76/1.01  
% 3.76/1.01  fof(f15,plain,(
% 3.76/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.76/1.01    inference(flattening,[],[f14])).
% 3.76/1.01  
% 3.76/1.01  fof(f48,plain,(
% 3.76/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.76/1.01    inference(cnf_transformation,[],[f15])).
% 3.76/1.01  
% 3.76/1.01  fof(f62,plain,(
% 3.76/1.01    m1_pre_topc(sK3,sK1)),
% 3.76/1.01    inference(cnf_transformation,[],[f37])).
% 3.76/1.01  
% 3.76/1.01  fof(f60,plain,(
% 3.76/1.01    m1_pre_topc(sK2,sK1)),
% 3.76/1.01    inference(cnf_transformation,[],[f37])).
% 3.76/1.01  
% 3.76/1.01  fof(f7,axiom,(
% 3.76/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3))))))),
% 3.76/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.01  
% 3.76/1.01  fof(f20,plain,(
% 3.76/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.76/1.01    inference(ennf_transformation,[],[f7])).
% 3.76/1.01  
% 3.76/1.01  fof(f21,plain,(
% 3.76/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.01    inference(flattening,[],[f20])).
% 3.76/1.01  
% 3.76/1.01  fof(f32,plain,(
% 3.76/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.01    inference(nnf_transformation,[],[f21])).
% 3.76/1.01  
% 3.76/1.01  fof(f52,plain,(
% 3.76/1.01    ( ! [X2,X0,X3,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.01    inference(cnf_transformation,[],[f32])).
% 3.76/1.01  
% 3.76/1.01  fof(f69,plain,(
% 3.76/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.01    inference(equality_resolution,[],[f52])).
% 3.76/1.01  
% 3.76/1.01  fof(f8,axiom,(
% 3.76/1.01    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.76/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.01  
% 3.76/1.01  fof(f22,plain,(
% 3.76/1.01    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.76/1.01    inference(ennf_transformation,[],[f8])).
% 3.76/1.01  
% 3.76/1.01  fof(f23,plain,(
% 3.76/1.01    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.76/1.01    inference(flattening,[],[f22])).
% 3.76/1.01  
% 3.76/1.01  fof(f54,plain,(
% 3.76/1.01    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.01    inference(cnf_transformation,[],[f23])).
% 3.76/1.01  
% 3.76/1.01  fof(f55,plain,(
% 3.76/1.01    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.01    inference(cnf_transformation,[],[f23])).
% 3.76/1.01  
% 3.76/1.01  fof(f56,plain,(
% 3.76/1.01    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.76/1.01    inference(cnf_transformation,[],[f23])).
% 3.76/1.01  
% 3.76/1.01  fof(f57,plain,(
% 3.76/1.01    ~v2_struct_0(sK1)),
% 3.76/1.01    inference(cnf_transformation,[],[f37])).
% 3.76/1.01  
% 3.76/1.01  fof(f58,plain,(
% 3.76/1.01    l1_pre_topc(sK1)),
% 3.76/1.01    inference(cnf_transformation,[],[f37])).
% 3.76/1.01  
% 3.76/1.01  fof(f59,plain,(
% 3.76/1.01    ~v2_struct_0(sK2)),
% 3.76/1.01    inference(cnf_transformation,[],[f37])).
% 3.76/1.01  
% 3.76/1.01  fof(f61,plain,(
% 3.76/1.01    ~v2_struct_0(sK3)),
% 3.76/1.01    inference(cnf_transformation,[],[f37])).
% 3.76/1.01  
% 3.76/1.01  fof(f1,axiom,(
% 3.76/1.01    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.76/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.01  
% 3.76/1.01  fof(f26,plain,(
% 3.76/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.76/1.01    inference(nnf_transformation,[],[f1])).
% 3.76/1.01  
% 3.76/1.01  fof(f27,plain,(
% 3.76/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.76/1.01    inference(flattening,[],[f26])).
% 3.76/1.01  
% 3.76/1.01  fof(f28,plain,(
% 3.76/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.76/1.01    inference(rectify,[],[f27])).
% 3.76/1.01  
% 3.76/1.01  fof(f29,plain,(
% 3.76/1.01    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.76/1.01    introduced(choice_axiom,[])).
% 3.76/1.01  
% 3.76/1.01  fof(f30,plain,(
% 3.76/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.76/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.76/1.01  
% 3.76/1.01  fof(f38,plain,(
% 3.76/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.76/1.01    inference(cnf_transformation,[],[f30])).
% 3.76/1.01  
% 3.76/1.01  fof(f68,plain,(
% 3.76/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 3.76/1.01    inference(equality_resolution,[],[f38])).
% 3.76/1.01  
% 3.76/1.01  fof(f6,axiom,(
% 3.76/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.76/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.01  
% 3.76/1.01  fof(f18,plain,(
% 3.76/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.76/1.01    inference(ennf_transformation,[],[f6])).
% 3.76/1.01  
% 3.76/1.01  fof(f19,plain,(
% 3.76/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.76/1.01    inference(flattening,[],[f18])).
% 3.76/1.01  
% 3.76/1.01  fof(f51,plain,(
% 3.76/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.76/1.01    inference(cnf_transformation,[],[f19])).
% 3.76/1.01  
% 3.76/1.01  fof(f4,axiom,(
% 3.76/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.76/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.01  
% 3.76/1.01  fof(f16,plain,(
% 3.76/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.76/1.01    inference(ennf_transformation,[],[f4])).
% 3.76/1.01  
% 3.76/1.01  fof(f49,plain,(
% 3.76/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.76/1.01    inference(cnf_transformation,[],[f16])).
% 3.76/1.01  
% 3.76/1.01  fof(f5,axiom,(
% 3.76/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.76/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.01  
% 3.76/1.01  fof(f17,plain,(
% 3.76/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.76/1.01    inference(ennf_transformation,[],[f5])).
% 3.76/1.01  
% 3.76/1.01  fof(f50,plain,(
% 3.76/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.76/1.01    inference(cnf_transformation,[],[f17])).
% 3.76/1.01  
% 3.76/1.01  fof(f2,axiom,(
% 3.76/1.01    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.76/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.01  
% 3.76/1.01  fof(f13,plain,(
% 3.76/1.01    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.76/1.01    inference(ennf_transformation,[],[f2])).
% 3.76/1.01  
% 3.76/1.01  fof(f31,plain,(
% 3.76/1.01    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.76/1.01    inference(nnf_transformation,[],[f13])).
% 3.76/1.01  
% 3.76/1.01  fof(f45,plain,(
% 3.76/1.01    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.76/1.01    inference(cnf_transformation,[],[f31])).
% 3.76/1.01  
% 3.76/1.01  fof(f64,plain,(
% 3.76/1.01    ( ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 3.76/1.01    inference(cnf_transformation,[],[f37])).
% 3.76/1.01  
% 3.76/1.01  fof(f71,plain,(
% 3.76/1.01    ~m1_subset_1(sK4,u1_struct_0(sK2))),
% 3.76/1.01    inference(equality_resolution,[],[f64])).
% 3.76/1.01  
% 3.76/1.01  fof(f65,plain,(
% 3.76/1.01    ( ! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) )),
% 3.76/1.01    inference(cnf_transformation,[],[f37])).
% 3.76/1.01  
% 3.76/1.01  fof(f70,plain,(
% 3.76/1.01    ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 3.76/1.01    inference(equality_resolution,[],[f65])).
% 3.76/1.01  
% 3.76/1.01  cnf(c_21,negated_conjecture,
% 3.76/1.01      ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
% 3.76/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_841,plain,
% 3.76/1.01      ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_10,plain,
% 3.76/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.76/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_851,plain,
% 3.76/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 3.76/1.01      | r2_hidden(X0,X1) = iProver_top
% 3.76/1.01      | v1_xboole_0(X1) = iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_2453,plain,
% 3.76/1.01      ( r2_hidden(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top
% 3.76/1.01      | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 3.76/1.01      inference(superposition,[status(thm)],[c_841,c_851]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_22,negated_conjecture,
% 3.76/1.01      ( m1_pre_topc(sK3,sK1) ),
% 3.76/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_840,plain,
% 3.76/1.01      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_24,negated_conjecture,
% 3.76/1.01      ( m1_pre_topc(sK2,sK1) ),
% 3.76/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_838,plain,
% 3.76/1.01      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_15,plain,
% 3.76/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.76/1.01      | ~ m1_pre_topc(X2,X1)
% 3.76/1.01      | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 3.76/1.01      | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 3.76/1.01      | v2_struct_0(X1)
% 3.76/1.01      | v2_struct_0(X0)
% 3.76/1.01      | v2_struct_0(X2)
% 3.76/1.01      | v2_struct_0(k1_tsep_1(X1,X0,X2))
% 3.76/1.01      | ~ l1_pre_topc(X1)
% 3.76/1.01      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 3.76/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_18,plain,
% 3.76/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.76/1.01      | ~ m1_pre_topc(X2,X1)
% 3.76/1.01      | v2_struct_0(X1)
% 3.76/1.01      | v2_struct_0(X0)
% 3.76/1.01      | v2_struct_0(X2)
% 3.76/1.01      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 3.76/1.01      | ~ l1_pre_topc(X1) ),
% 3.76/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_17,plain,
% 3.76/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.76/1.01      | ~ m1_pre_topc(X2,X1)
% 3.76/1.01      | v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 3.76/1.01      | v2_struct_0(X1)
% 3.76/1.01      | v2_struct_0(X0)
% 3.76/1.01      | v2_struct_0(X2)
% 3.76/1.01      | ~ l1_pre_topc(X1) ),
% 3.76/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_16,plain,
% 3.76/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.76/1.01      | ~ m1_pre_topc(X2,X1)
% 3.76/1.01      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 3.76/1.01      | v2_struct_0(X1)
% 3.76/1.01      | v2_struct_0(X0)
% 3.76/1.01      | v2_struct_0(X2)
% 3.76/1.01      | ~ l1_pre_topc(X1) ),
% 3.76/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_223,plain,
% 3.76/1.01      ( v2_struct_0(X2)
% 3.76/1.01      | v2_struct_0(X0)
% 3.76/1.01      | v2_struct_0(X1)
% 3.76/1.01      | ~ m1_pre_topc(X2,X1)
% 3.76/1.01      | ~ m1_pre_topc(X0,X1)
% 3.76/1.01      | ~ l1_pre_topc(X1)
% 3.76/1.01      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 3.76/1.01      inference(global_propositional_subsumption,
% 3.76/1.01                [status(thm)],
% 3.76/1.01                [c_15,c_18,c_17,c_16]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_224,plain,
% 3.76/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.76/1.01      | ~ m1_pre_topc(X2,X1)
% 3.76/1.01      | v2_struct_0(X0)
% 3.76/1.01      | v2_struct_0(X1)
% 3.76/1.01      | v2_struct_0(X2)
% 3.76/1.01      | ~ l1_pre_topc(X1)
% 3.76/1.01      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 3.76/1.01      inference(renaming,[status(thm)],[c_223]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_834,plain,
% 3.76/1.01      ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
% 3.76/1.01      | m1_pre_topc(X1,X0) != iProver_top
% 3.76/1.01      | m1_pre_topc(X2,X0) != iProver_top
% 3.76/1.01      | v2_struct_0(X0) = iProver_top
% 3.76/1.01      | v2_struct_0(X1) = iProver_top
% 3.76/1.01      | v2_struct_0(X2) = iProver_top
% 3.76/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_1410,plain,
% 3.76/1.01      ( u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))
% 3.76/1.01      | m1_pre_topc(X0,sK1) != iProver_top
% 3.76/1.01      | v2_struct_0(X0) = iProver_top
% 3.76/1.01      | v2_struct_0(sK1) = iProver_top
% 3.76/1.01      | v2_struct_0(sK2) = iProver_top
% 3.76/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 3.76/1.01      inference(superposition,[status(thm)],[c_838,c_834]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_27,negated_conjecture,
% 3.76/1.01      ( ~ v2_struct_0(sK1) ),
% 3.76/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_28,plain,
% 3.76/1.01      ( v2_struct_0(sK1) != iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_26,negated_conjecture,
% 3.76/1.01      ( l1_pre_topc(sK1) ),
% 3.76/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_29,plain,
% 3.76/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 3.76/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.76/1.01  
% 3.76/1.01  cnf(c_25,negated_conjecture,
% 3.76/1.02      ( ~ v2_struct_0(sK2) ),
% 3.76/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_30,plain,
% 3.76/1.02      ( v2_struct_0(sK2) != iProver_top ),
% 3.76/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_2061,plain,
% 3.76/1.02      ( v2_struct_0(X0) = iProver_top
% 3.76/1.02      | m1_pre_topc(X0,sK1) != iProver_top
% 3.76/1.02      | u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0)) ),
% 3.76/1.02      inference(global_propositional_subsumption,
% 3.76/1.02                [status(thm)],
% 3.76/1.02                [c_1410,c_28,c_29,c_30]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_2062,plain,
% 3.76/1.02      ( u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))
% 3.76/1.02      | m1_pre_topc(X0,sK1) != iProver_top
% 3.76/1.02      | v2_struct_0(X0) = iProver_top ),
% 3.76/1.02      inference(renaming,[status(thm)],[c_2061]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_2070,plain,
% 3.76/1.02      ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
% 3.76/1.02      | v2_struct_0(sK3) = iProver_top ),
% 3.76/1.02      inference(superposition,[status(thm)],[c_840,c_2062]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_23,negated_conjecture,
% 3.76/1.02      ( ~ v2_struct_0(sK3) ),
% 3.76/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_1174,plain,
% 3.76/1.02      ( ~ m1_pre_topc(X0,sK1)
% 3.76/1.02      | ~ m1_pre_topc(sK3,sK1)
% 3.76/1.02      | v2_struct_0(X0)
% 3.76/1.02      | v2_struct_0(sK1)
% 3.76/1.02      | v2_struct_0(sK3)
% 3.76/1.02      | ~ l1_pre_topc(sK1)
% 3.76/1.02      | u1_struct_0(k1_tsep_1(sK1,X0,sK3)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK3)) ),
% 3.76/1.02      inference(instantiation,[status(thm)],[c_224]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_1610,plain,
% 3.76/1.02      ( ~ m1_pre_topc(sK2,sK1)
% 3.76/1.02      | ~ m1_pre_topc(sK3,sK1)
% 3.76/1.02      | v2_struct_0(sK1)
% 3.76/1.02      | v2_struct_0(sK2)
% 3.76/1.02      | v2_struct_0(sK3)
% 3.76/1.02      | ~ l1_pre_topc(sK1)
% 3.76/1.02      | u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.76/1.02      inference(instantiation,[status(thm)],[c_1174]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_2127,plain,
% 3.76/1.02      ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.76/1.02      inference(global_propositional_subsumption,
% 3.76/1.02                [status(thm)],
% 3.76/1.02                [c_2070,c_27,c_26,c_25,c_24,c_23,c_22,c_1610]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_5,plain,
% 3.76/1.02      ( r2_hidden(X0,X1)
% 3.76/1.02      | r2_hidden(X0,X2)
% 3.76/1.02      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.76/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_855,plain,
% 3.76/1.02      ( r2_hidden(X0,X1) = iProver_top
% 3.76/1.02      | r2_hidden(X0,X2) = iProver_top
% 3.76/1.02      | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 3.76/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_3272,plain,
% 3.76/1.02      ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
% 3.76/1.02      | r2_hidden(X0,u1_struct_0(sK2)) = iProver_top
% 3.76/1.02      | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top ),
% 3.76/1.02      inference(superposition,[status(thm)],[c_2127,c_855]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_4671,plain,
% 3.76/1.02      ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
% 3.76/1.02      | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
% 3.76/1.02      | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 3.76/1.02      inference(superposition,[status(thm)],[c_2453,c_3272]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_31,plain,
% 3.76/1.02      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.76/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_32,plain,
% 3.76/1.02      ( v2_struct_0(sK3) != iProver_top ),
% 3.76/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_33,plain,
% 3.76/1.02      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 3.76/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_13,plain,
% 3.76/1.02      ( v2_struct_0(X0)
% 3.76/1.02      | ~ l1_struct_0(X0)
% 3.76/1.02      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.76/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_1253,plain,
% 3.76/1.02      ( v2_struct_0(k1_tsep_1(sK1,sK2,sK3))
% 3.76/1.02      | ~ l1_struct_0(k1_tsep_1(sK1,sK2,sK3))
% 3.76/1.02      | ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
% 3.76/1.02      inference(instantiation,[status(thm)],[c_13]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_1254,plain,
% 3.76/1.02      ( v2_struct_0(k1_tsep_1(sK1,sK2,sK3)) = iProver_top
% 3.76/1.02      | l1_struct_0(k1_tsep_1(sK1,sK2,sK3)) != iProver_top
% 3.76/1.02      | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top ),
% 3.76/1.02      inference(predicate_to_equality,[status(thm)],[c_1253]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_1164,plain,
% 3.76/1.02      ( ~ m1_pre_topc(X0,sK1)
% 3.76/1.02      | m1_pre_topc(k1_tsep_1(sK1,X0,sK3),sK1)
% 3.76/1.02      | ~ m1_pre_topc(sK3,sK1)
% 3.76/1.02      | v2_struct_0(X0)
% 3.76/1.02      | v2_struct_0(sK1)
% 3.76/1.02      | v2_struct_0(sK3)
% 3.76/1.02      | ~ l1_pre_topc(sK1) ),
% 3.76/1.02      inference(instantiation,[status(thm)],[c_16]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_1271,plain,
% 3.76/1.02      ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),sK1)
% 3.76/1.02      | ~ m1_pre_topc(sK2,sK1)
% 3.76/1.02      | ~ m1_pre_topc(sK3,sK1)
% 3.76/1.02      | v2_struct_0(sK1)
% 3.76/1.02      | v2_struct_0(sK2)
% 3.76/1.02      | v2_struct_0(sK3)
% 3.76/1.02      | ~ l1_pre_topc(sK1) ),
% 3.76/1.02      inference(instantiation,[status(thm)],[c_1164]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_1272,plain,
% 3.76/1.02      ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),sK1) = iProver_top
% 3.76/1.02      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.76/1.02      | m1_pre_topc(sK3,sK1) != iProver_top
% 3.76/1.02      | v2_struct_0(sK1) = iProver_top
% 3.76/1.02      | v2_struct_0(sK2) = iProver_top
% 3.76/1.02      | v2_struct_0(sK3) = iProver_top
% 3.76/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 3.76/1.02      inference(predicate_to_equality,[status(thm)],[c_1271]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_11,plain,
% 3.76/1.02      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.76/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_1680,plain,
% 3.76/1.02      ( ~ l1_pre_topc(k1_tsep_1(sK1,sK2,sK3))
% 3.76/1.02      | l1_struct_0(k1_tsep_1(sK1,sK2,sK3)) ),
% 3.76/1.02      inference(instantiation,[status(thm)],[c_11]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_1681,plain,
% 3.76/1.02      ( l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) != iProver_top
% 3.76/1.02      | l1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = iProver_top ),
% 3.76/1.02      inference(predicate_to_equality,[status(thm)],[c_1680]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_2018,plain,
% 3.76/1.02      ( ~ m1_pre_topc(sK2,sK1)
% 3.76/1.02      | ~ m1_pre_topc(sK3,sK1)
% 3.76/1.02      | ~ v2_struct_0(k1_tsep_1(sK1,sK2,sK3))
% 3.76/1.02      | v2_struct_0(sK1)
% 3.76/1.02      | v2_struct_0(sK2)
% 3.76/1.02      | v2_struct_0(sK3)
% 3.76/1.02      | ~ l1_pre_topc(sK1) ),
% 3.76/1.02      inference(instantiation,[status(thm)],[c_18]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_2019,plain,
% 3.76/1.02      ( m1_pre_topc(sK2,sK1) != iProver_top
% 3.76/1.02      | m1_pre_topc(sK3,sK1) != iProver_top
% 3.76/1.02      | v2_struct_0(k1_tsep_1(sK1,sK2,sK3)) != iProver_top
% 3.76/1.02      | v2_struct_0(sK1) = iProver_top
% 3.76/1.02      | v2_struct_0(sK2) = iProver_top
% 3.76/1.02      | v2_struct_0(sK3) = iProver_top
% 3.76/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 3.76/1.02      inference(predicate_to_equality,[status(thm)],[c_2018]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_12,plain,
% 3.76/1.02      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.76/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_2745,plain,
% 3.76/1.02      ( ~ m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),X0)
% 3.76/1.02      | ~ l1_pre_topc(X0)
% 3.76/1.02      | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) ),
% 3.76/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_2746,plain,
% 3.76/1.02      ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),X0) != iProver_top
% 3.76/1.02      | l1_pre_topc(X0) != iProver_top
% 3.76/1.02      | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) = iProver_top ),
% 3.76/1.02      inference(predicate_to_equality,[status(thm)],[c_2745]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_2748,plain,
% 3.76/1.02      ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),sK1) != iProver_top
% 3.76/1.02      | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) = iProver_top
% 3.76/1.02      | l1_pre_topc(sK1) != iProver_top ),
% 3.76/1.02      inference(instantiation,[status(thm)],[c_2746]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_6545,plain,
% 3.76/1.02      ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
% 3.76/1.02      | r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top ),
% 3.76/1.02      inference(global_propositional_subsumption,
% 3.76/1.02                [status(thm)],
% 3.76/1.02                [c_4671,c_28,c_29,c_30,c_31,c_32,c_33,c_1254,c_1272,
% 3.76/1.02                 c_1681,c_2019,c_2748]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_6546,plain,
% 3.76/1.02      ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
% 3.76/1.02      | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.76/1.02      inference(renaming,[status(thm)],[c_6545]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_8,plain,
% 3.76/1.02      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.76/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_852,plain,
% 3.76/1.02      ( m1_subset_1(X0,X1) = iProver_top
% 3.76/1.02      | r2_hidden(X0,X1) != iProver_top
% 3.76/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.76/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_6551,plain,
% 3.76/1.02      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top
% 3.76/1.02      | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
% 3.76/1.02      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.76/1.02      inference(superposition,[status(thm)],[c_6546,c_852]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_20,negated_conjecture,
% 3.76/1.02      ( ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 3.76/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_35,plain,
% 3.76/1.02      ( m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top ),
% 3.76/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_6922,plain,
% 3.76/1.02      ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
% 3.76/1.02      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.76/1.02      inference(global_propositional_subsumption,
% 3.76/1.02                [status(thm)],
% 3.76/1.02                [c_6551,c_35]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_6928,plain,
% 3.76/1.02      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top
% 3.76/1.02      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
% 3.76/1.02      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.76/1.02      inference(superposition,[status(thm)],[c_6922,c_852]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_19,negated_conjecture,
% 3.76/1.02      ( ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.76/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_36,plain,
% 3.76/1.02      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 3.76/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_6996,plain,
% 3.76/1.02      ( v1_xboole_0(u1_struct_0(sK2)) = iProver_top
% 3.76/1.02      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.76/1.02      inference(global_propositional_subsumption,
% 3.76/1.02                [status(thm)],
% 3.76/1.02                [c_6928,c_36]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_848,plain,
% 3.76/1.02      ( v2_struct_0(X0) = iProver_top
% 3.76/1.02      | l1_struct_0(X0) != iProver_top
% 3.76/1.02      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.76/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_7002,plain,
% 3.76/1.02      ( v2_struct_0(sK2) = iProver_top
% 3.76/1.02      | l1_struct_0(sK2) != iProver_top
% 3.76/1.02      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.76/1.02      inference(superposition,[status(thm)],[c_6996,c_848]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_1661,plain,
% 3.76/1.02      ( ~ l1_pre_topc(sK1) | l1_pre_topc(sK2) ),
% 3.76/1.02      inference(resolution,[status(thm)],[c_12,c_24]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_1772,plain,
% 3.76/1.02      ( l1_pre_topc(sK2) ),
% 3.76/1.02      inference(global_propositional_subsumption,
% 3.76/1.02                [status(thm)],
% 3.76/1.02                [c_1661,c_26]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_1784,plain,
% 3.76/1.02      ( l1_struct_0(sK2) ),
% 3.76/1.02      inference(resolution,[status(thm)],[c_1772,c_11]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_1785,plain,
% 3.76/1.02      ( l1_struct_0(sK2) = iProver_top ),
% 3.76/1.02      inference(predicate_to_equality,[status(thm)],[c_1784]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_7017,plain,
% 3.76/1.02      ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.76/1.02      inference(global_propositional_subsumption,
% 3.76/1.02                [status(thm)],
% 3.76/1.02                [c_7002,c_30,c_1785]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_7022,plain,
% 3.76/1.02      ( v2_struct_0(sK3) = iProver_top
% 3.76/1.02      | l1_struct_0(sK3) != iProver_top ),
% 3.76/1.02      inference(superposition,[status(thm)],[c_7017,c_848]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_1659,plain,
% 3.76/1.02      ( ~ l1_pre_topc(sK1) | l1_pre_topc(sK3) ),
% 3.76/1.02      inference(resolution,[status(thm)],[c_12,c_22]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_1672,plain,
% 3.76/1.02      ( l1_pre_topc(sK3) ),
% 3.76/1.02      inference(global_propositional_subsumption,
% 3.76/1.02                [status(thm)],
% 3.76/1.02                [c_1659,c_26]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_1769,plain,
% 3.76/1.02      ( l1_struct_0(sK3) ),
% 3.76/1.02      inference(resolution,[status(thm)],[c_1672,c_11]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(c_1770,plain,
% 3.76/1.02      ( l1_struct_0(sK3) = iProver_top ),
% 3.76/1.02      inference(predicate_to_equality,[status(thm)],[c_1769]) ).
% 3.76/1.02  
% 3.76/1.02  cnf(contradiction,plain,
% 3.76/1.02      ( $false ),
% 3.76/1.02      inference(minisat,[status(thm)],[c_7022,c_1770,c_32]) ).
% 3.76/1.02  
% 3.76/1.02  
% 3.76/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.76/1.02  
% 3.76/1.02  ------                               Statistics
% 3.76/1.02  
% 3.76/1.02  ------ Selected
% 3.76/1.02  
% 3.76/1.02  total_time:                             0.202
% 3.76/1.02  
%------------------------------------------------------------------------------
