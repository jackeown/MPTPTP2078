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
% DateTime   : Thu Dec  3 12:22:00 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 524 expanded)
%              Number of clauses        :   73 ( 131 expanded)
%              Number of leaves         :   16 ( 149 expanded)
%              Depth                    :   16
%              Number of atoms          :  508 (3794 expanded)
%              Number of equality atoms :  106 ( 137 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f14,plain,(
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
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f15,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ! [X3] :
                    ( m1_pre_topc(X3,X0)
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( r1_tsep_1(X3,X2)
            | r1_tsep_1(X2,X3) )
          & ( ~ r1_tsep_1(X3,X1)
            | ~ r1_tsep_1(X1,X3) )
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X3,X0) )
     => ( ( r1_tsep_1(sK5,X2)
          | r1_tsep_1(X2,sK5) )
        & ( ~ r1_tsep_1(sK5,X1)
          | ~ r1_tsep_1(X1,sK5) )
        & m1_pre_topc(X1,X2)
        & m1_pre_topc(sK5,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & ( ~ r1_tsep_1(X3,X1)
                | ~ r1_tsep_1(X1,X3) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X3,X0) )
          & m1_pre_topc(X2,X0) )
     => ( ? [X3] :
            ( ( r1_tsep_1(X3,sK4)
              | r1_tsep_1(sK4,X3) )
            & ( ~ r1_tsep_1(X3,X1)
              | ~ r1_tsep_1(X1,X3) )
            & m1_pre_topc(X1,sK4)
            & m1_pre_topc(X3,X0) )
        & m1_pre_topc(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & ( ~ r1_tsep_1(X3,sK3)
                  | ~ r1_tsep_1(sK3,X3) )
                & m1_pre_topc(sK3,X2)
                & m1_pre_topc(X3,X0) )
            & m1_pre_topc(X2,X0) )
        & m1_pre_topc(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0) )
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK2) )
              & m1_pre_topc(X2,sK2) )
          & m1_pre_topc(X1,sK2) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( r1_tsep_1(sK5,sK4)
      | r1_tsep_1(sK4,sK5) )
    & ( ~ r1_tsep_1(sK5,sK3)
      | ~ r1_tsep_1(sK3,sK5) )
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK5,sK2)
    & m1_pre_topc(sK4,sK2)
    & m1_pre_topc(sK3,sK2)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f38,f37,f36,f35])).

fof(f61,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f32])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,
    ( r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,
    ( ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_636,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_639,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_645,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1240,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_639,c_645])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_646,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2225,plain,
    ( k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X0)
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1240,c_646])).

cnf(c_3272,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(sK3)
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_636,c_2225])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_936,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(resolution,[status(thm)],[c_12,c_21])).

cnf(c_1393,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1424,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1766,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),X0)
    | k3_xboole_0(u1_struct_0(sK3),X0) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2995,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
    | k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1766])).

cnf(c_3463,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3272,c_23,c_19,c_936,c_1393,c_1424,c_2995])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_648,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_651,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1435,plain,
    ( r1_xboole_0(X0,k3_xboole_0(X1,X2)) = iProver_top
    | r2_hidden(sK1(X0,k3_xboole_0(X1,X2)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_648,c_651])).

cnf(c_3470,plain,
    ( r1_xboole_0(X0,k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))) = iProver_top
    | r2_hidden(sK1(X0,u1_struct_0(sK3)),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3463,c_1435])).

cnf(c_3478,plain,
    ( r1_xboole_0(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK1(X0,u1_struct_0(sK3)),u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3470,c_3463])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_647,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_14,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_641,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_struct_0(X1) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_649,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1936,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r2_hidden(X2,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X2,u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X1) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_641,c_649])).

cnf(c_2781,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_xboole_0(u1_struct_0(X1),X2) = iProver_top
    | r2_hidden(sK1(u1_struct_0(X1),X2),u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X1) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_647,c_1936])).

cnf(c_12987,plain,
    ( r1_tsep_1(sK4,X0) != iProver_top
    | r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3478,c_2781])).

cnf(c_13027,plain,
    ( r1_tsep_1(sK4,sK5) != iProver_top
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
    | l1_struct_0(sK4) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12987])).

cnf(c_15,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2955,plain,
    ( r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK5,sK3)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2956,plain,
    ( r1_tsep_1(sK3,sK5) = iProver_top
    | r1_tsep_1(sK5,sK3) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2955])).

cnf(c_13,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1928,plain,
    ( r1_tsep_1(sK5,sK3)
    | ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1929,plain,
    ( r1_tsep_1(sK5,sK3) = iProver_top
    | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1928])).

cnf(c_17,negated_conjecture,
    ( r1_tsep_1(sK4,sK5)
    | r1_tsep_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1473,plain,
    ( r1_tsep_1(sK5,sK4)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_15,c_17])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_11,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_43,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_839,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_841,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_1056,plain,
    ( l1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_936,c_23])).

cnf(c_1271,plain,
    ( l1_struct_0(sK4) ),
    inference(resolution,[status(thm)],[c_1056,c_11])).

cnf(c_638,plain,
    ( r1_tsep_1(sK4,sK5) = iProver_top
    | r1_tsep_1(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_640,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X1,X0) = iProver_top
    | l1_struct_0(X1) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1452,plain,
    ( r1_tsep_1(sK5,sK4) = iProver_top
    | l1_struct_0(sK4) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_638,c_640])).

cnf(c_1453,plain,
    ( r1_tsep_1(sK5,sK4)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1452])).

cnf(c_1476,plain,
    ( r1_tsep_1(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1473,c_23,c_20,c_43,c_841,c_1271,c_1453])).

cnf(c_1606,plain,
    ( r1_tsep_1(sK4,sK5)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_1476,c_15])).

cnf(c_1607,plain,
    ( r1_tsep_1(sK4,sK5) = iProver_top
    | l1_struct_0(sK4) != iProver_top
    | l1_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1606])).

cnf(c_1272,plain,
    ( l1_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1271])).

cnf(c_932,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[status(thm)],[c_12,c_19])).

cnf(c_941,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_932,c_23,c_936])).

cnf(c_953,plain,
    ( l1_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_941,c_11])).

cnf(c_954,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_953])).

cnf(c_840,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_839])).

cnf(c_842,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_840])).

cnf(c_42,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_44,plain,
    ( l1_pre_topc(sK5) != iProver_top
    | l1_struct_0(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tsep_1(sK3,sK5)
    | ~ r1_tsep_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_29,plain,
    ( r1_tsep_1(sK3,sK5) != iProver_top
    | r1_tsep_1(sK5,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_27,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_24,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13027,c_2956,c_1929,c_1607,c_1272,c_954,c_842,c_44,c_29,c_27,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.72/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.00  
% 3.72/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/1.00  
% 3.72/1.00  ------  iProver source info
% 3.72/1.00  
% 3.72/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.72/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/1.00  git: non_committed_changes: false
% 3.72/1.00  git: last_make_outside_of_git: false
% 3.72/1.00  
% 3.72/1.00  ------ 
% 3.72/1.00  
% 3.72/1.00  ------ Input Options
% 3.72/1.00  
% 3.72/1.00  --out_options                           all
% 3.72/1.00  --tptp_safe_out                         true
% 3.72/1.00  --problem_path                          ""
% 3.72/1.00  --include_path                          ""
% 3.72/1.00  --clausifier                            res/vclausify_rel
% 3.72/1.00  --clausifier_options                    --mode clausify
% 3.72/1.00  --stdin                                 false
% 3.72/1.00  --stats_out                             sel
% 3.72/1.00  
% 3.72/1.00  ------ General Options
% 3.72/1.00  
% 3.72/1.00  --fof                                   false
% 3.72/1.00  --time_out_real                         604.99
% 3.72/1.00  --time_out_virtual                      -1.
% 3.72/1.00  --symbol_type_check                     false
% 3.72/1.00  --clausify_out                          false
% 3.72/1.00  --sig_cnt_out                           false
% 3.72/1.00  --trig_cnt_out                          false
% 3.72/1.00  --trig_cnt_out_tolerance                1.
% 3.72/1.00  --trig_cnt_out_sk_spl                   false
% 3.72/1.00  --abstr_cl_out                          false
% 3.72/1.00  
% 3.72/1.00  ------ Global Options
% 3.72/1.00  
% 3.72/1.00  --schedule                              none
% 3.72/1.00  --add_important_lit                     false
% 3.72/1.00  --prop_solver_per_cl                    1000
% 3.72/1.00  --min_unsat_core                        false
% 3.72/1.00  --soft_assumptions                      false
% 3.72/1.00  --soft_lemma_size                       3
% 3.72/1.00  --prop_impl_unit_size                   0
% 3.72/1.00  --prop_impl_unit                        []
% 3.72/1.00  --share_sel_clauses                     true
% 3.72/1.00  --reset_solvers                         false
% 3.72/1.00  --bc_imp_inh                            [conj_cone]
% 3.72/1.00  --conj_cone_tolerance                   3.
% 3.72/1.00  --extra_neg_conj                        none
% 3.72/1.00  --large_theory_mode                     true
% 3.72/1.00  --prolific_symb_bound                   200
% 3.72/1.00  --lt_threshold                          2000
% 3.72/1.00  --clause_weak_htbl                      true
% 3.72/1.00  --gc_record_bc_elim                     false
% 3.72/1.00  
% 3.72/1.00  ------ Preprocessing Options
% 3.72/1.00  
% 3.72/1.00  --preprocessing_flag                    true
% 3.72/1.00  --time_out_prep_mult                    0.1
% 3.72/1.00  --splitting_mode                        input
% 3.72/1.00  --splitting_grd                         true
% 3.72/1.00  --splitting_cvd                         false
% 3.72/1.00  --splitting_cvd_svl                     false
% 3.72/1.00  --splitting_nvd                         32
% 3.72/1.00  --sub_typing                            true
% 3.72/1.00  --prep_gs_sim                           false
% 3.72/1.00  --prep_unflatten                        true
% 3.72/1.00  --prep_res_sim                          true
% 3.72/1.00  --prep_upred                            true
% 3.72/1.00  --prep_sem_filter                       exhaustive
% 3.72/1.00  --prep_sem_filter_out                   false
% 3.72/1.00  --pred_elim                             false
% 3.72/1.00  --res_sim_input                         true
% 3.72/1.00  --eq_ax_congr_red                       true
% 3.72/1.00  --pure_diseq_elim                       true
% 3.72/1.00  --brand_transform                       false
% 3.72/1.00  --non_eq_to_eq                          false
% 3.72/1.00  --prep_def_merge                        true
% 3.72/1.00  --prep_def_merge_prop_impl              false
% 3.72/1.00  --prep_def_merge_mbd                    true
% 3.72/1.00  --prep_def_merge_tr_red                 false
% 3.72/1.00  --prep_def_merge_tr_cl                  false
% 3.72/1.00  --smt_preprocessing                     true
% 3.72/1.00  --smt_ac_axioms                         fast
% 3.72/1.00  --preprocessed_out                      false
% 3.72/1.00  --preprocessed_stats                    false
% 3.72/1.00  
% 3.72/1.00  ------ Abstraction refinement Options
% 3.72/1.00  
% 3.72/1.00  --abstr_ref                             []
% 3.72/1.00  --abstr_ref_prep                        false
% 3.72/1.00  --abstr_ref_until_sat                   false
% 3.72/1.00  --abstr_ref_sig_restrict                funpre
% 3.72/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/1.00  --abstr_ref_under                       []
% 3.72/1.00  
% 3.72/1.00  ------ SAT Options
% 3.72/1.00  
% 3.72/1.00  --sat_mode                              false
% 3.72/1.00  --sat_fm_restart_options                ""
% 3.72/1.00  --sat_gr_def                            false
% 3.72/1.00  --sat_epr_types                         true
% 3.72/1.00  --sat_non_cyclic_types                  false
% 3.72/1.00  --sat_finite_models                     false
% 3.72/1.00  --sat_fm_lemmas                         false
% 3.72/1.00  --sat_fm_prep                           false
% 3.72/1.00  --sat_fm_uc_incr                        true
% 3.72/1.00  --sat_out_model                         small
% 3.72/1.00  --sat_out_clauses                       false
% 3.72/1.00  
% 3.72/1.00  ------ QBF Options
% 3.72/1.00  
% 3.72/1.00  --qbf_mode                              false
% 3.72/1.00  --qbf_elim_univ                         false
% 3.72/1.00  --qbf_dom_inst                          none
% 3.72/1.00  --qbf_dom_pre_inst                      false
% 3.72/1.00  --qbf_sk_in                             false
% 3.72/1.00  --qbf_pred_elim                         true
% 3.72/1.00  --qbf_split                             512
% 3.72/1.00  
% 3.72/1.00  ------ BMC1 Options
% 3.72/1.00  
% 3.72/1.00  --bmc1_incremental                      false
% 3.72/1.00  --bmc1_axioms                           reachable_all
% 3.72/1.00  --bmc1_min_bound                        0
% 3.72/1.00  --bmc1_max_bound                        -1
% 3.72/1.00  --bmc1_max_bound_default                -1
% 3.72/1.00  --bmc1_symbol_reachability              true
% 3.72/1.00  --bmc1_property_lemmas                  false
% 3.72/1.00  --bmc1_k_induction                      false
% 3.72/1.00  --bmc1_non_equiv_states                 false
% 3.72/1.00  --bmc1_deadlock                         false
% 3.72/1.00  --bmc1_ucm                              false
% 3.72/1.00  --bmc1_add_unsat_core                   none
% 3.72/1.00  --bmc1_unsat_core_children              false
% 3.72/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/1.00  --bmc1_out_stat                         full
% 3.72/1.00  --bmc1_ground_init                      false
% 3.72/1.00  --bmc1_pre_inst_next_state              false
% 3.72/1.00  --bmc1_pre_inst_state                   false
% 3.72/1.00  --bmc1_pre_inst_reach_state             false
% 3.72/1.00  --bmc1_out_unsat_core                   false
% 3.72/1.00  --bmc1_aig_witness_out                  false
% 3.72/1.00  --bmc1_verbose                          false
% 3.72/1.00  --bmc1_dump_clauses_tptp                false
% 3.72/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.72/1.00  --bmc1_dump_file                        -
% 3.72/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.72/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.72/1.00  --bmc1_ucm_extend_mode                  1
% 3.72/1.00  --bmc1_ucm_init_mode                    2
% 3.72/1.00  --bmc1_ucm_cone_mode                    none
% 3.72/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.72/1.00  --bmc1_ucm_relax_model                  4
% 3.72/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.72/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/1.00  --bmc1_ucm_layered_model                none
% 3.72/1.00  --bmc1_ucm_max_lemma_size               10
% 3.72/1.00  
% 3.72/1.00  ------ AIG Options
% 3.72/1.00  
% 3.72/1.00  --aig_mode                              false
% 3.72/1.00  
% 3.72/1.00  ------ Instantiation Options
% 3.72/1.00  
% 3.72/1.00  --instantiation_flag                    true
% 3.72/1.00  --inst_sos_flag                         false
% 3.72/1.00  --inst_sos_phase                        true
% 3.72/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/1.00  --inst_lit_sel_side                     num_symb
% 3.72/1.00  --inst_solver_per_active                1400
% 3.72/1.00  --inst_solver_calls_frac                1.
% 3.72/1.00  --inst_passive_queue_type               priority_queues
% 3.72/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/1.00  --inst_passive_queues_freq              [25;2]
% 3.72/1.00  --inst_dismatching                      true
% 3.72/1.00  --inst_eager_unprocessed_to_passive     true
% 3.72/1.00  --inst_prop_sim_given                   true
% 3.72/1.00  --inst_prop_sim_new                     false
% 3.72/1.00  --inst_subs_new                         false
% 3.72/1.00  --inst_eq_res_simp                      false
% 3.72/1.00  --inst_subs_given                       false
% 3.72/1.00  --inst_orphan_elimination               true
% 3.72/1.00  --inst_learning_loop_flag               true
% 3.72/1.00  --inst_learning_start                   3000
% 3.72/1.00  --inst_learning_factor                  2
% 3.72/1.00  --inst_start_prop_sim_after_learn       3
% 3.72/1.00  --inst_sel_renew                        solver
% 3.72/1.00  --inst_lit_activity_flag                true
% 3.72/1.00  --inst_restr_to_given                   false
% 3.72/1.00  --inst_activity_threshold               500
% 3.72/1.00  --inst_out_proof                        true
% 3.72/1.00  
% 3.72/1.00  ------ Resolution Options
% 3.72/1.00  
% 3.72/1.00  --resolution_flag                       true
% 3.72/1.00  --res_lit_sel                           adaptive
% 3.72/1.00  --res_lit_sel_side                      none
% 3.72/1.00  --res_ordering                          kbo
% 3.72/1.00  --res_to_prop_solver                    active
% 3.72/1.00  --res_prop_simpl_new                    false
% 3.72/1.00  --res_prop_simpl_given                  true
% 3.72/1.00  --res_passive_queue_type                priority_queues
% 3.72/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/1.00  --res_passive_queues_freq               [15;5]
% 3.72/1.00  --res_forward_subs                      full
% 3.72/1.00  --res_backward_subs                     full
% 3.72/1.00  --res_forward_subs_resolution           true
% 3.72/1.00  --res_backward_subs_resolution          true
% 3.72/1.00  --res_orphan_elimination                true
% 3.72/1.00  --res_time_limit                        2.
% 3.72/1.00  --res_out_proof                         true
% 3.72/1.00  
% 3.72/1.00  ------ Superposition Options
% 3.72/1.00  
% 3.72/1.00  --superposition_flag                    true
% 3.72/1.00  --sup_passive_queue_type                priority_queues
% 3.72/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/1.00  --sup_passive_queues_freq               [1;4]
% 3.72/1.00  --demod_completeness_check              fast
% 3.72/1.00  --demod_use_ground                      true
% 3.72/1.00  --sup_to_prop_solver                    passive
% 3.72/1.00  --sup_prop_simpl_new                    true
% 3.72/1.00  --sup_prop_simpl_given                  true
% 3.72/1.00  --sup_fun_splitting                     false
% 3.72/1.00  --sup_smt_interval                      50000
% 3.72/1.00  
% 3.72/1.00  ------ Superposition Simplification Setup
% 3.72/1.00  
% 3.72/1.00  --sup_indices_passive                   []
% 3.72/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.00  --sup_full_bw                           [BwDemod]
% 3.72/1.00  --sup_immed_triv                        [TrivRules]
% 3.72/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.00  --sup_immed_bw_main                     []
% 3.72/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/1.00  
% 3.72/1.00  ------ Combination Options
% 3.72/1.00  
% 3.72/1.00  --comb_res_mult                         3
% 3.72/1.00  --comb_sup_mult                         2
% 3.72/1.00  --comb_inst_mult                        10
% 3.72/1.00  
% 3.72/1.00  ------ Debug Options
% 3.72/1.00  
% 3.72/1.00  --dbg_backtrace                         false
% 3.72/1.00  --dbg_dump_prop_clauses                 false
% 3.72/1.00  --dbg_dump_prop_clauses_file            -
% 3.72/1.00  --dbg_out_stat                          false
% 3.72/1.00  ------ Parsing...
% 3.72/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/1.00  
% 3.72/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.72/1.00  
% 3.72/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/1.00  
% 3.72/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/1.00  ------ Proving...
% 3.72/1.00  ------ Problem Properties 
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  clauses                                 24
% 3.72/1.00  conjectures                             7
% 3.72/1.00  EPR                                     11
% 3.72/1.00  Horn                                    19
% 3.72/1.00  unary                                   5
% 3.72/1.00  binary                                  9
% 3.72/1.00  lits                                    57
% 3.72/1.00  lits eq                                 4
% 3.72/1.00  fd_pure                                 0
% 3.72/1.00  fd_pseudo                               0
% 3.72/1.00  fd_cond                                 0
% 3.72/1.00  fd_pseudo_cond                          3
% 3.72/1.00  AC symbols                              0
% 3.72/1.00  
% 3.72/1.00  ------ Input Options Time Limit: Unbounded
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  ------ 
% 3.72/1.00  Current options:
% 3.72/1.00  ------ 
% 3.72/1.00  
% 3.72/1.00  ------ Input Options
% 3.72/1.00  
% 3.72/1.00  --out_options                           all
% 3.72/1.00  --tptp_safe_out                         true
% 3.72/1.00  --problem_path                          ""
% 3.72/1.00  --include_path                          ""
% 3.72/1.00  --clausifier                            res/vclausify_rel
% 3.72/1.00  --clausifier_options                    --mode clausify
% 3.72/1.00  --stdin                                 false
% 3.72/1.00  --stats_out                             sel
% 3.72/1.00  
% 3.72/1.00  ------ General Options
% 3.72/1.00  
% 3.72/1.00  --fof                                   false
% 3.72/1.00  --time_out_real                         604.99
% 3.72/1.00  --time_out_virtual                      -1.
% 3.72/1.00  --symbol_type_check                     false
% 3.72/1.00  --clausify_out                          false
% 3.72/1.00  --sig_cnt_out                           false
% 3.72/1.00  --trig_cnt_out                          false
% 3.72/1.00  --trig_cnt_out_tolerance                1.
% 3.72/1.00  --trig_cnt_out_sk_spl                   false
% 3.72/1.00  --abstr_cl_out                          false
% 3.72/1.00  
% 3.72/1.00  ------ Global Options
% 3.72/1.00  
% 3.72/1.00  --schedule                              none
% 3.72/1.00  --add_important_lit                     false
% 3.72/1.00  --prop_solver_per_cl                    1000
% 3.72/1.00  --min_unsat_core                        false
% 3.72/1.00  --soft_assumptions                      false
% 3.72/1.00  --soft_lemma_size                       3
% 3.72/1.00  --prop_impl_unit_size                   0
% 3.72/1.00  --prop_impl_unit                        []
% 3.72/1.00  --share_sel_clauses                     true
% 3.72/1.00  --reset_solvers                         false
% 3.72/1.00  --bc_imp_inh                            [conj_cone]
% 3.72/1.00  --conj_cone_tolerance                   3.
% 3.72/1.00  --extra_neg_conj                        none
% 3.72/1.00  --large_theory_mode                     true
% 3.72/1.00  --prolific_symb_bound                   200
% 3.72/1.00  --lt_threshold                          2000
% 3.72/1.00  --clause_weak_htbl                      true
% 3.72/1.00  --gc_record_bc_elim                     false
% 3.72/1.00  
% 3.72/1.00  ------ Preprocessing Options
% 3.72/1.00  
% 3.72/1.00  --preprocessing_flag                    true
% 3.72/1.00  --time_out_prep_mult                    0.1
% 3.72/1.00  --splitting_mode                        input
% 3.72/1.00  --splitting_grd                         true
% 3.72/1.00  --splitting_cvd                         false
% 3.72/1.00  --splitting_cvd_svl                     false
% 3.72/1.00  --splitting_nvd                         32
% 3.72/1.00  --sub_typing                            true
% 3.72/1.00  --prep_gs_sim                           false
% 3.72/1.00  --prep_unflatten                        true
% 3.72/1.00  --prep_res_sim                          true
% 3.72/1.00  --prep_upred                            true
% 3.72/1.00  --prep_sem_filter                       exhaustive
% 3.72/1.00  --prep_sem_filter_out                   false
% 3.72/1.00  --pred_elim                             false
% 3.72/1.00  --res_sim_input                         true
% 3.72/1.00  --eq_ax_congr_red                       true
% 3.72/1.00  --pure_diseq_elim                       true
% 3.72/1.00  --brand_transform                       false
% 3.72/1.00  --non_eq_to_eq                          false
% 3.72/1.00  --prep_def_merge                        true
% 3.72/1.00  --prep_def_merge_prop_impl              false
% 3.72/1.00  --prep_def_merge_mbd                    true
% 3.72/1.00  --prep_def_merge_tr_red                 false
% 3.72/1.00  --prep_def_merge_tr_cl                  false
% 3.72/1.00  --smt_preprocessing                     true
% 3.72/1.00  --smt_ac_axioms                         fast
% 3.72/1.00  --preprocessed_out                      false
% 3.72/1.00  --preprocessed_stats                    false
% 3.72/1.00  
% 3.72/1.00  ------ Abstraction refinement Options
% 3.72/1.00  
% 3.72/1.00  --abstr_ref                             []
% 3.72/1.00  --abstr_ref_prep                        false
% 3.72/1.00  --abstr_ref_until_sat                   false
% 3.72/1.00  --abstr_ref_sig_restrict                funpre
% 3.72/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.72/1.00  --abstr_ref_under                       []
% 3.72/1.00  
% 3.72/1.00  ------ SAT Options
% 3.72/1.00  
% 3.72/1.00  --sat_mode                              false
% 3.72/1.00  --sat_fm_restart_options                ""
% 3.72/1.00  --sat_gr_def                            false
% 3.72/1.00  --sat_epr_types                         true
% 3.72/1.00  --sat_non_cyclic_types                  false
% 3.72/1.00  --sat_finite_models                     false
% 3.72/1.00  --sat_fm_lemmas                         false
% 3.72/1.00  --sat_fm_prep                           false
% 3.72/1.00  --sat_fm_uc_incr                        true
% 3.72/1.00  --sat_out_model                         small
% 3.72/1.00  --sat_out_clauses                       false
% 3.72/1.00  
% 3.72/1.00  ------ QBF Options
% 3.72/1.00  
% 3.72/1.00  --qbf_mode                              false
% 3.72/1.00  --qbf_elim_univ                         false
% 3.72/1.00  --qbf_dom_inst                          none
% 3.72/1.00  --qbf_dom_pre_inst                      false
% 3.72/1.00  --qbf_sk_in                             false
% 3.72/1.00  --qbf_pred_elim                         true
% 3.72/1.00  --qbf_split                             512
% 3.72/1.00  
% 3.72/1.00  ------ BMC1 Options
% 3.72/1.00  
% 3.72/1.00  --bmc1_incremental                      false
% 3.72/1.00  --bmc1_axioms                           reachable_all
% 3.72/1.00  --bmc1_min_bound                        0
% 3.72/1.00  --bmc1_max_bound                        -1
% 3.72/1.00  --bmc1_max_bound_default                -1
% 3.72/1.00  --bmc1_symbol_reachability              true
% 3.72/1.00  --bmc1_property_lemmas                  false
% 3.72/1.00  --bmc1_k_induction                      false
% 3.72/1.00  --bmc1_non_equiv_states                 false
% 3.72/1.00  --bmc1_deadlock                         false
% 3.72/1.00  --bmc1_ucm                              false
% 3.72/1.00  --bmc1_add_unsat_core                   none
% 3.72/1.00  --bmc1_unsat_core_children              false
% 3.72/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.72/1.00  --bmc1_out_stat                         full
% 3.72/1.00  --bmc1_ground_init                      false
% 3.72/1.00  --bmc1_pre_inst_next_state              false
% 3.72/1.00  --bmc1_pre_inst_state                   false
% 3.72/1.00  --bmc1_pre_inst_reach_state             false
% 3.72/1.00  --bmc1_out_unsat_core                   false
% 3.72/1.00  --bmc1_aig_witness_out                  false
% 3.72/1.00  --bmc1_verbose                          false
% 3.72/1.00  --bmc1_dump_clauses_tptp                false
% 3.72/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.72/1.00  --bmc1_dump_file                        -
% 3.72/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.72/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.72/1.00  --bmc1_ucm_extend_mode                  1
% 3.72/1.00  --bmc1_ucm_init_mode                    2
% 3.72/1.00  --bmc1_ucm_cone_mode                    none
% 3.72/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.72/1.00  --bmc1_ucm_relax_model                  4
% 3.72/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.72/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.72/1.00  --bmc1_ucm_layered_model                none
% 3.72/1.00  --bmc1_ucm_max_lemma_size               10
% 3.72/1.00  
% 3.72/1.00  ------ AIG Options
% 3.72/1.00  
% 3.72/1.00  --aig_mode                              false
% 3.72/1.00  
% 3.72/1.00  ------ Instantiation Options
% 3.72/1.00  
% 3.72/1.00  --instantiation_flag                    true
% 3.72/1.00  --inst_sos_flag                         false
% 3.72/1.00  --inst_sos_phase                        true
% 3.72/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.72/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.72/1.00  --inst_lit_sel_side                     num_symb
% 3.72/1.00  --inst_solver_per_active                1400
% 3.72/1.00  --inst_solver_calls_frac                1.
% 3.72/1.00  --inst_passive_queue_type               priority_queues
% 3.72/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.72/1.00  --inst_passive_queues_freq              [25;2]
% 3.72/1.00  --inst_dismatching                      true
% 3.72/1.00  --inst_eager_unprocessed_to_passive     true
% 3.72/1.00  --inst_prop_sim_given                   true
% 3.72/1.00  --inst_prop_sim_new                     false
% 3.72/1.00  --inst_subs_new                         false
% 3.72/1.00  --inst_eq_res_simp                      false
% 3.72/1.00  --inst_subs_given                       false
% 3.72/1.00  --inst_orphan_elimination               true
% 3.72/1.00  --inst_learning_loop_flag               true
% 3.72/1.00  --inst_learning_start                   3000
% 3.72/1.00  --inst_learning_factor                  2
% 3.72/1.00  --inst_start_prop_sim_after_learn       3
% 3.72/1.00  --inst_sel_renew                        solver
% 3.72/1.00  --inst_lit_activity_flag                true
% 3.72/1.00  --inst_restr_to_given                   false
% 3.72/1.00  --inst_activity_threshold               500
% 3.72/1.00  --inst_out_proof                        true
% 3.72/1.00  
% 3.72/1.00  ------ Resolution Options
% 3.72/1.00  
% 3.72/1.00  --resolution_flag                       true
% 3.72/1.00  --res_lit_sel                           adaptive
% 3.72/1.00  --res_lit_sel_side                      none
% 3.72/1.00  --res_ordering                          kbo
% 3.72/1.00  --res_to_prop_solver                    active
% 3.72/1.00  --res_prop_simpl_new                    false
% 3.72/1.00  --res_prop_simpl_given                  true
% 3.72/1.00  --res_passive_queue_type                priority_queues
% 3.72/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.72/1.00  --res_passive_queues_freq               [15;5]
% 3.72/1.00  --res_forward_subs                      full
% 3.72/1.00  --res_backward_subs                     full
% 3.72/1.00  --res_forward_subs_resolution           true
% 3.72/1.00  --res_backward_subs_resolution          true
% 3.72/1.00  --res_orphan_elimination                true
% 3.72/1.00  --res_time_limit                        2.
% 3.72/1.00  --res_out_proof                         true
% 3.72/1.00  
% 3.72/1.00  ------ Superposition Options
% 3.72/1.00  
% 3.72/1.00  --superposition_flag                    true
% 3.72/1.00  --sup_passive_queue_type                priority_queues
% 3.72/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.72/1.00  --sup_passive_queues_freq               [1;4]
% 3.72/1.00  --demod_completeness_check              fast
% 3.72/1.00  --demod_use_ground                      true
% 3.72/1.00  --sup_to_prop_solver                    passive
% 3.72/1.00  --sup_prop_simpl_new                    true
% 3.72/1.00  --sup_prop_simpl_given                  true
% 3.72/1.00  --sup_fun_splitting                     false
% 3.72/1.00  --sup_smt_interval                      50000
% 3.72/1.00  
% 3.72/1.00  ------ Superposition Simplification Setup
% 3.72/1.00  
% 3.72/1.00  --sup_indices_passive                   []
% 3.72/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.72/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.72/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.00  --sup_full_bw                           [BwDemod]
% 3.72/1.00  --sup_immed_triv                        [TrivRules]
% 3.72/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.72/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.00  --sup_immed_bw_main                     []
% 3.72/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.72/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.72/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.72/1.00  
% 3.72/1.00  ------ Combination Options
% 3.72/1.00  
% 3.72/1.00  --comb_res_mult                         3
% 3.72/1.00  --comb_sup_mult                         2
% 3.72/1.00  --comb_inst_mult                        10
% 3.72/1.00  
% 3.72/1.00  ------ Debug Options
% 3.72/1.00  
% 3.72/1.00  --dbg_backtrace                         false
% 3.72/1.00  --dbg_dump_prop_clauses                 false
% 3.72/1.00  --dbg_dump_prop_clauses_file            -
% 3.72/1.00  --dbg_out_stat                          false
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  ------ Proving...
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  % SZS status Theorem for theBenchmark.p
% 3.72/1.00  
% 3.72/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.72/1.00  
% 3.72/1.00  fof(f10,conjecture,(
% 3.72/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f11,negated_conjecture,(
% 3.72/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.72/1.00    inference(negated_conjecture,[],[f10])).
% 3.72/1.00  
% 3.72/1.00  fof(f14,plain,(
% 3.72/1.00    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.72/1.00    inference(pure_predicate_removal,[],[f11])).
% 3.72/1.00  
% 3.72/1.00  fof(f15,plain,(
% 3.72/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.72/1.00    inference(pure_predicate_removal,[],[f14])).
% 3.72/1.00  
% 3.72/1.00  fof(f25,plain,(
% 3.72/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 3.72/1.00    inference(ennf_transformation,[],[f15])).
% 3.72/1.00  
% 3.72/1.00  fof(f26,plain,(
% 3.72/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 3.72/1.00    inference(flattening,[],[f25])).
% 3.72/1.00  
% 3.72/1.00  fof(f38,plain,(
% 3.72/1.00    ( ! [X2,X0,X1] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) => ((r1_tsep_1(sK5,X2) | r1_tsep_1(X2,sK5)) & (~r1_tsep_1(sK5,X1) | ~r1_tsep_1(X1,sK5)) & m1_pre_topc(X1,X2) & m1_pre_topc(sK5,X0))) )),
% 3.72/1.00    introduced(choice_axiom,[])).
% 3.72/1.00  
% 3.72/1.00  fof(f37,plain,(
% 3.72/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) => (? [X3] : ((r1_tsep_1(X3,sK4) | r1_tsep_1(sK4,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,sK4) & m1_pre_topc(X3,X0)) & m1_pre_topc(sK4,X0))) )),
% 3.72/1.00    introduced(choice_axiom,[])).
% 3.72/1.00  
% 3.72/1.00  fof(f36,plain,(
% 3.72/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) => (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK3) | ~r1_tsep_1(sK3,X3)) & m1_pre_topc(sK3,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(sK3,X0))) )),
% 3.72/1.00    introduced(choice_axiom,[])).
% 3.72/1.00  
% 3.72/1.00  fof(f35,plain,(
% 3.72/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK2)) & m1_pre_topc(X2,sK2)) & m1_pre_topc(X1,sK2)) & l1_pre_topc(sK2))),
% 3.72/1.00    introduced(choice_axiom,[])).
% 3.72/1.00  
% 3.72/1.00  fof(f39,plain,(
% 3.72/1.00    ((((r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5)) & (~r1_tsep_1(sK5,sK3) | ~r1_tsep_1(sK3,sK5)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK5,sK2)) & m1_pre_topc(sK4,sK2)) & m1_pre_topc(sK3,sK2)) & l1_pre_topc(sK2)),
% 3.72/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f38,f37,f36,f35])).
% 3.72/1.00  
% 3.72/1.00  fof(f61,plain,(
% 3.72/1.00    m1_pre_topc(sK3,sK4)),
% 3.72/1.00    inference(cnf_transformation,[],[f39])).
% 3.72/1.00  
% 3.72/1.00  fof(f9,axiom,(
% 3.72/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f24,plain,(
% 3.72/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.72/1.00    inference(ennf_transformation,[],[f9])).
% 3.72/1.00  
% 3.72/1.00  fof(f56,plain,(
% 3.72/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f24])).
% 3.72/1.00  
% 3.72/1.00  fof(f4,axiom,(
% 3.72/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f13,plain,(
% 3.72/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.72/1.00    inference(unused_predicate_definition_removal,[],[f4])).
% 3.72/1.00  
% 3.72/1.00  fof(f18,plain,(
% 3.72/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.72/1.00    inference(ennf_transformation,[],[f13])).
% 3.72/1.00  
% 3.72/1.00  fof(f50,plain,(
% 3.72/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.72/1.00    inference(cnf_transformation,[],[f18])).
% 3.72/1.00  
% 3.72/1.00  fof(f3,axiom,(
% 3.72/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f17,plain,(
% 3.72/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.72/1.00    inference(ennf_transformation,[],[f3])).
% 3.72/1.00  
% 3.72/1.00  fof(f49,plain,(
% 3.72/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f17])).
% 3.72/1.00  
% 3.72/1.00  fof(f57,plain,(
% 3.72/1.00    l1_pre_topc(sK2)),
% 3.72/1.00    inference(cnf_transformation,[],[f39])).
% 3.72/1.00  
% 3.72/1.00  fof(f6,axiom,(
% 3.72/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f20,plain,(
% 3.72/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.72/1.00    inference(ennf_transformation,[],[f6])).
% 3.72/1.00  
% 3.72/1.00  fof(f52,plain,(
% 3.72/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f20])).
% 3.72/1.00  
% 3.72/1.00  fof(f59,plain,(
% 3.72/1.00    m1_pre_topc(sK4,sK2)),
% 3.72/1.00    inference(cnf_transformation,[],[f39])).
% 3.72/1.00  
% 3.72/1.00  fof(f2,axiom,(
% 3.72/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f12,plain,(
% 3.72/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.72/1.00    inference(rectify,[],[f2])).
% 3.72/1.00  
% 3.72/1.00  fof(f16,plain,(
% 3.72/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.72/1.00    inference(ennf_transformation,[],[f12])).
% 3.72/1.00  
% 3.72/1.00  fof(f32,plain,(
% 3.72/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.72/1.00    introduced(choice_axiom,[])).
% 3.72/1.00  
% 3.72/1.00  fof(f33,plain,(
% 3.72/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.72/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f32])).
% 3.72/1.00  
% 3.72/1.00  fof(f47,plain,(
% 3.72/1.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f33])).
% 3.72/1.00  
% 3.72/1.00  fof(f1,axiom,(
% 3.72/1.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f27,plain,(
% 3.72/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.72/1.00    inference(nnf_transformation,[],[f1])).
% 3.72/1.00  
% 3.72/1.00  fof(f28,plain,(
% 3.72/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.72/1.00    inference(flattening,[],[f27])).
% 3.72/1.00  
% 3.72/1.00  fof(f29,plain,(
% 3.72/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.72/1.00    inference(rectify,[],[f28])).
% 3.72/1.00  
% 3.72/1.00  fof(f30,plain,(
% 3.72/1.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.72/1.00    introduced(choice_axiom,[])).
% 3.72/1.00  
% 3.72/1.00  fof(f31,plain,(
% 3.72/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.72/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 3.72/1.00  
% 3.72/1.00  fof(f41,plain,(
% 3.72/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.72/1.00    inference(cnf_transformation,[],[f31])).
% 3.72/1.00  
% 3.72/1.00  fof(f65,plain,(
% 3.72/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.72/1.00    inference(equality_resolution,[],[f41])).
% 3.72/1.00  
% 3.72/1.00  fof(f46,plain,(
% 3.72/1.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f33])).
% 3.72/1.00  
% 3.72/1.00  fof(f7,axiom,(
% 3.72/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f21,plain,(
% 3.72/1.00    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.72/1.00    inference(ennf_transformation,[],[f7])).
% 3.72/1.00  
% 3.72/1.00  fof(f34,plain,(
% 3.72/1.00    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.72/1.00    inference(nnf_transformation,[],[f21])).
% 3.72/1.00  
% 3.72/1.00  fof(f53,plain,(
% 3.72/1.00    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f34])).
% 3.72/1.00  
% 3.72/1.00  fof(f48,plain,(
% 3.72/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f33])).
% 3.72/1.00  
% 3.72/1.00  fof(f8,axiom,(
% 3.72/1.00    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f22,plain,(
% 3.72/1.00    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 3.72/1.00    inference(ennf_transformation,[],[f8])).
% 3.72/1.00  
% 3.72/1.00  fof(f23,plain,(
% 3.72/1.00    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 3.72/1.00    inference(flattening,[],[f22])).
% 3.72/1.00  
% 3.72/1.00  fof(f55,plain,(
% 3.72/1.00    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f23])).
% 3.72/1.00  
% 3.72/1.00  fof(f54,plain,(
% 3.72/1.00    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f34])).
% 3.72/1.00  
% 3.72/1.00  fof(f63,plain,(
% 3.72/1.00    r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5)),
% 3.72/1.00    inference(cnf_transformation,[],[f39])).
% 3.72/1.00  
% 3.72/1.00  fof(f60,plain,(
% 3.72/1.00    m1_pre_topc(sK5,sK2)),
% 3.72/1.00    inference(cnf_transformation,[],[f39])).
% 3.72/1.00  
% 3.72/1.00  fof(f5,axiom,(
% 3.72/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f19,plain,(
% 3.72/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.72/1.00    inference(ennf_transformation,[],[f5])).
% 3.72/1.00  
% 3.72/1.00  fof(f51,plain,(
% 3.72/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f19])).
% 3.72/1.00  
% 3.72/1.00  fof(f62,plain,(
% 3.72/1.00    ~r1_tsep_1(sK5,sK3) | ~r1_tsep_1(sK3,sK5)),
% 3.72/1.00    inference(cnf_transformation,[],[f39])).
% 3.72/1.00  
% 3.72/1.00  cnf(c_19,negated_conjecture,
% 3.72/1.00      ( m1_pre_topc(sK3,sK4) ),
% 3.72/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_636,plain,
% 3.72/1.00      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_16,plain,
% 3.72/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.72/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.72/1.00      | ~ l1_pre_topc(X1) ),
% 3.72/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_639,plain,
% 3.72/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.72/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.72/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_10,plain,
% 3.72/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.72/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_645,plain,
% 3.72/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.72/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1240,plain,
% 3.72/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.72/1.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.72/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_639,c_645]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_9,plain,
% 3.72/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.72/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_646,plain,
% 3.72/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_2225,plain,
% 3.72/1.00      ( k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(X0)
% 3.72/1.00      | m1_pre_topc(X0,X1) != iProver_top
% 3.72/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_1240,c_646]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_3272,plain,
% 3.72/1.00      ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(sK3)
% 3.72/1.00      | l1_pre_topc(sK4) != iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_636,c_2225]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_23,negated_conjecture,
% 3.72/1.00      ( l1_pre_topc(sK2) ),
% 3.72/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_12,plain,
% 3.72/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.72/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_21,negated_conjecture,
% 3.72/1.00      ( m1_pre_topc(sK4,sK2) ),
% 3.72/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_936,plain,
% 3.72/1.00      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK4) ),
% 3.72/1.00      inference(resolution,[status(thm)],[c_12,c_21]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1393,plain,
% 3.72/1.00      ( ~ m1_pre_topc(sK3,sK4)
% 3.72/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.72/1.00      | ~ l1_pre_topc(sK4) ),
% 3.72/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1424,plain,
% 3.72/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.72/1.00      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 3.72/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1766,plain,
% 3.72/1.00      ( ~ r1_tarski(u1_struct_0(sK3),X0)
% 3.72/1.00      | k3_xboole_0(u1_struct_0(sK3),X0) = u1_struct_0(sK3) ),
% 3.72/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_2995,plain,
% 3.72/1.00      ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
% 3.72/1.00      | k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(sK3) ),
% 3.72/1.00      inference(instantiation,[status(thm)],[c_1766]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_3463,plain,
% 3.72/1.00      ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(sK3) ),
% 3.72/1.00      inference(global_propositional_subsumption,
% 3.72/1.00                [status(thm)],
% 3.72/1.00                [c_3272,c_23,c_19,c_936,c_1393,c_1424,c_2995]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_7,plain,
% 3.72/1.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 3.72/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_648,plain,
% 3.72/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 3.72/1.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_4,plain,
% 3.72/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.72/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_651,plain,
% 3.72/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.72/1.00      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1435,plain,
% 3.72/1.00      ( r1_xboole_0(X0,k3_xboole_0(X1,X2)) = iProver_top
% 3.72/1.00      | r2_hidden(sK1(X0,k3_xboole_0(X1,X2)),X2) = iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_648,c_651]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_3470,plain,
% 3.72/1.00      ( r1_xboole_0(X0,k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))) = iProver_top
% 3.72/1.00      | r2_hidden(sK1(X0,u1_struct_0(sK3)),u1_struct_0(sK4)) = iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_3463,c_1435]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_3478,plain,
% 3.72/1.00      ( r1_xboole_0(X0,u1_struct_0(sK3)) = iProver_top
% 3.72/1.00      | r2_hidden(sK1(X0,u1_struct_0(sK3)),u1_struct_0(sK4)) = iProver_top ),
% 3.72/1.00      inference(light_normalisation,[status(thm)],[c_3470,c_3463]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_8,plain,
% 3.72/1.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.72/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_647,plain,
% 3.72/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 3.72/1.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_14,plain,
% 3.72/1.00      ( ~ r1_tsep_1(X0,X1)
% 3.72/1.00      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 3.72/1.00      | ~ l1_struct_0(X1)
% 3.72/1.00      | ~ l1_struct_0(X0) ),
% 3.72/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_641,plain,
% 3.72/1.00      ( r1_tsep_1(X0,X1) != iProver_top
% 3.72/1.00      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.72/1.00      | l1_struct_0(X1) != iProver_top
% 3.72/1.00      | l1_struct_0(X0) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_6,plain,
% 3.72/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 3.72/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_649,plain,
% 3.72/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 3.72/1.00      | r2_hidden(X2,X1) != iProver_top
% 3.72/1.00      | r2_hidden(X2,X0) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1936,plain,
% 3.72/1.00      ( r1_tsep_1(X0,X1) != iProver_top
% 3.72/1.00      | r2_hidden(X2,u1_struct_0(X1)) != iProver_top
% 3.72/1.00      | r2_hidden(X2,u1_struct_0(X0)) != iProver_top
% 3.72/1.00      | l1_struct_0(X1) != iProver_top
% 3.72/1.00      | l1_struct_0(X0) != iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_641,c_649]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_2781,plain,
% 3.72/1.00      ( r1_tsep_1(X0,X1) != iProver_top
% 3.72/1.00      | r1_xboole_0(u1_struct_0(X1),X2) = iProver_top
% 3.72/1.00      | r2_hidden(sK1(u1_struct_0(X1),X2),u1_struct_0(X0)) != iProver_top
% 3.72/1.00      | l1_struct_0(X1) != iProver_top
% 3.72/1.00      | l1_struct_0(X0) != iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_647,c_1936]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_12987,plain,
% 3.72/1.00      ( r1_tsep_1(sK4,X0) != iProver_top
% 3.72/1.00      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
% 3.72/1.00      | l1_struct_0(X0) != iProver_top
% 3.72/1.00      | l1_struct_0(sK4) != iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_3478,c_2781]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_13027,plain,
% 3.72/1.00      ( r1_tsep_1(sK4,sK5) != iProver_top
% 3.72/1.00      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top
% 3.72/1.00      | l1_struct_0(sK4) != iProver_top
% 3.72/1.00      | l1_struct_0(sK5) != iProver_top ),
% 3.72/1.00      inference(instantiation,[status(thm)],[c_12987]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_15,plain,
% 3.72/1.00      ( ~ r1_tsep_1(X0,X1)
% 3.72/1.00      | r1_tsep_1(X1,X0)
% 3.72/1.00      | ~ l1_struct_0(X1)
% 3.72/1.00      | ~ l1_struct_0(X0) ),
% 3.72/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_2955,plain,
% 3.72/1.00      ( r1_tsep_1(sK3,sK5)
% 3.72/1.00      | ~ r1_tsep_1(sK5,sK3)
% 3.72/1.00      | ~ l1_struct_0(sK3)
% 3.72/1.00      | ~ l1_struct_0(sK5) ),
% 3.72/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_2956,plain,
% 3.72/1.00      ( r1_tsep_1(sK3,sK5) = iProver_top
% 3.72/1.00      | r1_tsep_1(sK5,sK3) != iProver_top
% 3.72/1.00      | l1_struct_0(sK3) != iProver_top
% 3.72/1.00      | l1_struct_0(sK5) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_2955]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_13,plain,
% 3.72/1.00      ( r1_tsep_1(X0,X1)
% 3.72/1.00      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
% 3.72/1.00      | ~ l1_struct_0(X1)
% 3.72/1.00      | ~ l1_struct_0(X0) ),
% 3.72/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1928,plain,
% 3.72/1.00      ( r1_tsep_1(sK5,sK3)
% 3.72/1.00      | ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
% 3.72/1.00      | ~ l1_struct_0(sK3)
% 3.72/1.00      | ~ l1_struct_0(sK5) ),
% 3.72/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1929,plain,
% 3.72/1.00      ( r1_tsep_1(sK5,sK3) = iProver_top
% 3.72/1.00      | r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 3.72/1.00      | l1_struct_0(sK3) != iProver_top
% 3.72/1.00      | l1_struct_0(sK5) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_1928]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_17,negated_conjecture,
% 3.72/1.00      ( r1_tsep_1(sK4,sK5) | r1_tsep_1(sK5,sK4) ),
% 3.72/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1473,plain,
% 3.72/1.00      ( r1_tsep_1(sK5,sK4) | ~ l1_struct_0(sK4) | ~ l1_struct_0(sK5) ),
% 3.72/1.00      inference(resolution,[status(thm)],[c_15,c_17]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_20,negated_conjecture,
% 3.72/1.00      ( m1_pre_topc(sK5,sK2) ),
% 3.72/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_11,plain,
% 3.72/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.72/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_43,plain,
% 3.72/1.00      ( ~ l1_pre_topc(sK5) | l1_struct_0(sK5) ),
% 3.72/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_839,plain,
% 3.72/1.00      ( ~ m1_pre_topc(X0,sK2) | l1_pre_topc(X0) | ~ l1_pre_topc(sK2) ),
% 3.72/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_841,plain,
% 3.72/1.00      ( ~ m1_pre_topc(sK5,sK2) | ~ l1_pre_topc(sK2) | l1_pre_topc(sK5) ),
% 3.72/1.00      inference(instantiation,[status(thm)],[c_839]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1056,plain,
% 3.72/1.00      ( l1_pre_topc(sK4) ),
% 3.72/1.00      inference(global_propositional_subsumption,
% 3.72/1.00                [status(thm)],
% 3.72/1.00                [c_936,c_23]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1271,plain,
% 3.72/1.00      ( l1_struct_0(sK4) ),
% 3.72/1.00      inference(resolution,[status(thm)],[c_1056,c_11]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_638,plain,
% 3.72/1.00      ( r1_tsep_1(sK4,sK5) = iProver_top
% 3.72/1.00      | r1_tsep_1(sK5,sK4) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_640,plain,
% 3.72/1.00      ( r1_tsep_1(X0,X1) != iProver_top
% 3.72/1.00      | r1_tsep_1(X1,X0) = iProver_top
% 3.72/1.00      | l1_struct_0(X1) != iProver_top
% 3.72/1.00      | l1_struct_0(X0) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1452,plain,
% 3.72/1.00      ( r1_tsep_1(sK5,sK4) = iProver_top
% 3.72/1.00      | l1_struct_0(sK4) != iProver_top
% 3.72/1.00      | l1_struct_0(sK5) != iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_638,c_640]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1453,plain,
% 3.72/1.00      ( r1_tsep_1(sK5,sK4) | ~ l1_struct_0(sK4) | ~ l1_struct_0(sK5) ),
% 3.72/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1452]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1476,plain,
% 3.72/1.00      ( r1_tsep_1(sK5,sK4) ),
% 3.72/1.00      inference(global_propositional_subsumption,
% 3.72/1.00                [status(thm)],
% 3.72/1.00                [c_1473,c_23,c_20,c_43,c_841,c_1271,c_1453]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1606,plain,
% 3.72/1.00      ( r1_tsep_1(sK4,sK5) | ~ l1_struct_0(sK4) | ~ l1_struct_0(sK5) ),
% 3.72/1.00      inference(resolution,[status(thm)],[c_1476,c_15]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1607,plain,
% 3.72/1.00      ( r1_tsep_1(sK4,sK5) = iProver_top
% 3.72/1.00      | l1_struct_0(sK4) != iProver_top
% 3.72/1.00      | l1_struct_0(sK5) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_1606]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1272,plain,
% 3.72/1.00      ( l1_struct_0(sK4) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_1271]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_932,plain,
% 3.72/1.00      ( l1_pre_topc(sK3) | ~ l1_pre_topc(sK4) ),
% 3.72/1.00      inference(resolution,[status(thm)],[c_12,c_19]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_941,plain,
% 3.72/1.00      ( l1_pre_topc(sK3) ),
% 3.72/1.00      inference(global_propositional_subsumption,
% 3.72/1.00                [status(thm)],
% 3.72/1.00                [c_932,c_23,c_936]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_953,plain,
% 3.72/1.00      ( l1_struct_0(sK3) ),
% 3.72/1.00      inference(resolution,[status(thm)],[c_941,c_11]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_954,plain,
% 3.72/1.00      ( l1_struct_0(sK3) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_953]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_840,plain,
% 3.72/1.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 3.72/1.00      | l1_pre_topc(X0) = iProver_top
% 3.72/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_839]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_842,plain,
% 3.72/1.00      ( m1_pre_topc(sK5,sK2) != iProver_top
% 3.72/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.72/1.00      | l1_pre_topc(sK5) = iProver_top ),
% 3.72/1.00      inference(instantiation,[status(thm)],[c_840]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_42,plain,
% 3.72/1.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_44,plain,
% 3.72/1.00      ( l1_pre_topc(sK5) != iProver_top
% 3.72/1.00      | l1_struct_0(sK5) = iProver_top ),
% 3.72/1.00      inference(instantiation,[status(thm)],[c_42]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_18,negated_conjecture,
% 3.72/1.00      ( ~ r1_tsep_1(sK3,sK5) | ~ r1_tsep_1(sK5,sK3) ),
% 3.72/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_29,plain,
% 3.72/1.00      ( r1_tsep_1(sK3,sK5) != iProver_top
% 3.72/1.00      | r1_tsep_1(sK5,sK3) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_27,plain,
% 3.72/1.00      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_24,plain,
% 3.72/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(contradiction,plain,
% 3.72/1.00      ( $false ),
% 3.72/1.00      inference(minisat,
% 3.72/1.00                [status(thm)],
% 3.72/1.00                [c_13027,c_2956,c_1929,c_1607,c_1272,c_954,c_842,c_44,
% 3.72/1.00                 c_29,c_27,c_24]) ).
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.72/1.00  
% 3.72/1.00  ------                               Statistics
% 3.72/1.00  
% 3.72/1.00  ------ Selected
% 3.72/1.00  
% 3.72/1.00  total_time:                             0.401
% 3.72/1.00  
%------------------------------------------------------------------------------
