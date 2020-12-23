%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:31 EST 2020

% Result     : Theorem 12.12s
% Output     : CNFRefutation 12.12s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 187 expanded)
%              Number of clauses        :   54 (  56 expanded)
%              Number of leaves         :   15 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  419 ( 918 expanded)
%              Number of equality atoms :   35 (  44 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v4_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK2(X0,X1),X0)
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v2_tops_2(X1,X0)
               => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v2_tops_2(X1,X0)
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK5),X0)
        & v2_tops_2(X1,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK4,X2),X0)
            & v2_tops_2(sK4,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v2_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),X1,X2),sK3)
              & v2_tops_2(X1,sK3)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) )
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3)
    & v2_tops_2(sK4,sK3)
    & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    & l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f18,f35,f34,f33])).

fof(f55,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v4_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    v2_tops_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8940,plain,
    ( ~ r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK3))),X1)
    | r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK3))),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_23312,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))),X0)
    | ~ r2_hidden(sK0(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))),sK5)
    | ~ r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_8940])).

cnf(c_58675,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK0(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))),sK5)
    | ~ r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_23312])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3542,plain,
    ( r2_hidden(sK0(k3_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK3))),X1)
    | ~ r2_hidden(sK0(k3_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK3))),k3_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_9409,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))),k3_xboole_0(sK4,sK5))
    | r2_hidden(sK0(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))),sK5) ),
    inference(instantiation,[status(thm)],[c_3542])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4139,plain,
    ( ~ r2_hidden(sK2(sK3,k3_xboole_0(sK4,sK5)),k3_xboole_0(sK4,sK5))
    | r2_hidden(sK2(sK3,k3_xboole_0(sK4,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1536,plain,
    ( r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK3))),X0)
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2911,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))),k3_xboole_0(sK4,sK5))
    | r1_tarski(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1536])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1537,plain,
    ( ~ r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2913,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1537])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1437,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2141,plain,
    ( m1_subset_1(k3_xboole_0(sK4,sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r1_tarski(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1437])).

cnf(c_15,plain,
    ( v2_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(sK2(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_370,plain,
    ( v2_tops_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(sK2(X1,X0),X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_371,plain,
    ( v2_tops_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | r2_hidden(sK2(sK3,X0),X0) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_1886,plain,
    ( v2_tops_2(k3_xboole_0(sK4,sK5),sK3)
    | ~ m1_subset_1(k3_xboole_0(sK4,sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | r2_hidden(sK2(sK3,k3_xboole_0(sK4,sK5)),k3_xboole_0(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_14,plain,
    ( ~ v4_pre_topc(sK2(X0,X1),X0)
    | v2_tops_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_17,plain,
    ( v4_pre_topc(X0,X1)
    | ~ v2_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(X0,X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_304,plain,
    ( ~ v2_tops_2(X0,X1)
    | v2_tops_2(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(X4,X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | sK2(X3,X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_305,plain,
    ( ~ v2_tops_2(X0,X1)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(sK2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK2(X1,X2),X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_321,plain,
    ( ~ v2_tops_2(X0,X1)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(sK2(X1,X2),X0)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_305,c_13])).

cnf(c_336,plain,
    ( ~ v2_tops_2(X0,X1)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r2_hidden(sK2(X1,X2),X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_321,c_22])).

cnf(c_337,plain,
    ( ~ v2_tops_2(X0,sK3)
    | v2_tops_2(X1,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r2_hidden(sK2(sK3,X1),X0) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_1432,plain,
    ( v2_tops_2(X0,sK3)
    | ~ v2_tops_2(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r2_hidden(sK2(sK3,X0),sK4) ),
    inference(instantiation,[status(thm)],[c_337])).

cnf(c_1887,plain,
    ( v2_tops_2(k3_xboole_0(sK4,sK5),sK3)
    | ~ v2_tops_2(sK4,sK3)
    | ~ m1_subset_1(k3_xboole_0(sK4,sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r2_hidden(sK2(sK3,k3_xboole_0(sK4,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_175,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_176,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_175])).

cnf(c_222,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_176])).

cnf(c_1783,plain,
    ( ~ r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5) = k3_xboole_0(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_801,plain,
    ( ~ v2_tops_2(X0,X1)
    | v2_tops_2(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1681,plain,
    ( ~ v2_tops_2(X0,X1)
    | v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3)
    | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5) != X0
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_1782,plain,
    ( v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3)
    | ~ v2_tops_2(k3_xboole_0(sK4,sK5),X0)
    | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5) != k3_xboole_0(sK4,sK5)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1681])).

cnf(c_1785,plain,
    ( v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3)
    | ~ v2_tops_2(k3_xboole_0(sK4,sK5),sK3)
    | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5) != k3_xboole_0(sK4,sK5)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1782])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1270,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1274,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1653,plain,
    ( r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1270,c_1274])).

cnf(c_1666,plain,
    ( r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1653])).

cnf(c_795,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_812,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_18,negated_conjecture,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,negated_conjecture,
    ( v2_tops_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f56])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_58675,c_9409,c_4139,c_2911,c_2913,c_2141,c_1886,c_1887,c_1783,c_1785,c_1666,c_812,c_18,c_19,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:07:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 12.12/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.12/1.98  
% 12.12/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.12/1.98  
% 12.12/1.98  ------  iProver source info
% 12.12/1.98  
% 12.12/1.98  git: date: 2020-06-30 10:37:57 +0100
% 12.12/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.12/1.98  git: non_committed_changes: false
% 12.12/1.98  git: last_make_outside_of_git: false
% 12.12/1.98  
% 12.12/1.98  ------ 
% 12.12/1.98  
% 12.12/1.98  ------ Input Options
% 12.12/1.98  
% 12.12/1.98  --out_options                           all
% 12.12/1.98  --tptp_safe_out                         true
% 12.12/1.98  --problem_path                          ""
% 12.12/1.98  --include_path                          ""
% 12.12/1.98  --clausifier                            res/vclausify_rel
% 12.12/1.98  --clausifier_options                    --mode clausify
% 12.12/1.98  --stdin                                 false
% 12.12/1.98  --stats_out                             all
% 12.12/1.98  
% 12.12/1.98  ------ General Options
% 12.12/1.98  
% 12.12/1.98  --fof                                   false
% 12.12/1.98  --time_out_real                         305.
% 12.12/1.98  --time_out_virtual                      -1.
% 12.12/1.98  --symbol_type_check                     false
% 12.12/1.98  --clausify_out                          false
% 12.12/1.98  --sig_cnt_out                           false
% 12.12/1.98  --trig_cnt_out                          false
% 12.12/1.98  --trig_cnt_out_tolerance                1.
% 12.12/1.98  --trig_cnt_out_sk_spl                   false
% 12.12/1.98  --abstr_cl_out                          false
% 12.12/1.98  
% 12.12/1.98  ------ Global Options
% 12.12/1.98  
% 12.12/1.98  --schedule                              default
% 12.12/1.98  --add_important_lit                     false
% 12.12/1.98  --prop_solver_per_cl                    1000
% 12.12/1.98  --min_unsat_core                        false
% 12.12/1.98  --soft_assumptions                      false
% 12.12/1.98  --soft_lemma_size                       3
% 12.12/1.98  --prop_impl_unit_size                   0
% 12.12/1.98  --prop_impl_unit                        []
% 12.12/1.98  --share_sel_clauses                     true
% 12.12/1.98  --reset_solvers                         false
% 12.12/1.98  --bc_imp_inh                            [conj_cone]
% 12.12/1.98  --conj_cone_tolerance                   3.
% 12.12/1.98  --extra_neg_conj                        none
% 12.12/1.98  --large_theory_mode                     true
% 12.12/1.98  --prolific_symb_bound                   200
% 12.12/1.98  --lt_threshold                          2000
% 12.12/1.98  --clause_weak_htbl                      true
% 12.12/1.98  --gc_record_bc_elim                     false
% 12.12/1.98  
% 12.12/1.98  ------ Preprocessing Options
% 12.12/1.98  
% 12.12/1.98  --preprocessing_flag                    true
% 12.12/1.98  --time_out_prep_mult                    0.1
% 12.12/1.98  --splitting_mode                        input
% 12.12/1.98  --splitting_grd                         true
% 12.12/1.98  --splitting_cvd                         false
% 12.12/1.98  --splitting_cvd_svl                     false
% 12.12/1.98  --splitting_nvd                         32
% 12.12/1.98  --sub_typing                            true
% 12.12/1.98  --prep_gs_sim                           true
% 12.12/1.98  --prep_unflatten                        true
% 12.12/1.98  --prep_res_sim                          true
% 12.12/1.98  --prep_upred                            true
% 12.12/1.98  --prep_sem_filter                       exhaustive
% 12.12/1.98  --prep_sem_filter_out                   false
% 12.12/1.98  --pred_elim                             true
% 12.12/1.98  --res_sim_input                         true
% 12.12/1.98  --eq_ax_congr_red                       true
% 12.12/1.98  --pure_diseq_elim                       true
% 12.12/1.98  --brand_transform                       false
% 12.12/1.98  --non_eq_to_eq                          false
% 12.12/1.98  --prep_def_merge                        true
% 12.12/1.98  --prep_def_merge_prop_impl              false
% 12.12/1.98  --prep_def_merge_mbd                    true
% 12.12/1.98  --prep_def_merge_tr_red                 false
% 12.12/1.98  --prep_def_merge_tr_cl                  false
% 12.12/1.98  --smt_preprocessing                     true
% 12.12/1.98  --smt_ac_axioms                         fast
% 12.12/1.98  --preprocessed_out                      false
% 12.12/1.98  --preprocessed_stats                    false
% 12.12/1.98  
% 12.12/1.98  ------ Abstraction refinement Options
% 12.12/1.98  
% 12.12/1.98  --abstr_ref                             []
% 12.12/1.98  --abstr_ref_prep                        false
% 12.12/1.98  --abstr_ref_until_sat                   false
% 12.12/1.98  --abstr_ref_sig_restrict                funpre
% 12.12/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 12.12/1.98  --abstr_ref_under                       []
% 12.12/1.98  
% 12.12/1.98  ------ SAT Options
% 12.12/1.98  
% 12.12/1.98  --sat_mode                              false
% 12.12/1.98  --sat_fm_restart_options                ""
% 12.12/1.98  --sat_gr_def                            false
% 12.12/1.98  --sat_epr_types                         true
% 12.12/1.98  --sat_non_cyclic_types                  false
% 12.12/1.98  --sat_finite_models                     false
% 12.12/1.98  --sat_fm_lemmas                         false
% 12.12/1.98  --sat_fm_prep                           false
% 12.12/1.98  --sat_fm_uc_incr                        true
% 12.12/1.98  --sat_out_model                         small
% 12.12/1.98  --sat_out_clauses                       false
% 12.12/1.98  
% 12.12/1.98  ------ QBF Options
% 12.12/1.98  
% 12.12/1.98  --qbf_mode                              false
% 12.12/1.98  --qbf_elim_univ                         false
% 12.12/1.98  --qbf_dom_inst                          none
% 12.12/1.98  --qbf_dom_pre_inst                      false
% 12.12/1.98  --qbf_sk_in                             false
% 12.12/1.98  --qbf_pred_elim                         true
% 12.12/1.98  --qbf_split                             512
% 12.12/1.98  
% 12.12/1.98  ------ BMC1 Options
% 12.12/1.98  
% 12.12/1.98  --bmc1_incremental                      false
% 12.12/1.98  --bmc1_axioms                           reachable_all
% 12.12/1.98  --bmc1_min_bound                        0
% 12.12/1.98  --bmc1_max_bound                        -1
% 12.12/1.98  --bmc1_max_bound_default                -1
% 12.12/1.98  --bmc1_symbol_reachability              true
% 12.12/1.98  --bmc1_property_lemmas                  false
% 12.12/1.98  --bmc1_k_induction                      false
% 12.12/1.98  --bmc1_non_equiv_states                 false
% 12.12/1.98  --bmc1_deadlock                         false
% 12.12/1.98  --bmc1_ucm                              false
% 12.12/1.98  --bmc1_add_unsat_core                   none
% 12.12/1.98  --bmc1_unsat_core_children              false
% 12.12/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 12.12/1.98  --bmc1_out_stat                         full
% 12.12/1.98  --bmc1_ground_init                      false
% 12.12/1.98  --bmc1_pre_inst_next_state              false
% 12.12/1.98  --bmc1_pre_inst_state                   false
% 12.12/1.98  --bmc1_pre_inst_reach_state             false
% 12.12/1.98  --bmc1_out_unsat_core                   false
% 12.12/1.98  --bmc1_aig_witness_out                  false
% 12.12/1.98  --bmc1_verbose                          false
% 12.12/1.98  --bmc1_dump_clauses_tptp                false
% 12.12/1.98  --bmc1_dump_unsat_core_tptp             false
% 12.12/1.98  --bmc1_dump_file                        -
% 12.12/1.98  --bmc1_ucm_expand_uc_limit              128
% 12.12/1.98  --bmc1_ucm_n_expand_iterations          6
% 12.12/1.98  --bmc1_ucm_extend_mode                  1
% 12.12/1.98  --bmc1_ucm_init_mode                    2
% 12.12/1.98  --bmc1_ucm_cone_mode                    none
% 12.12/1.98  --bmc1_ucm_reduced_relation_type        0
% 12.12/1.98  --bmc1_ucm_relax_model                  4
% 12.12/1.98  --bmc1_ucm_full_tr_after_sat            true
% 12.12/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 12.12/1.98  --bmc1_ucm_layered_model                none
% 12.12/1.98  --bmc1_ucm_max_lemma_size               10
% 12.12/1.98  
% 12.12/1.98  ------ AIG Options
% 12.12/1.98  
% 12.12/1.98  --aig_mode                              false
% 12.12/1.98  
% 12.12/1.98  ------ Instantiation Options
% 12.12/1.98  
% 12.12/1.98  --instantiation_flag                    true
% 12.12/1.98  --inst_sos_flag                         false
% 12.12/1.98  --inst_sos_phase                        true
% 12.12/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.12/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.12/1.98  --inst_lit_sel_side                     num_symb
% 12.12/1.98  --inst_solver_per_active                1400
% 12.12/1.98  --inst_solver_calls_frac                1.
% 12.12/1.98  --inst_passive_queue_type               priority_queues
% 12.12/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.12/1.98  --inst_passive_queues_freq              [25;2]
% 12.12/1.98  --inst_dismatching                      true
% 12.12/1.98  --inst_eager_unprocessed_to_passive     true
% 12.12/1.98  --inst_prop_sim_given                   true
% 12.12/1.98  --inst_prop_sim_new                     false
% 12.12/1.98  --inst_subs_new                         false
% 12.12/1.98  --inst_eq_res_simp                      false
% 12.12/1.98  --inst_subs_given                       false
% 12.12/1.98  --inst_orphan_elimination               true
% 12.12/1.98  --inst_learning_loop_flag               true
% 12.12/1.98  --inst_learning_start                   3000
% 12.12/1.98  --inst_learning_factor                  2
% 12.12/1.98  --inst_start_prop_sim_after_learn       3
% 12.12/1.98  --inst_sel_renew                        solver
% 12.12/1.98  --inst_lit_activity_flag                true
% 12.12/1.98  --inst_restr_to_given                   false
% 12.12/1.98  --inst_activity_threshold               500
% 12.12/1.98  --inst_out_proof                        true
% 12.12/1.98  
% 12.12/1.98  ------ Resolution Options
% 12.12/1.98  
% 12.12/1.98  --resolution_flag                       true
% 12.12/1.98  --res_lit_sel                           adaptive
% 12.12/1.98  --res_lit_sel_side                      none
% 12.12/1.98  --res_ordering                          kbo
% 12.12/1.98  --res_to_prop_solver                    active
% 12.12/1.98  --res_prop_simpl_new                    false
% 12.12/1.98  --res_prop_simpl_given                  true
% 12.12/1.98  --res_passive_queue_type                priority_queues
% 12.12/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.12/1.98  --res_passive_queues_freq               [15;5]
% 12.12/1.98  --res_forward_subs                      full
% 12.12/1.98  --res_backward_subs                     full
% 12.12/1.98  --res_forward_subs_resolution           true
% 12.12/1.98  --res_backward_subs_resolution          true
% 12.12/1.98  --res_orphan_elimination                true
% 12.12/1.98  --res_time_limit                        2.
% 12.12/1.98  --res_out_proof                         true
% 12.12/1.98  
% 12.12/1.98  ------ Superposition Options
% 12.12/1.98  
% 12.12/1.98  --superposition_flag                    true
% 12.12/1.98  --sup_passive_queue_type                priority_queues
% 12.12/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.12/1.98  --sup_passive_queues_freq               [8;1;4]
% 12.12/1.98  --demod_completeness_check              fast
% 12.12/1.98  --demod_use_ground                      true
% 12.12/1.98  --sup_to_prop_solver                    passive
% 12.12/1.98  --sup_prop_simpl_new                    true
% 12.12/1.98  --sup_prop_simpl_given                  true
% 12.12/1.98  --sup_fun_splitting                     false
% 12.12/1.98  --sup_smt_interval                      50000
% 12.12/1.98  
% 12.12/1.98  ------ Superposition Simplification Setup
% 12.12/1.98  
% 12.12/1.98  --sup_indices_passive                   []
% 12.12/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.12/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.12/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.12/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 12.12/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.12/1.98  --sup_full_bw                           [BwDemod]
% 12.12/1.98  --sup_immed_triv                        [TrivRules]
% 12.12/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.12/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.12/1.98  --sup_immed_bw_main                     []
% 12.12/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.12/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 12.12/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.12/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.12/1.98  
% 12.12/1.98  ------ Combination Options
% 12.12/1.98  
% 12.12/1.98  --comb_res_mult                         3
% 12.12/1.98  --comb_sup_mult                         2
% 12.12/1.98  --comb_inst_mult                        10
% 12.12/1.98  
% 12.12/1.98  ------ Debug Options
% 12.12/1.98  
% 12.12/1.98  --dbg_backtrace                         false
% 12.12/1.98  --dbg_dump_prop_clauses                 false
% 12.12/1.98  --dbg_dump_prop_clauses_file            -
% 12.12/1.98  --dbg_out_stat                          false
% 12.12/1.98  ------ Parsing...
% 12.12/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.12/1.98  
% 12.12/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 12.12/1.98  
% 12.12/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.12/1.98  
% 12.12/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.12/1.98  ------ Proving...
% 12.12/1.98  ------ Problem Properties 
% 12.12/1.98  
% 12.12/1.98  
% 12.12/1.98  clauses                                 20
% 12.12/1.98  conjectures                             4
% 12.12/1.98  EPR                                     2
% 12.12/1.98  Horn                                    15
% 12.12/1.98  unary                                   4
% 12.12/1.98  binary                                  7
% 12.12/1.98  lits                                    48
% 12.12/1.98  lits eq                                 4
% 12.12/1.98  fd_pure                                 0
% 12.12/1.98  fd_pseudo                               0
% 12.12/1.98  fd_cond                                 0
% 12.12/1.98  fd_pseudo_cond                          3
% 12.12/1.98  AC symbols                              0
% 12.12/1.98  
% 12.12/1.98  ------ Schedule dynamic 5 is on 
% 12.12/1.98  
% 12.12/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 12.12/1.98  
% 12.12/1.98  
% 12.12/1.98  ------ 
% 12.12/1.98  Current options:
% 12.12/1.98  ------ 
% 12.12/1.98  
% 12.12/1.98  ------ Input Options
% 12.12/1.98  
% 12.12/1.98  --out_options                           all
% 12.12/1.98  --tptp_safe_out                         true
% 12.12/1.98  --problem_path                          ""
% 12.12/1.98  --include_path                          ""
% 12.12/1.98  --clausifier                            res/vclausify_rel
% 12.12/1.98  --clausifier_options                    --mode clausify
% 12.12/1.98  --stdin                                 false
% 12.12/1.98  --stats_out                             all
% 12.12/1.98  
% 12.12/1.98  ------ General Options
% 12.12/1.98  
% 12.12/1.98  --fof                                   false
% 12.12/1.98  --time_out_real                         305.
% 12.12/1.98  --time_out_virtual                      -1.
% 12.12/1.98  --symbol_type_check                     false
% 12.12/1.98  --clausify_out                          false
% 12.12/1.98  --sig_cnt_out                           false
% 12.12/1.98  --trig_cnt_out                          false
% 12.12/1.98  --trig_cnt_out_tolerance                1.
% 12.12/1.98  --trig_cnt_out_sk_spl                   false
% 12.12/1.98  --abstr_cl_out                          false
% 12.12/1.98  
% 12.12/1.98  ------ Global Options
% 12.12/1.98  
% 12.12/1.98  --schedule                              default
% 12.12/1.98  --add_important_lit                     false
% 12.12/1.98  --prop_solver_per_cl                    1000
% 12.12/1.98  --min_unsat_core                        false
% 12.12/1.98  --soft_assumptions                      false
% 12.12/1.98  --soft_lemma_size                       3
% 12.12/1.98  --prop_impl_unit_size                   0
% 12.12/1.98  --prop_impl_unit                        []
% 12.12/1.98  --share_sel_clauses                     true
% 12.12/1.98  --reset_solvers                         false
% 12.12/1.98  --bc_imp_inh                            [conj_cone]
% 12.12/1.98  --conj_cone_tolerance                   3.
% 12.12/1.98  --extra_neg_conj                        none
% 12.12/1.98  --large_theory_mode                     true
% 12.12/1.98  --prolific_symb_bound                   200
% 12.12/1.98  --lt_threshold                          2000
% 12.12/1.98  --clause_weak_htbl                      true
% 12.12/1.98  --gc_record_bc_elim                     false
% 12.12/1.98  
% 12.12/1.98  ------ Preprocessing Options
% 12.12/1.98  
% 12.12/1.98  --preprocessing_flag                    true
% 12.12/1.98  --time_out_prep_mult                    0.1
% 12.12/1.98  --splitting_mode                        input
% 12.12/1.98  --splitting_grd                         true
% 12.12/1.98  --splitting_cvd                         false
% 12.12/1.98  --splitting_cvd_svl                     false
% 12.12/1.98  --splitting_nvd                         32
% 12.12/1.98  --sub_typing                            true
% 12.12/1.98  --prep_gs_sim                           true
% 12.12/1.98  --prep_unflatten                        true
% 12.12/1.98  --prep_res_sim                          true
% 12.12/1.98  --prep_upred                            true
% 12.12/1.98  --prep_sem_filter                       exhaustive
% 12.12/1.98  --prep_sem_filter_out                   false
% 12.12/1.98  --pred_elim                             true
% 12.12/1.98  --res_sim_input                         true
% 12.12/1.98  --eq_ax_congr_red                       true
% 12.12/1.98  --pure_diseq_elim                       true
% 12.12/1.98  --brand_transform                       false
% 12.12/1.98  --non_eq_to_eq                          false
% 12.12/1.98  --prep_def_merge                        true
% 12.12/1.98  --prep_def_merge_prop_impl              false
% 12.12/1.98  --prep_def_merge_mbd                    true
% 12.12/1.98  --prep_def_merge_tr_red                 false
% 12.12/1.98  --prep_def_merge_tr_cl                  false
% 12.12/1.98  --smt_preprocessing                     true
% 12.12/1.98  --smt_ac_axioms                         fast
% 12.12/1.98  --preprocessed_out                      false
% 12.12/1.98  --preprocessed_stats                    false
% 12.12/1.98  
% 12.12/1.98  ------ Abstraction refinement Options
% 12.12/1.98  
% 12.12/1.98  --abstr_ref                             []
% 12.12/1.98  --abstr_ref_prep                        false
% 12.12/1.98  --abstr_ref_until_sat                   false
% 12.12/1.98  --abstr_ref_sig_restrict                funpre
% 12.12/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 12.12/1.98  --abstr_ref_under                       []
% 12.12/1.98  
% 12.12/1.98  ------ SAT Options
% 12.12/1.98  
% 12.12/1.98  --sat_mode                              false
% 12.12/1.98  --sat_fm_restart_options                ""
% 12.12/1.98  --sat_gr_def                            false
% 12.12/1.98  --sat_epr_types                         true
% 12.12/1.98  --sat_non_cyclic_types                  false
% 12.12/1.98  --sat_finite_models                     false
% 12.12/1.98  --sat_fm_lemmas                         false
% 12.12/1.98  --sat_fm_prep                           false
% 12.12/1.98  --sat_fm_uc_incr                        true
% 12.12/1.98  --sat_out_model                         small
% 12.12/1.98  --sat_out_clauses                       false
% 12.12/1.98  
% 12.12/1.98  ------ QBF Options
% 12.12/1.98  
% 12.12/1.98  --qbf_mode                              false
% 12.12/1.98  --qbf_elim_univ                         false
% 12.12/1.98  --qbf_dom_inst                          none
% 12.12/1.98  --qbf_dom_pre_inst                      false
% 12.12/1.98  --qbf_sk_in                             false
% 12.12/1.98  --qbf_pred_elim                         true
% 12.12/1.98  --qbf_split                             512
% 12.12/1.98  
% 12.12/1.98  ------ BMC1 Options
% 12.12/1.98  
% 12.12/1.98  --bmc1_incremental                      false
% 12.12/1.98  --bmc1_axioms                           reachable_all
% 12.12/1.98  --bmc1_min_bound                        0
% 12.12/1.98  --bmc1_max_bound                        -1
% 12.12/1.98  --bmc1_max_bound_default                -1
% 12.12/1.98  --bmc1_symbol_reachability              true
% 12.12/1.99  --bmc1_property_lemmas                  false
% 12.12/1.99  --bmc1_k_induction                      false
% 12.12/1.99  --bmc1_non_equiv_states                 false
% 12.12/1.99  --bmc1_deadlock                         false
% 12.12/1.99  --bmc1_ucm                              false
% 12.12/1.99  --bmc1_add_unsat_core                   none
% 12.12/1.99  --bmc1_unsat_core_children              false
% 12.12/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 12.12/1.99  --bmc1_out_stat                         full
% 12.12/1.99  --bmc1_ground_init                      false
% 12.12/1.99  --bmc1_pre_inst_next_state              false
% 12.12/1.99  --bmc1_pre_inst_state                   false
% 12.12/1.99  --bmc1_pre_inst_reach_state             false
% 12.12/1.99  --bmc1_out_unsat_core                   false
% 12.12/1.99  --bmc1_aig_witness_out                  false
% 12.12/1.99  --bmc1_verbose                          false
% 12.12/1.99  --bmc1_dump_clauses_tptp                false
% 12.12/1.99  --bmc1_dump_unsat_core_tptp             false
% 12.12/1.99  --bmc1_dump_file                        -
% 12.12/1.99  --bmc1_ucm_expand_uc_limit              128
% 12.12/1.99  --bmc1_ucm_n_expand_iterations          6
% 12.12/1.99  --bmc1_ucm_extend_mode                  1
% 12.12/1.99  --bmc1_ucm_init_mode                    2
% 12.12/1.99  --bmc1_ucm_cone_mode                    none
% 12.12/1.99  --bmc1_ucm_reduced_relation_type        0
% 12.12/1.99  --bmc1_ucm_relax_model                  4
% 12.12/1.99  --bmc1_ucm_full_tr_after_sat            true
% 12.12/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 12.12/1.99  --bmc1_ucm_layered_model                none
% 12.12/1.99  --bmc1_ucm_max_lemma_size               10
% 12.12/1.99  
% 12.12/1.99  ------ AIG Options
% 12.12/1.99  
% 12.12/1.99  --aig_mode                              false
% 12.12/1.99  
% 12.12/1.99  ------ Instantiation Options
% 12.12/1.99  
% 12.12/1.99  --instantiation_flag                    true
% 12.12/1.99  --inst_sos_flag                         false
% 12.12/1.99  --inst_sos_phase                        true
% 12.12/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.12/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.12/1.99  --inst_lit_sel_side                     none
% 12.12/1.99  --inst_solver_per_active                1400
% 12.12/1.99  --inst_solver_calls_frac                1.
% 12.12/1.99  --inst_passive_queue_type               priority_queues
% 12.12/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.12/1.99  --inst_passive_queues_freq              [25;2]
% 12.12/1.99  --inst_dismatching                      true
% 12.12/1.99  --inst_eager_unprocessed_to_passive     true
% 12.12/1.99  --inst_prop_sim_given                   true
% 12.12/1.99  --inst_prop_sim_new                     false
% 12.12/1.99  --inst_subs_new                         false
% 12.12/1.99  --inst_eq_res_simp                      false
% 12.12/1.99  --inst_subs_given                       false
% 12.12/1.99  --inst_orphan_elimination               true
% 12.12/1.99  --inst_learning_loop_flag               true
% 12.12/1.99  --inst_learning_start                   3000
% 12.12/1.99  --inst_learning_factor                  2
% 12.12/1.99  --inst_start_prop_sim_after_learn       3
% 12.12/1.99  --inst_sel_renew                        solver
% 12.12/1.99  --inst_lit_activity_flag                true
% 12.12/1.99  --inst_restr_to_given                   false
% 12.12/1.99  --inst_activity_threshold               500
% 12.12/1.99  --inst_out_proof                        true
% 12.12/1.99  
% 12.12/1.99  ------ Resolution Options
% 12.12/1.99  
% 12.12/1.99  --resolution_flag                       false
% 12.12/1.99  --res_lit_sel                           adaptive
% 12.12/1.99  --res_lit_sel_side                      none
% 12.12/1.99  --res_ordering                          kbo
% 12.12/1.99  --res_to_prop_solver                    active
% 12.12/1.99  --res_prop_simpl_new                    false
% 12.12/1.99  --res_prop_simpl_given                  true
% 12.12/1.99  --res_passive_queue_type                priority_queues
% 12.12/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.12/1.99  --res_passive_queues_freq               [15;5]
% 12.12/1.99  --res_forward_subs                      full
% 12.12/1.99  --res_backward_subs                     full
% 12.12/1.99  --res_forward_subs_resolution           true
% 12.12/1.99  --res_backward_subs_resolution          true
% 12.12/1.99  --res_orphan_elimination                true
% 12.12/1.99  --res_time_limit                        2.
% 12.12/1.99  --res_out_proof                         true
% 12.12/1.99  
% 12.12/1.99  ------ Superposition Options
% 12.12/1.99  
% 12.12/1.99  --superposition_flag                    true
% 12.12/1.99  --sup_passive_queue_type                priority_queues
% 12.12/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.12/1.99  --sup_passive_queues_freq               [8;1;4]
% 12.12/1.99  --demod_completeness_check              fast
% 12.12/1.99  --demod_use_ground                      true
% 12.12/1.99  --sup_to_prop_solver                    passive
% 12.12/1.99  --sup_prop_simpl_new                    true
% 12.12/1.99  --sup_prop_simpl_given                  true
% 12.12/1.99  --sup_fun_splitting                     false
% 12.12/1.99  --sup_smt_interval                      50000
% 12.12/1.99  
% 12.12/1.99  ------ Superposition Simplification Setup
% 12.12/1.99  
% 12.12/1.99  --sup_indices_passive                   []
% 12.12/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.12/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.12/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 12.12/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 12.12/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.12/1.99  --sup_full_bw                           [BwDemod]
% 12.12/1.99  --sup_immed_triv                        [TrivRules]
% 12.12/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.12/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.12/1.99  --sup_immed_bw_main                     []
% 12.12/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.12/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 12.12/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 12.12/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 12.12/1.99  
% 12.12/1.99  ------ Combination Options
% 12.12/1.99  
% 12.12/1.99  --comb_res_mult                         3
% 12.12/1.99  --comb_sup_mult                         2
% 12.12/1.99  --comb_inst_mult                        10
% 12.12/1.99  
% 12.12/1.99  ------ Debug Options
% 12.12/1.99  
% 12.12/1.99  --dbg_backtrace                         false
% 12.12/1.99  --dbg_dump_prop_clauses                 false
% 12.12/1.99  --dbg_dump_prop_clauses_file            -
% 12.12/1.99  --dbg_out_stat                          false
% 12.12/1.99  
% 12.12/1.99  
% 12.12/1.99  
% 12.12/1.99  
% 12.12/1.99  ------ Proving...
% 12.12/1.99  
% 12.12/1.99  
% 12.12/1.99  % SZS status Theorem for theBenchmark.p
% 12.12/1.99  
% 12.12/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 12.12/1.99  
% 12.12/1.99  fof(f1,axiom,(
% 12.12/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 12.12/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.12/1.99  
% 12.12/1.99  fof(f10,plain,(
% 12.12/1.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 12.12/1.99    inference(ennf_transformation,[],[f1])).
% 12.12/1.99  
% 12.12/1.99  fof(f19,plain,(
% 12.12/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 12.12/1.99    inference(nnf_transformation,[],[f10])).
% 12.12/1.99  
% 12.12/1.99  fof(f20,plain,(
% 12.12/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.12/1.99    inference(rectify,[],[f19])).
% 12.12/1.99  
% 12.12/1.99  fof(f21,plain,(
% 12.12/1.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 12.12/1.99    introduced(choice_axiom,[])).
% 12.12/1.99  
% 12.12/1.99  fof(f22,plain,(
% 12.12/1.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.12/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 12.12/1.99  
% 12.12/1.99  fof(f37,plain,(
% 12.12/1.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 12.12/1.99    inference(cnf_transformation,[],[f22])).
% 12.12/1.99  
% 12.12/1.99  fof(f2,axiom,(
% 12.12/1.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 12.12/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.12/1.99  
% 12.12/1.99  fof(f23,plain,(
% 12.12/1.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 12.12/1.99    inference(nnf_transformation,[],[f2])).
% 12.12/1.99  
% 12.12/1.99  fof(f24,plain,(
% 12.12/1.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 12.12/1.99    inference(flattening,[],[f23])).
% 12.12/1.99  
% 12.12/1.99  fof(f25,plain,(
% 12.12/1.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 12.12/1.99    inference(rectify,[],[f24])).
% 12.12/1.99  
% 12.12/1.99  fof(f26,plain,(
% 12.12/1.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 12.12/1.99    introduced(choice_axiom,[])).
% 12.12/1.99  
% 12.12/1.99  fof(f27,plain,(
% 12.12/1.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 12.12/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 12.12/1.99  
% 12.12/1.99  fof(f41,plain,(
% 12.12/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 12.12/1.99    inference(cnf_transformation,[],[f27])).
% 12.12/1.99  
% 12.12/1.99  fof(f61,plain,(
% 12.12/1.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 12.12/1.99    inference(equality_resolution,[],[f41])).
% 12.12/1.99  
% 12.12/1.99  fof(f40,plain,(
% 12.12/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 12.12/1.99    inference(cnf_transformation,[],[f27])).
% 12.12/1.99  
% 12.12/1.99  fof(f62,plain,(
% 12.12/1.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 12.12/1.99    inference(equality_resolution,[],[f40])).
% 12.12/1.99  
% 12.12/1.99  fof(f38,plain,(
% 12.12/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 12.12/1.99    inference(cnf_transformation,[],[f22])).
% 12.12/1.99  
% 12.12/1.99  fof(f39,plain,(
% 12.12/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 12.12/1.99    inference(cnf_transformation,[],[f22])).
% 12.12/1.99  
% 12.12/1.99  fof(f5,axiom,(
% 12.12/1.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 12.12/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.12/1.99  
% 12.12/1.99  fof(f28,plain,(
% 12.12/1.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 12.12/1.99    inference(nnf_transformation,[],[f5])).
% 12.12/1.99  
% 12.12/1.99  fof(f49,plain,(
% 12.12/1.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 12.12/1.99    inference(cnf_transformation,[],[f28])).
% 12.12/1.99  
% 12.12/1.99  fof(f7,axiom,(
% 12.12/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))))))),
% 12.12/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.12/1.99  
% 12.12/1.99  fof(f15,plain,(
% 12.12/1.99    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : ((v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 12.12/1.99    inference(ennf_transformation,[],[f7])).
% 12.12/1.99  
% 12.12/1.99  fof(f16,plain,(
% 12.12/1.99    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 12.12/1.99    inference(flattening,[],[f15])).
% 12.12/1.99  
% 12.12/1.99  fof(f29,plain,(
% 12.12/1.99    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 12.12/1.99    inference(nnf_transformation,[],[f16])).
% 12.12/1.99  
% 12.12/1.99  fof(f30,plain,(
% 12.12/1.99    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 12.12/1.99    inference(rectify,[],[f29])).
% 12.12/1.99  
% 12.12/1.99  fof(f31,plain,(
% 12.12/1.99    ! [X1,X0] : (? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 12.12/1.99    introduced(choice_axiom,[])).
% 12.12/1.99  
% 12.12/1.99  fof(f32,plain,(
% 12.12/1.99    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | (~v4_pre_topc(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 12.12/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 12.12/1.99  
% 12.12/1.99  fof(f53,plain,(
% 12.12/1.99    ( ! [X0,X1] : (v2_tops_2(X1,X0) | r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 12.12/1.99    inference(cnf_transformation,[],[f32])).
% 12.12/1.99  
% 12.12/1.99  fof(f8,conjecture,(
% 12.12/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 12.12/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.12/1.99  
% 12.12/1.99  fof(f9,negated_conjecture,(
% 12.12/1.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 12.12/1.99    inference(negated_conjecture,[],[f8])).
% 12.12/1.99  
% 12.12/1.99  fof(f17,plain,(
% 12.12/1.99    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 12.12/1.99    inference(ennf_transformation,[],[f9])).
% 12.12/1.99  
% 12.12/1.99  fof(f18,plain,(
% 12.12/1.99    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 12.12/1.99    inference(flattening,[],[f17])).
% 12.12/1.99  
% 12.12/1.99  fof(f35,plain,(
% 12.12/1.99    ( ! [X0,X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK5),X0) & v2_tops_2(X1,X0) & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 12.12/1.99    introduced(choice_axiom,[])).
% 12.12/1.99  
% 12.12/1.99  fof(f34,plain,(
% 12.12/1.99    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK4,X2),X0) & v2_tops_2(sK4,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 12.12/1.99    introduced(choice_axiom,[])).
% 12.12/1.99  
% 12.12/1.99  fof(f33,plain,(
% 12.12/1.99    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),X1,X2),sK3) & v2_tops_2(X1,sK3) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) & l1_pre_topc(sK3))),
% 12.12/1.99    introduced(choice_axiom,[])).
% 12.12/1.99  
% 12.12/1.99  fof(f36,plain,(
% 12.12/1.99    ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3) & v2_tops_2(sK4,sK3) & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) & l1_pre_topc(sK3)),
% 12.12/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f18,f35,f34,f33])).
% 12.12/1.99  
% 12.12/1.99  fof(f55,plain,(
% 12.12/1.99    l1_pre_topc(sK3)),
% 12.12/1.99    inference(cnf_transformation,[],[f36])).
% 12.12/1.99  
% 12.12/1.99  fof(f54,plain,(
% 12.12/1.99    ( ! [X0,X1] : (v2_tops_2(X1,X0) | ~v4_pre_topc(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 12.12/1.99    inference(cnf_transformation,[],[f32])).
% 12.12/1.99  
% 12.12/1.99  fof(f51,plain,(
% 12.12/1.99    ( ! [X0,X3,X1] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 12.12/1.99    inference(cnf_transformation,[],[f32])).
% 12.12/1.99  
% 12.12/1.99  fof(f6,axiom,(
% 12.12/1.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 12.12/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.12/1.99  
% 12.12/1.99  fof(f13,plain,(
% 12.12/1.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 12.12/1.99    inference(ennf_transformation,[],[f6])).
% 12.12/1.99  
% 12.12/1.99  fof(f14,plain,(
% 12.12/1.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 12.12/1.99    inference(flattening,[],[f13])).
% 12.12/1.99  
% 12.12/1.99  fof(f50,plain,(
% 12.12/1.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 12.12/1.99    inference(cnf_transformation,[],[f14])).
% 12.12/1.99  
% 12.12/1.99  fof(f4,axiom,(
% 12.12/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 12.12/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.12/1.99  
% 12.12/1.99  fof(f12,plain,(
% 12.12/1.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 12.12/1.99    inference(ennf_transformation,[],[f4])).
% 12.12/1.99  
% 12.12/1.99  fof(f47,plain,(
% 12.12/1.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 12.12/1.99    inference(cnf_transformation,[],[f12])).
% 12.12/1.99  
% 12.12/1.99  fof(f57,plain,(
% 12.12/1.99    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))),
% 12.12/1.99    inference(cnf_transformation,[],[f36])).
% 12.12/1.99  
% 12.12/1.99  fof(f48,plain,(
% 12.12/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 12.12/1.99    inference(cnf_transformation,[],[f28])).
% 12.12/1.99  
% 12.12/1.99  fof(f59,plain,(
% 12.12/1.99    ~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3)),
% 12.12/1.99    inference(cnf_transformation,[],[f36])).
% 12.12/1.99  
% 12.12/1.99  fof(f58,plain,(
% 12.12/1.99    v2_tops_2(sK4,sK3)),
% 12.12/1.99    inference(cnf_transformation,[],[f36])).
% 12.12/1.99  
% 12.12/1.99  fof(f56,plain,(
% 12.12/1.99    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))),
% 12.12/1.99    inference(cnf_transformation,[],[f36])).
% 12.12/1.99  
% 12.12/1.99  cnf(c_2,plain,
% 12.12/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 12.12/1.99      inference(cnf_transformation,[],[f37]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_8940,plain,
% 12.12/1.99      ( ~ r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK3))),X1)
% 12.12/1.99      | r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK3))),X2)
% 12.12/1.99      | ~ r1_tarski(X1,X2) ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_23312,plain,
% 12.12/1.99      ( r2_hidden(sK0(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))),X0)
% 12.12/1.99      | ~ r2_hidden(sK0(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))),sK5)
% 12.12/1.99      | ~ r1_tarski(sK5,X0) ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_8940]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_58675,plain,
% 12.12/1.99      ( r2_hidden(sK0(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
% 12.12/1.99      | ~ r2_hidden(sK0(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))),sK5)
% 12.12/1.99      | ~ r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_23312]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_7,plain,
% 12.12/1.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 12.12/1.99      inference(cnf_transformation,[],[f61]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_3542,plain,
% 12.12/1.99      ( r2_hidden(sK0(k3_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK3))),X1)
% 12.12/1.99      | ~ r2_hidden(sK0(k3_xboole_0(X0,X1),k1_zfmisc_1(u1_struct_0(sK3))),k3_xboole_0(X0,X1)) ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_7]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_9409,plain,
% 12.12/1.99      ( ~ r2_hidden(sK0(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))),k3_xboole_0(sK4,sK5))
% 12.12/1.99      | r2_hidden(sK0(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))),sK5) ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_3542]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_8,plain,
% 12.12/1.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 12.12/1.99      inference(cnf_transformation,[],[f62]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_4139,plain,
% 12.12/1.99      ( ~ r2_hidden(sK2(sK3,k3_xboole_0(sK4,sK5)),k3_xboole_0(sK4,sK5))
% 12.12/1.99      | r2_hidden(sK2(sK3,k3_xboole_0(sK4,sK5)),sK4) ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_8]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_1,plain,
% 12.12/1.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 12.12/1.99      inference(cnf_transformation,[],[f38]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_1536,plain,
% 12.12/1.99      ( r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK3))),X0)
% 12.12/1.99      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_2911,plain,
% 12.12/1.99      ( r2_hidden(sK0(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))),k3_xboole_0(sK4,sK5))
% 12.12/1.99      | r1_tarski(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_1536]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_0,plain,
% 12.12/1.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 12.12/1.99      inference(cnf_transformation,[],[f39]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_1537,plain,
% 12.12/1.99      ( ~ r2_hidden(sK0(X0,k1_zfmisc_1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
% 12.12/1.99      | r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_0]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_2913,plain,
% 12.12/1.99      ( ~ r2_hidden(sK0(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
% 12.12/1.99      | r1_tarski(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_1537]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_11,plain,
% 12.12/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 12.12/1.99      inference(cnf_transformation,[],[f49]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_1437,plain,
% 12.12/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 12.12/1.99      | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_11]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_2141,plain,
% 12.12/1.99      ( m1_subset_1(k3_xboole_0(sK4,sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 12.12/1.99      | ~ r1_tarski(k3_xboole_0(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_1437]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_15,plain,
% 12.12/1.99      ( v2_tops_2(X0,X1)
% 12.12/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 12.12/1.99      | r2_hidden(sK2(X1,X0),X0)
% 12.12/1.99      | ~ l1_pre_topc(X1) ),
% 12.12/1.99      inference(cnf_transformation,[],[f53]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_22,negated_conjecture,
% 12.12/1.99      ( l1_pre_topc(sK3) ),
% 12.12/1.99      inference(cnf_transformation,[],[f55]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_370,plain,
% 12.12/1.99      ( v2_tops_2(X0,X1)
% 12.12/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 12.12/1.99      | r2_hidden(sK2(X1,X0),X0)
% 12.12/1.99      | sK3 != X1 ),
% 12.12/1.99      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_371,plain,
% 12.12/1.99      ( v2_tops_2(X0,sK3)
% 12.12/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 12.12/1.99      | r2_hidden(sK2(sK3,X0),X0) ),
% 12.12/1.99      inference(unflattening,[status(thm)],[c_370]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_1886,plain,
% 12.12/1.99      ( v2_tops_2(k3_xboole_0(sK4,sK5),sK3)
% 12.12/1.99      | ~ m1_subset_1(k3_xboole_0(sK4,sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 12.12/1.99      | r2_hidden(sK2(sK3,k3_xboole_0(sK4,sK5)),k3_xboole_0(sK4,sK5)) ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_371]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_14,plain,
% 12.12/1.99      ( ~ v4_pre_topc(sK2(X0,X1),X0)
% 12.12/1.99      | v2_tops_2(X1,X0)
% 12.12/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 12.12/1.99      | ~ l1_pre_topc(X0) ),
% 12.12/1.99      inference(cnf_transformation,[],[f54]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_17,plain,
% 12.12/1.99      ( v4_pre_topc(X0,X1)
% 12.12/1.99      | ~ v2_tops_2(X2,X1)
% 12.12/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.12/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 12.12/1.99      | ~ r2_hidden(X0,X2)
% 12.12/1.99      | ~ l1_pre_topc(X1) ),
% 12.12/1.99      inference(cnf_transformation,[],[f51]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_304,plain,
% 12.12/1.99      ( ~ v2_tops_2(X0,X1)
% 12.12/1.99      | v2_tops_2(X2,X3)
% 12.12/1.99      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
% 12.12/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
% 12.12/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 12.12/1.99      | ~ r2_hidden(X4,X0)
% 12.12/1.99      | ~ l1_pre_topc(X3)
% 12.12/1.99      | ~ l1_pre_topc(X1)
% 12.12/1.99      | X1 != X3
% 12.12/1.99      | sK2(X3,X2) != X4 ),
% 12.12/1.99      inference(resolution_lifted,[status(thm)],[c_14,c_17]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_305,plain,
% 12.12/1.99      ( ~ v2_tops_2(X0,X1)
% 12.12/1.99      | v2_tops_2(X2,X1)
% 12.12/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 12.12/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 12.12/1.99      | ~ m1_subset_1(sK2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 12.12/1.99      | ~ r2_hidden(sK2(X1,X2),X0)
% 12.12/1.99      | ~ l1_pre_topc(X1) ),
% 12.12/1.99      inference(unflattening,[status(thm)],[c_304]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_13,plain,
% 12.12/1.99      ( m1_subset_1(X0,X1)
% 12.12/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 12.12/1.99      | ~ r2_hidden(X0,X2) ),
% 12.12/1.99      inference(cnf_transformation,[],[f50]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_321,plain,
% 12.12/1.99      ( ~ v2_tops_2(X0,X1)
% 12.12/1.99      | v2_tops_2(X2,X1)
% 12.12/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 12.12/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 12.12/1.99      | ~ r2_hidden(sK2(X1,X2),X0)
% 12.12/1.99      | ~ l1_pre_topc(X1) ),
% 12.12/1.99      inference(forward_subsumption_resolution,
% 12.12/1.99                [status(thm)],
% 12.12/1.99                [c_305,c_13]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_336,plain,
% 12.12/1.99      ( ~ v2_tops_2(X0,X1)
% 12.12/1.99      | v2_tops_2(X2,X1)
% 12.12/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 12.12/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 12.12/1.99      | ~ r2_hidden(sK2(X1,X2),X0)
% 12.12/1.99      | sK3 != X1 ),
% 12.12/1.99      inference(resolution_lifted,[status(thm)],[c_321,c_22]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_337,plain,
% 12.12/1.99      ( ~ v2_tops_2(X0,sK3)
% 12.12/1.99      | v2_tops_2(X1,sK3)
% 12.12/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 12.12/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 12.12/1.99      | ~ r2_hidden(sK2(sK3,X1),X0) ),
% 12.12/1.99      inference(unflattening,[status(thm)],[c_336]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_1432,plain,
% 12.12/1.99      ( v2_tops_2(X0,sK3)
% 12.12/1.99      | ~ v2_tops_2(sK4,sK3)
% 12.12/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 12.12/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 12.12/1.99      | ~ r2_hidden(sK2(sK3,X0),sK4) ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_337]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_1887,plain,
% 12.12/1.99      ( v2_tops_2(k3_xboole_0(sK4,sK5),sK3)
% 12.12/1.99      | ~ v2_tops_2(sK4,sK3)
% 12.12/1.99      | ~ m1_subset_1(k3_xboole_0(sK4,sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 12.12/1.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
% 12.12/1.99      | ~ r2_hidden(sK2(sK3,k3_xboole_0(sK4,sK5)),sK4) ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_1432]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_10,plain,
% 12.12/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 12.12/1.99      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 12.12/1.99      inference(cnf_transformation,[],[f47]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_175,plain,
% 12.12/1.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 12.12/1.99      inference(prop_impl,[status(thm)],[c_11]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_176,plain,
% 12.12/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 12.12/1.99      inference(renaming,[status(thm)],[c_175]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_222,plain,
% 12.12/1.99      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 12.12/1.99      inference(bin_hyper_res,[status(thm)],[c_10,c_176]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_1783,plain,
% 12.12/1.99      ( ~ r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 12.12/1.99      | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5) = k3_xboole_0(sK4,sK5) ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_222]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_801,plain,
% 12.12/1.99      ( ~ v2_tops_2(X0,X1) | v2_tops_2(X2,X3) | X2 != X0 | X3 != X1 ),
% 12.12/1.99      theory(equality) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_1681,plain,
% 12.12/1.99      ( ~ v2_tops_2(X0,X1)
% 12.12/1.99      | v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3)
% 12.12/1.99      | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5) != X0
% 12.12/1.99      | sK3 != X1 ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_801]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_1782,plain,
% 12.12/1.99      ( v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3)
% 12.12/1.99      | ~ v2_tops_2(k3_xboole_0(sK4,sK5),X0)
% 12.12/1.99      | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5) != k3_xboole_0(sK4,sK5)
% 12.12/1.99      | sK3 != X0 ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_1681]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_1785,plain,
% 12.12/1.99      ( v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3)
% 12.12/1.99      | ~ v2_tops_2(k3_xboole_0(sK4,sK5),sK3)
% 12.12/1.99      | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5) != k3_xboole_0(sK4,sK5)
% 12.12/1.99      | sK3 != sK3 ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_1782]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_20,negated_conjecture,
% 12.12/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
% 12.12/1.99      inference(cnf_transformation,[],[f57]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_1270,plain,
% 12.12/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) = iProver_top ),
% 12.12/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_12,plain,
% 12.12/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 12.12/1.99      inference(cnf_transformation,[],[f48]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_1274,plain,
% 12.12/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 12.12/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 12.12/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_1653,plain,
% 12.12/1.99      ( r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 12.12/1.99      inference(superposition,[status(thm)],[c_1270,c_1274]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_1666,plain,
% 12.12/1.99      ( r1_tarski(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 12.12/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_1653]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_795,plain,( X0 = X0 ),theory(equality) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_812,plain,
% 12.12/1.99      ( sK3 = sK3 ),
% 12.12/1.99      inference(instantiation,[status(thm)],[c_795]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_18,negated_conjecture,
% 12.12/1.99      ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK4,sK5),sK3) ),
% 12.12/1.99      inference(cnf_transformation,[],[f59]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_19,negated_conjecture,
% 12.12/1.99      ( v2_tops_2(sK4,sK3) ),
% 12.12/1.99      inference(cnf_transformation,[],[f58]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(c_21,negated_conjecture,
% 12.12/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
% 12.12/1.99      inference(cnf_transformation,[],[f56]) ).
% 12.12/1.99  
% 12.12/1.99  cnf(contradiction,plain,
% 12.12/1.99      ( $false ),
% 12.12/1.99      inference(minisat,
% 12.12/1.99                [status(thm)],
% 12.12/1.99                [c_58675,c_9409,c_4139,c_2911,c_2913,c_2141,c_1886,
% 12.12/1.99                 c_1887,c_1783,c_1785,c_1666,c_812,c_18,c_19,c_21]) ).
% 12.12/1.99  
% 12.12/1.99  
% 12.12/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 12.12/1.99  
% 12.12/1.99  ------                               Statistics
% 12.12/1.99  
% 12.12/1.99  ------ General
% 12.12/1.99  
% 12.12/1.99  abstr_ref_over_cycles:                  0
% 12.12/1.99  abstr_ref_under_cycles:                 0
% 12.12/1.99  gc_basic_clause_elim:                   0
% 12.12/1.99  forced_gc_time:                         0
% 12.12/1.99  parsing_time:                           0.008
% 12.12/1.99  unif_index_cands_time:                  0.
% 12.12/1.99  unif_index_add_time:                    0.
% 12.12/1.99  orderings_time:                         0.
% 12.12/1.99  out_proof_time:                         0.013
% 12.12/1.99  total_time:                             1.433
% 12.12/1.99  num_of_symbols:                         47
% 12.12/1.99  num_of_terms:                           46295
% 12.12/1.99  
% 12.12/1.99  ------ Preprocessing
% 12.12/1.99  
% 12.12/1.99  num_of_splits:                          0
% 12.12/1.99  num_of_split_atoms:                     0
% 12.12/1.99  num_of_reused_defs:                     0
% 12.12/1.99  num_eq_ax_congr_red:                    32
% 12.12/1.99  num_of_sem_filtered_clauses:            1
% 12.12/1.99  num_of_subtypes:                        0
% 12.12/1.99  monotx_restored_types:                  0
% 12.12/1.99  sat_num_of_epr_types:                   0
% 12.12/1.99  sat_num_of_non_cyclic_types:            0
% 12.12/1.99  sat_guarded_non_collapsed_types:        0
% 12.12/1.99  num_pure_diseq_elim:                    0
% 12.12/1.99  simp_replaced_by:                       0
% 12.12/1.99  res_preprocessed:                       101
% 12.12/1.99  prep_upred:                             0
% 12.12/1.99  prep_unflattend:                        17
% 12.12/1.99  smt_new_axioms:                         0
% 12.12/1.99  pred_elim_cands:                        4
% 12.12/1.99  pred_elim:                              2
% 12.12/1.99  pred_elim_cl:                           2
% 12.12/1.99  pred_elim_cycles:                       4
% 12.12/1.99  merged_defs:                            8
% 12.12/1.99  merged_defs_ncl:                        0
% 12.12/1.99  bin_hyper_res:                          10
% 12.12/1.99  prep_cycles:                            4
% 12.12/1.99  pred_elim_time:                         0.005
% 12.12/1.99  splitting_time:                         0.
% 12.12/1.99  sem_filter_time:                        0.
% 12.12/1.99  monotx_time:                            0.
% 12.12/1.99  subtype_inf_time:                       0.
% 12.12/1.99  
% 12.12/1.99  ------ Problem properties
% 12.12/1.99  
% 12.12/1.99  clauses:                                20
% 12.12/1.99  conjectures:                            4
% 12.12/1.99  epr:                                    2
% 12.12/1.99  horn:                                   15
% 12.12/1.99  ground:                                 4
% 12.12/1.99  unary:                                  4
% 12.12/1.99  binary:                                 7
% 12.12/1.99  lits:                                   48
% 12.12/1.99  lits_eq:                                4
% 12.12/1.99  fd_pure:                                0
% 12.12/1.99  fd_pseudo:                              0
% 12.12/1.99  fd_cond:                                0
% 12.12/1.99  fd_pseudo_cond:                         3
% 12.12/1.99  ac_symbols:                             0
% 12.12/1.99  
% 12.12/1.99  ------ Propositional Solver
% 12.12/1.99  
% 12.12/1.99  prop_solver_calls:                      34
% 12.12/1.99  prop_fast_solver_calls:                 2011
% 12.12/1.99  smt_solver_calls:                       0
% 12.12/1.99  smt_fast_solver_calls:                  0
% 12.12/1.99  prop_num_of_clauses:                    17994
% 12.12/1.99  prop_preprocess_simplified:             20457
% 12.12/1.99  prop_fo_subsumed:                       8
% 12.12/1.99  prop_solver_time:                       0.
% 12.12/1.99  smt_solver_time:                        0.
% 12.12/1.99  smt_fast_solver_time:                   0.
% 12.12/1.99  prop_fast_solver_time:                  0.
% 12.12/1.99  prop_unsat_core_time:                   0.005
% 12.12/1.99  
% 12.12/1.99  ------ QBF
% 12.12/1.99  
% 12.12/1.99  qbf_q_res:                              0
% 12.12/1.99  qbf_num_tautologies:                    0
% 12.12/1.99  qbf_prep_cycles:                        0
% 12.12/1.99  
% 12.12/1.99  ------ BMC1
% 12.12/1.99  
% 12.12/1.99  bmc1_current_bound:                     -1
% 12.12/1.99  bmc1_last_solved_bound:                 -1
% 12.12/1.99  bmc1_unsat_core_size:                   -1
% 12.12/1.99  bmc1_unsat_core_parents_size:           -1
% 12.12/1.99  bmc1_merge_next_fun:                    0
% 12.12/1.99  bmc1_unsat_core_clauses_time:           0.
% 12.12/1.99  
% 12.12/1.99  ------ Instantiation
% 12.12/1.99  
% 12.12/1.99  inst_num_of_clauses:                    3703
% 12.12/1.99  inst_num_in_passive:                    409
% 12.12/1.99  inst_num_in_active:                     1773
% 12.12/1.99  inst_num_in_unprocessed:                1520
% 12.12/1.99  inst_num_of_loops:                      2361
% 12.12/1.99  inst_num_of_learning_restarts:          0
% 12.12/1.99  inst_num_moves_active_passive:          579
% 12.12/1.99  inst_lit_activity:                      0
% 12.12/1.99  inst_lit_activity_moves:                0
% 12.12/1.99  inst_num_tautologies:                   0
% 12.12/1.99  inst_num_prop_implied:                  0
% 12.12/1.99  inst_num_existing_simplified:           0
% 12.12/1.99  inst_num_eq_res_simplified:             0
% 12.12/1.99  inst_num_child_elim:                    0
% 12.12/1.99  inst_num_of_dismatching_blockings:      4110
% 12.12/1.99  inst_num_of_non_proper_insts:           5718
% 12.12/1.99  inst_num_of_duplicates:                 0
% 12.12/1.99  inst_inst_num_from_inst_to_res:         0
% 12.12/1.99  inst_dismatching_checking_time:         0.
% 12.12/1.99  
% 12.12/1.99  ------ Resolution
% 12.12/1.99  
% 12.12/1.99  res_num_of_clauses:                     0
% 12.12/1.99  res_num_in_passive:                     0
% 12.12/1.99  res_num_in_active:                      0
% 12.12/1.99  res_num_of_loops:                       105
% 12.12/1.99  res_forward_subset_subsumed:            437
% 12.12/1.99  res_backward_subset_subsumed:           0
% 12.12/1.99  res_forward_subsumed:                   0
% 12.12/1.99  res_backward_subsumed:                  0
% 12.12/1.99  res_forward_subsumption_resolution:     1
% 12.12/1.99  res_backward_subsumption_resolution:    0
% 12.12/1.99  res_clause_to_clause_subsumption:       35955
% 12.12/1.99  res_orphan_elimination:                 0
% 12.12/1.99  res_tautology_del:                      914
% 12.12/1.99  res_num_eq_res_simplified:              0
% 12.12/1.99  res_num_sel_changes:                    0
% 12.12/1.99  res_moves_from_active_to_pass:          0
% 12.12/1.99  
% 12.12/1.99  ------ Superposition
% 12.12/1.99  
% 12.12/1.99  sup_time_total:                         0.
% 12.12/1.99  sup_time_generating:                    0.
% 12.12/1.99  sup_time_sim_full:                      0.
% 12.12/1.99  sup_time_sim_immed:                     0.
% 12.12/1.99  
% 12.12/1.99  sup_num_of_clauses:                     2323
% 12.12/1.99  sup_num_in_active:                      470
% 12.12/1.99  sup_num_in_passive:                     1853
% 12.12/1.99  sup_num_of_loops:                       472
% 12.12/1.99  sup_fw_superposition:                   939
% 12.12/1.99  sup_bw_superposition:                   2214
% 12.12/1.99  sup_immediate_simplified:               239
% 12.12/1.99  sup_given_eliminated:                   0
% 12.12/1.99  comparisons_done:                       0
% 12.12/1.99  comparisons_avoided:                    0
% 12.12/1.99  
% 12.12/1.99  ------ Simplifications
% 12.12/1.99  
% 12.12/1.99  
% 12.12/1.99  sim_fw_subset_subsumed:                 34
% 12.12/1.99  sim_bw_subset_subsumed:                 24
% 12.12/1.99  sim_fw_subsumed:                        108
% 12.12/1.99  sim_bw_subsumed:                        54
% 12.12/1.99  sim_fw_subsumption_res:                 35
% 12.12/1.99  sim_bw_subsumption_res:                 0
% 12.12/1.99  sim_tautology_del:                      90
% 12.12/1.99  sim_eq_tautology_del:                   0
% 12.12/1.99  sim_eq_res_simp:                        11
% 12.12/1.99  sim_fw_demodulated:                     0
% 12.12/1.99  sim_bw_demodulated:                     1
% 12.12/1.99  sim_light_normalised:                   0
% 12.12/1.99  sim_joinable_taut:                      0
% 12.12/1.99  sim_joinable_simp:                      0
% 12.12/1.99  sim_ac_normalised:                      0
% 12.12/1.99  sim_smt_subsumption:                    0
% 12.12/1.99  
%------------------------------------------------------------------------------
