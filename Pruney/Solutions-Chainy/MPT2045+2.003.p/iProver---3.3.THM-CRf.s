%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:03 EST 2020

% Result     : Theorem 12.12s
% Output     : CNFRefutation 12.12s
% Verified   : 
% Statistics : Number of formulae       :  268 ( 872 expanded)
%              Number of clauses        :  173 ( 216 expanded)
%              Number of leaves         :   28 ( 229 expanded)
%              Depth                    :   20
%              Number of atoms          : 1147 (6637 expanded)
%              Number of equality atoms :  103 ( 110 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
     => ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) )
           => r2_hidden(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(flattening,[],[f31])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ? [X2,X3] :
              ( ~ r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) ) )
        & ( ! [X2,X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ r1_tarski(X3,X0)
              | ~ r1_tarski(X2,X3) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ? [X2,X3] :
              ( ~ r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) ) )
        & ( ! [X4,X5] :
              ( r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1)
              | ~ r1_tarski(X5,X0)
              | ~ r1_tarski(X4,X5) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & r1_tarski(X3,X0)
          & r1_tarski(X2,X3) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X1)
        & r1_tarski(sK4(X0,X1),X0)
        & r1_tarski(sK3(X0,X1),sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ( ~ r2_hidden(sK4(X0,X1),X1)
            & r2_hidden(sK3(X0,X1),X1)
            & r1_tarski(sK4(X0,X1),X0)
            & r1_tarski(sK3(X0,X1),sK4(X0,X1)) ) )
        & ( ! [X4,X5] :
              ( r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1)
              | ~ r1_tarski(X5,X0)
              | ~ r1_tarski(X4,X5) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f52,f53])).

fof(f85,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f104,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) ) ),
    inference(definition_unfolding,[],[f85,f79,f79])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X0) )
               => r2_hidden(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X3] :
                ( r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X3)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(X2,sK2(X0,X1,X2))
        & v3_pre_topc(sK2(X0,X1,X2),X0)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(X2,sK2(X0,X1,X2))
              & v3_pre_topc(sK2(X0,X1,X2),X0)
              & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
             => ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
               => ( r2_waybel_7(X0,X2,X1)
                <=> r1_tarski(k1_yellow19(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <~> r1_tarski(k1_yellow19(X0,X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <~> r1_tarski(k1_yellow19(X0,X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k1_yellow19(X0,X1),X2)
                | ~ r2_waybel_7(X0,X2,X1) )
              & ( r1_tarski(k1_yellow19(X0,X1),X2)
                | r2_waybel_7(X0,X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k1_yellow19(X0,X1),X2)
                | ~ r2_waybel_7(X0,X2,X1) )
              & ( r1_tarski(k1_yellow19(X0,X1),X2)
                | r2_waybel_7(X0,X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k1_yellow19(X0,X1),X2)
            | ~ r2_waybel_7(X0,X2,X1) )
          & ( r1_tarski(k1_yellow19(X0,X1),X2)
            | r2_waybel_7(X0,X2,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
     => ( ( ~ r1_tarski(k1_yellow19(X0,X1),sK7)
          | ~ r2_waybel_7(X0,sK7,X1) )
        & ( r1_tarski(k1_yellow19(X0,X1),sK7)
          | r2_waybel_7(X0,sK7,X1) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK7,k3_yellow_1(k2_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k1_yellow19(X0,X1),X2)
                | ~ r2_waybel_7(X0,X2,X1) )
              & ( r1_tarski(k1_yellow19(X0,X1),X2)
                | r2_waybel_7(X0,X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r1_tarski(k1_yellow19(X0,sK6),X2)
              | ~ r2_waybel_7(X0,X2,sK6) )
            & ( r1_tarski(k1_yellow19(X0,sK6),X2)
              | r2_waybel_7(X0,X2,sK6) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(k1_yellow19(X0,X1),X2)
                  | ~ r2_waybel_7(X0,X2,X1) )
                & ( r1_tarski(k1_yellow19(X0,X1),X2)
                  | r2_waybel_7(X0,X2,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k1_yellow19(sK5,X1),X2)
                | ~ r2_waybel_7(sK5,X2,X1) )
              & ( r1_tarski(k1_yellow19(sK5,X1),X2)
                | r2_waybel_7(sK5,X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK5)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK5))) )
          & m1_subset_1(X1,u1_struct_0(sK5)) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( ~ r1_tarski(k1_yellow19(sK5,sK6),sK7)
      | ~ r2_waybel_7(sK5,sK7,sK6) )
    & ( r1_tarski(k1_yellow19(sK5,sK6),sK7)
      | r2_waybel_7(sK5,sK7,sK6) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK5)))))
    & v13_waybel_0(sK7,k3_yellow_1(k2_struct_0(sK5)))
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f57,f60,f59,f58])).

fof(f93,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f94,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X3] :
                  ( r2_hidden(X1,X3)
                  & r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK1(X0,X1,X2))
        & r1_tarski(sK1(X0,X1,X2),X2)
        & v3_pre_topc(sK1(X0,X1,X2),X0)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ( r2_hidden(X1,sK1(X0,X1,X2))
                & r1_tarski(sK1(X0,X1,X2),X2)
                & v3_pre_topc(sK1(X0,X1,X2),X0)
                & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK1(X0,X1,X2),X2)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK1(X0,X1,X2))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f98,plain,
    ( r1_tarski(k1_yellow19(sK5,sK6),sK7)
    | r2_waybel_7(sK5,sK7,sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f99,plain,
    ( ~ r1_tarski(k1_yellow19(sK5,sK6),sK7)
    | ~ r2_waybel_7(sK5,sK7,sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | v3_pre_topc(sK2(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | r2_hidden(X2,sK2(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k1_yellow19(X0,X1))
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( m1_connsp_2(X2,X0,X1)
                | ~ r2_hidden(X2,k1_yellow19(X0,X1)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f97,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK5))))) ),
    inference(cnf_transformation,[],[f61])).

fof(f105,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5)))))) ),
    inference(definition_unfolding,[],[f97,f79])).

fof(f96,plain,(
    v13_waybel_0(sK7,k3_yellow_1(k2_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f61])).

fof(f106,plain,(
    v13_waybel_0(sK7,k3_lattice3(k1_lattice3(k2_struct_0(sK5)))) ),
    inference(definition_unfolding,[],[f96,f79])).

fof(f95,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2560,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | m1_subset_1(X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_3608,plain,
    ( m1_subset_1(X0_54,X1_54)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))))
    | X1_54 != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5)))))
    | X0_54 != sK7 ),
    inference(instantiation,[status(thm)],[c_2560])).

cnf(c_3694,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))))
    | X0_54 != sK7
    | k1_zfmisc_1(X1_54) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))) ),
    inference(instantiation,[status(thm)],[c_3608])).

cnf(c_35568,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK5))))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))))
    | X0_54 != sK7
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK5))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))) ),
    inference(instantiation,[status(thm)],[c_3694])).

cnf(c_35570,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK5))))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK5))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5)))))
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_35568])).

cnf(c_26,plain,
    ( ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X3,X0)
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2541,plain,
    ( ~ v13_waybel_0(X0_54,k3_lattice3(k1_lattice3(X1_54)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1_54)))))
    | ~ r2_hidden(X2_54,X0_54)
    | r2_hidden(X3_54,X0_54)
    | ~ r1_tarski(X3_54,X1_54)
    | ~ r1_tarski(X2_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_8394,plain,
    ( ~ v13_waybel_0(X0_54,k3_lattice3(k1_lattice3(X1_54)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1_54)))))
    | ~ r2_hidden(X2_54,X0_54)
    | r2_hidden(sK0(X3_54,X4_54),X0_54)
    | ~ r1_tarski(X2_54,sK0(X3_54,X4_54))
    | ~ r1_tarski(sK0(X3_54,X4_54),X1_54) ),
    inference(instantiation,[status(thm)],[c_2541])).

cnf(c_18617,plain,
    ( ~ v13_waybel_0(X0_54,k3_lattice3(k1_lattice3(X1_54)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1_54)))))
    | ~ r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),X0_54)
    | r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),X0_54)
    | ~ r1_tarski(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK0(k1_yellow19(sK5,sK6),sK7))
    | ~ r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),X1_54) ),
    inference(instantiation,[status(thm)],[c_8394])).

cnf(c_31608,plain,
    ( ~ v13_waybel_0(X0_54,k3_lattice3(k1_lattice3(u1_struct_0(sK5))))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK5))))))
    | ~ r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),X0_54)
    | r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),X0_54)
    | ~ r1_tarski(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK0(k1_yellow19(sK5,sK6),sK7))
    | ~ r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_18617])).

cnf(c_31610,plain,
    ( ~ v13_waybel_0(sK7,k3_lattice3(k1_lattice3(u1_struct_0(sK5))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK5))))))
    | ~ r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK7)
    | r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),sK7)
    | ~ r1_tarski(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK0(k1_yellow19(sK5,sK6),sK7))
    | ~ r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_31608])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2551,plain,
    ( ~ r2_hidden(sK0(X0_54,X1_54),X1_54)
    | r1_tarski(X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_18157,plain,
    ( ~ r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),sK7)
    | r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_2551])).

cnf(c_2559,plain,
    ( X0_54 != X1_54
    | k1_zfmisc_1(X0_54) = k1_zfmisc_1(X1_54) ),
    theory(equality)).

cnf(c_3695,plain,
    ( X0_54 != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))
    | k1_zfmisc_1(X0_54) = k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))) ),
    inference(instantiation,[status(thm)],[c_2559])).

cnf(c_4111,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))
    | k1_zfmisc_1(u1_struct_0(X0_55)) = k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))) ),
    inference(instantiation,[status(thm)],[c_3695])).

cnf(c_17319,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK5)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK5))))) = k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))) ),
    inference(instantiation,[status(thm)],[c_4111])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2547,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | r1_tarski(X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_5551,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(X0_54,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2547])).

cnf(c_10222,plain,
    ( ~ m1_subset_1(sK0(k1_yellow19(sK5,sK6),sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_5551])).

cnf(c_2570,plain,
    ( ~ v13_waybel_0(X0_54,X0_55)
    | v13_waybel_0(X1_54,X1_55)
    | X1_55 != X0_55
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_4154,plain,
    ( v13_waybel_0(X0_54,X0_55)
    | ~ v13_waybel_0(X1_54,k3_lattice3(k1_lattice3(k2_struct_0(sK5))))
    | X0_55 != k3_lattice3(k1_lattice3(k2_struct_0(sK5)))
    | X0_54 != X1_54 ),
    inference(instantiation,[status(thm)],[c_2570])).

cnf(c_7421,plain,
    ( v13_waybel_0(X0_54,k3_lattice3(k1_lattice3(u1_struct_0(sK5))))
    | ~ v13_waybel_0(X1_54,k3_lattice3(k1_lattice3(k2_struct_0(sK5))))
    | k3_lattice3(k1_lattice3(u1_struct_0(sK5))) != k3_lattice3(k1_lattice3(k2_struct_0(sK5)))
    | X0_54 != X1_54 ),
    inference(instantiation,[status(thm)],[c_4154])).

cnf(c_7425,plain,
    ( v13_waybel_0(sK7,k3_lattice3(k1_lattice3(u1_struct_0(sK5))))
    | ~ v13_waybel_0(sK7,k3_lattice3(k1_lattice3(k2_struct_0(sK5))))
    | k3_lattice3(k1_lattice3(u1_struct_0(sK5))) != k3_lattice3(k1_lattice3(k2_struct_0(sK5)))
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_7421])).

cnf(c_2562,plain,
    ( X0_55 != X1_55
    | u1_struct_0(X0_55) = u1_struct_0(X1_55) ),
    theory(equality)).

cnf(c_4112,plain,
    ( X0_55 != k3_lattice3(k1_lattice3(k2_struct_0(sK5)))
    | u1_struct_0(X0_55) = u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5)))) ),
    inference(instantiation,[status(thm)],[c_2562])).

cnf(c_7422,plain,
    ( k3_lattice3(k1_lattice3(u1_struct_0(sK5))) != k3_lattice3(k1_lattice3(k2_struct_0(sK5)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK5)))) = u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5)))) ),
    inference(instantiation,[status(thm)],[c_4112])).

cnf(c_2569,plain,
    ( X0_56 != X1_56
    | k3_lattice3(X0_56) = k3_lattice3(X1_56) ),
    theory(equality)).

cnf(c_3714,plain,
    ( X0_56 != k1_lattice3(k2_struct_0(sK5))
    | k3_lattice3(X0_56) = k3_lattice3(k1_lattice3(k2_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_2569])).

cnf(c_4158,plain,
    ( k1_lattice3(X0_54) != k1_lattice3(k2_struct_0(sK5))
    | k3_lattice3(k1_lattice3(X0_54)) = k3_lattice3(k1_lattice3(k2_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_3714])).

cnf(c_6461,plain,
    ( k1_lattice3(u1_struct_0(sK5)) != k1_lattice3(k2_struct_0(sK5))
    | k3_lattice3(k1_lattice3(u1_struct_0(sK5))) = k3_lattice3(k1_lattice3(k2_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_4158])).

cnf(c_2568,plain,
    ( k1_lattice3(X0_54) = k1_lattice3(X1_54)
    | X0_54 != X1_54 ),
    theory(equality)).

cnf(c_4159,plain,
    ( k1_lattice3(X0_54) = k1_lattice3(k2_struct_0(sK5))
    | X0_54 != k2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2568])).

cnf(c_5443,plain,
    ( k1_lattice3(u1_struct_0(sK5)) = k1_lattice3(k2_struct_0(sK5))
    | u1_struct_0(sK5) != k2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_4159])).

cnf(c_21,plain,
    ( ~ r2_waybel_7(X0,X1,X2)
    | ~ v3_pre_topc(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_813,plain,
    ( ~ r2_waybel_7(X0,X1,X2)
    | ~ v3_pre_topc(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,X1)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_35])).

cnf(c_814,plain,
    ( ~ r2_waybel_7(sK5,X0,X1)
    | ~ v3_pre_topc(X2,sK5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X2,X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_813])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_816,plain,
    ( r2_hidden(X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(X2,sK5)
    | ~ r2_waybel_7(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_814,c_34])).

cnf(c_817,plain,
    ( ~ r2_waybel_7(sK5,X0,X1)
    | ~ v3_pre_topc(X2,sK5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X2,X0) ),
    inference(renaming,[status(thm)],[c_816])).

cnf(c_2535,plain,
    ( ~ r2_waybel_7(sK5,X0_54,X1_54)
    | ~ v3_pre_topc(X2_54,sK5)
    | ~ m1_subset_1(X2_54,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1_54,X2_54)
    | r2_hidden(X2_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_817])).

cnf(c_4802,plain,
    ( ~ r2_waybel_7(sK5,X0_54,sK6)
    | ~ v3_pre_topc(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK5)
    | ~ m1_subset_1(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),X0_54)
    | ~ r2_hidden(sK6,sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7))) ),
    inference(instantiation,[status(thm)],[c_2535])).

cnf(c_4804,plain,
    ( ~ r2_waybel_7(sK5,sK7,sK6)
    | ~ v3_pre_topc(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK5)
    | ~ m1_subset_1(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK7)
    | ~ r2_hidden(sK6,sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7))) ),
    inference(instantiation,[status(thm)],[c_4802])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_950,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_35])).

cnf(c_951,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,k1_tops_1(sK5,X0))
    | r1_tarski(sK1(sK5,X1,X0),X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_950])).

cnf(c_955,plain,
    ( r1_tarski(sK1(sK5,X1,X0),X0)
    | ~ r2_hidden(X1,k1_tops_1(sK5,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_951,c_34])).

cnf(c_956,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,k1_tops_1(sK5,X0))
    | r1_tarski(sK1(sK5,X1,X0),X0) ),
    inference(renaming,[status(thm)],[c_955])).

cnf(c_2528,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1_54,k1_tops_1(sK5,X0_54))
    | r1_tarski(sK1(sK5,X1_54,X0_54),X0_54) ),
    inference(subtyping,[status(esa)],[c_956])).

cnf(c_4706,plain,
    ( ~ m1_subset_1(sK0(k1_yellow19(sK5,sK6),sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK6,k1_tops_1(sK5,sK0(k1_yellow19(sK5,sK6),sK7)))
    | r1_tarski(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK0(k1_yellow19(sK5,sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_2528])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,sK1(X1,X2,X0))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_971,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,sK1(X1,X2,X0))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_35])).

cnf(c_972,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(X1,sK1(sK5,X1,X0))
    | ~ r2_hidden(X1,k1_tops_1(sK5,X0))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_971])).

cnf(c_976,plain,
    ( ~ r2_hidden(X1,k1_tops_1(sK5,X0))
    | r2_hidden(X1,sK1(sK5,X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_972,c_34])).

cnf(c_977,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(X1,sK1(sK5,X1,X0))
    | ~ r2_hidden(X1,k1_tops_1(sK5,X0)) ),
    inference(renaming,[status(thm)],[c_976])).

cnf(c_2527,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(X1_54,sK1(sK5,X1_54,X0_54))
    | ~ r2_hidden(X1_54,k1_tops_1(sK5,X0_54)) ),
    inference(subtyping,[status(esa)],[c_977])).

cnf(c_4707,plain,
    ( ~ m1_subset_1(sK0(k1_yellow19(sK5,sK6),sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK6,sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)))
    | ~ r2_hidden(sK6,k1_tops_1(sK5,sK0(k1_yellow19(sK5,sK6),sK7))) ),
    inference(instantiation,[status(thm)],[c_2527])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_929,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_35])).

cnf(c_930,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK1(sK5,X1,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,k1_tops_1(sK5,X0))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_929])).

cnf(c_934,plain,
    ( ~ r2_hidden(X1,k1_tops_1(sK5,X0))
    | m1_subset_1(sK1(sK5,X1,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_930,c_34])).

cnf(c_935,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK1(sK5,X1,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,k1_tops_1(sK5,X0)) ),
    inference(renaming,[status(thm)],[c_934])).

cnf(c_2529,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK1(sK5,X1_54,X0_54),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1_54,k1_tops_1(sK5,X0_54)) ),
    inference(subtyping,[status(esa)],[c_935])).

cnf(c_4708,plain,
    ( m1_subset_1(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK0(k1_yellow19(sK5,sK6),sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK6,k1_tops_1(sK5,sK0(k1_yellow19(sK5,sK6),sK7))) ),
    inference(instantiation,[status(thm)],[c_2529])).

cnf(c_11,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,k1_tops_1(X0,X2))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_908,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,k1_tops_1(X0,X2))
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_35])).

cnf(c_909,plain,
    ( v3_pre_topc(sK1(sK5,X0,X1),sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,k1_tops_1(sK5,X1))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_908])).

cnf(c_913,plain,
    ( ~ r2_hidden(X0,k1_tops_1(sK5,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | v3_pre_topc(sK1(sK5,X0,X1),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_909,c_34])).

cnf(c_914,plain,
    ( v3_pre_topc(sK1(sK5,X0,X1),sK5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,k1_tops_1(sK5,X1)) ),
    inference(renaming,[status(thm)],[c_913])).

cnf(c_2530,plain,
    ( v3_pre_topc(sK1(sK5,X0_54,X1_54),sK5)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0_54,k1_tops_1(sK5,X1_54)) ),
    inference(subtyping,[status(esa)],[c_914])).

cnf(c_4691,plain,
    ( v3_pre_topc(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK5)
    | ~ m1_subset_1(sK0(k1_yellow19(sK5,sK6),sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK6,k1_tops_1(sK5,sK0(k1_yellow19(sK5,sK6),sK7))) ),
    inference(instantiation,[status(thm)],[c_2530])).

cnf(c_30,negated_conjecture,
    ( r2_waybel_7(sK5,sK7,sK6)
    | r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2539,negated_conjecture,
    ( r2_waybel_7(sK5,sK7,sK6)
    | r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_3423,plain,
    ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
    | r1_tarski(k1_yellow19(sK5,sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2539])).

cnf(c_29,negated_conjecture,
    ( ~ r2_waybel_7(sK5,sK7,sK6)
    | ~ r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2540,negated_conjecture,
    ( ~ r2_waybel_7(sK5,sK7,sK6)
    | ~ r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_3422,plain,
    ( r2_waybel_7(sK5,sK7,sK6) != iProver_top
    | r1_tarski(k1_yellow19(sK5,sK6),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2540])).

cnf(c_3663,plain,
    ( r2_waybel_7(sK5,sK7,sK6) != iProver_top
    | r2_waybel_7(sK5,sK7,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3423,c_3422])).

cnf(c_43,plain,
    ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
    | r1_tarski(k1_yellow19(sK5,sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_292,plain,
    ( ~ r2_waybel_7(sK5,sK7,sK6)
    | ~ r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
    inference(prop_impl,[status(thm)],[c_29])).

cnf(c_17,plain,
    ( r2_waybel_7(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_890,plain,
    ( r2_waybel_7(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X1)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_35])).

cnf(c_891,plain,
    ( r2_waybel_7(sK5,X0,X1)
    | ~ r2_hidden(sK2(sK5,X0,X1),X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_890])).

cnf(c_895,plain,
    ( ~ r2_hidden(sK2(sK5,X0,X1),X0)
    | r2_waybel_7(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_891,c_34])).

cnf(c_896,plain,
    ( r2_waybel_7(sK5,X0,X1)
    | ~ r2_hidden(sK2(sK5,X0,X1),X0) ),
    inference(renaming,[status(thm)],[c_895])).

cnf(c_1331,plain,
    ( ~ r2_hidden(sK2(sK5,X0,X1),X0)
    | ~ r1_tarski(k1_yellow19(sK5,sK6),sK7)
    | sK7 != X0
    | sK6 != X1
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_292,c_896])).

cnf(c_1332,plain,
    ( ~ r2_hidden(sK2(sK5,sK7,sK6),sK7)
    | ~ r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
    inference(unflattening,[status(thm)],[c_1331])).

cnf(c_1333,plain,
    ( r2_hidden(sK2(sK5,sK7,sK6),sK7) != iProver_top
    | r1_tarski(k1_yellow19(sK5,sK6),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1332])).

cnf(c_19,plain,
    ( r2_waybel_7(X0,X1,X2)
    | v3_pre_topc(sK2(X0,X1,X2),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_854,plain,
    ( r2_waybel_7(X0,X1,X2)
    | v3_pre_topc(sK2(X0,X1,X2),X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_35])).

cnf(c_855,plain,
    ( r2_waybel_7(sK5,X0,X1)
    | v3_pre_topc(sK2(sK5,X0,X1),sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_854])).

cnf(c_859,plain,
    ( v3_pre_topc(sK2(sK5,X0,X1),sK5)
    | r2_waybel_7(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_855,c_34])).

cnf(c_860,plain,
    ( r2_waybel_7(sK5,X0,X1)
    | v3_pre_topc(sK2(sK5,X0,X1),sK5) ),
    inference(renaming,[status(thm)],[c_859])).

cnf(c_2533,plain,
    ( r2_waybel_7(sK5,X0_54,X1_54)
    | v3_pre_topc(sK2(sK5,X0_54,X1_54),sK5) ),
    inference(subtyping,[status(esa)],[c_860])).

cnf(c_3676,plain,
    ( r2_waybel_7(sK5,sK7,sK6)
    | v3_pre_topc(sK2(sK5,sK7,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_2533])).

cnf(c_3677,plain,
    ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
    | v3_pre_topc(sK2(sK5,sK7,sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3676])).

cnf(c_20,plain,
    ( r2_waybel_7(X0,X1,X2)
    | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_836,plain,
    ( r2_waybel_7(X0,X1,X2)
    | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_35])).

cnf(c_837,plain,
    ( r2_waybel_7(sK5,X0,X1)
    | m1_subset_1(sK2(sK5,X0,X1),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_836])).

cnf(c_841,plain,
    ( m1_subset_1(sK2(sK5,X0,X1),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_waybel_7(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_837,c_34])).

cnf(c_842,plain,
    ( r2_waybel_7(sK5,X0,X1)
    | m1_subset_1(sK2(sK5,X0,X1),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(renaming,[status(thm)],[c_841])).

cnf(c_2534,plain,
    ( r2_waybel_7(sK5,X0_54,X1_54)
    | m1_subset_1(sK2(sK5,X0_54,X1_54),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_842])).

cnf(c_3675,plain,
    ( r2_waybel_7(sK5,sK7,sK6)
    | m1_subset_1(sK2(sK5,sK7,sK6),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_2534])).

cnf(c_3679,plain,
    ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
    | m1_subset_1(sK2(sK5,sK7,sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3675])).

cnf(c_18,plain,
    ( r2_waybel_7(X0,X1,X2)
    | r2_hidden(X2,sK2(X0,X1,X2))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_872,plain,
    ( r2_waybel_7(X0,X1,X2)
    | r2_hidden(X2,sK2(X0,X1,X2))
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_35])).

cnf(c_873,plain,
    ( r2_waybel_7(sK5,X0,X1)
    | r2_hidden(X1,sK2(sK5,X0,X1))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_872])).

cnf(c_877,plain,
    ( r2_hidden(X1,sK2(sK5,X0,X1))
    | r2_waybel_7(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_873,c_34])).

cnf(c_878,plain,
    ( r2_waybel_7(sK5,X0,X1)
    | r2_hidden(X1,sK2(sK5,X0,X1)) ),
    inference(renaming,[status(thm)],[c_877])).

cnf(c_2532,plain,
    ( r2_waybel_7(sK5,X0_54,X1_54)
    | r2_hidden(X1_54,sK2(sK5,X0_54,X1_54)) ),
    inference(subtyping,[status(esa)],[c_878])).

cnf(c_3674,plain,
    ( r2_waybel_7(sK5,sK7,sK6)
    | r2_hidden(sK6,sK2(sK5,sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_2532])).

cnf(c_3681,plain,
    ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
    | r2_hidden(sK6,sK2(sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3674])).

cnf(c_16,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_577,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_36])).

cnf(c_578,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_577])).

cnf(c_582,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_578,c_35,c_34])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_598,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_582,c_5])).

cnf(c_27,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X0,k1_yellow19(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_556,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X0,k1_yellow19(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_36])).

cnf(c_557,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X0,k1_yellow19(sK5,X1))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_561,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X0,k1_yellow19(sK5,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_557,c_35,c_34])).

cnf(c_1424,plain,
    ( ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,k1_yellow19(sK5,X1)) ),
    inference(resolution,[status(thm)],[c_598,c_561])).

cnf(c_1438,plain,
    ( ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,k1_yellow19(sK5,X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1424,c_5])).

cnf(c_2523,plain,
    ( ~ v3_pre_topc(X0_54,sK5)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1_54,X0_54)
    | r2_hidden(X0_54,k1_yellow19(sK5,X1_54)) ),
    inference(subtyping,[status(esa)],[c_1438])).

cnf(c_3783,plain,
    ( ~ v3_pre_topc(sK2(sK5,sK7,sK6),sK5)
    | ~ m1_subset_1(sK2(sK5,sK7,sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6))
    | ~ r2_hidden(sK6,sK2(sK5,sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_2523])).

cnf(c_3787,plain,
    ( v3_pre_topc(sK2(sK5,sK7,sK6),sK5) != iProver_top
    | m1_subset_1(sK2(sK5,sK7,sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6)) = iProver_top
    | r2_hidden(sK6,sK2(sK5,sK7,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3783])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2549,plain,
    ( ~ r2_hidden(X0_54,X1_54)
    | r2_hidden(X0_54,X2_54)
    | ~ r1_tarski(X1_54,X2_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3989,plain,
    ( r2_hidden(sK2(sK5,sK7,sK6),X0_54)
    | ~ r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6))
    | ~ r1_tarski(k1_yellow19(sK5,sK6),X0_54) ),
    inference(instantiation,[status(thm)],[c_2549])).

cnf(c_3990,plain,
    ( r2_hidden(sK2(sK5,sK7,sK6),X0_54) = iProver_top
    | r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6)) != iProver_top
    | r1_tarski(k1_yellow19(sK5,sK6),X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3989])).

cnf(c_3992,plain,
    ( r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6)) != iProver_top
    | r2_hidden(sK2(sK5,sK7,sK6),sK7) = iProver_top
    | r1_tarski(k1_yellow19(sK5,sK6),sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3990])).

cnf(c_4293,plain,
    ( r2_waybel_7(sK5,sK7,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3663,c_43,c_1333,c_3677,c_3679,c_3681,c_3787,c_3992])).

cnf(c_4295,plain,
    ( r2_waybel_7(sK5,sK7,sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4293])).

cnf(c_28,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k1_yellow19(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_535,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k1_yellow19(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_36])).

cnf(c_536,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X0,k1_yellow19(sK5,X1))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_540,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X0,k1_yellow19(sK5,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_536,c_35,c_34])).

cnf(c_14,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_15,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_15])).

cnf(c_224,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_223])).

cnf(c_514,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_224,c_36])).

cnf(c_515,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,k1_tops_1(sK5,X0))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_519,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,k1_tops_1(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_515,c_35,c_34])).

cnf(c_1483,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ r2_hidden(X1,k1_yellow19(sK5,X0))
    | r2_hidden(X0,k1_tops_1(sK5,X1)) ),
    inference(resolution,[status(thm)],[c_540,c_519])).

cnf(c_2520,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ r2_hidden(X1_54,k1_yellow19(sK5,X0_54))
    | r2_hidden(X0_54,k1_tops_1(sK5,X1_54)) ),
    inference(subtyping,[status(esa)],[c_1483])).

cnf(c_3828,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),k1_yellow19(sK5,sK6))
    | r2_hidden(sK6,k1_tops_1(sK5,sK0(k1_yellow19(sK5,sK6),sK7))) ),
    inference(instantiation,[status(thm)],[c_2520])).

cnf(c_606,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_36])).

cnf(c_607,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_611,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_607,c_35,c_34])).

cnf(c_1468,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,k1_yellow19(sK5,X0)) ),
    inference(resolution,[status(thm)],[c_540,c_611])).

cnf(c_2521,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1_54,k1_yellow19(sK5,X0_54)) ),
    inference(subtyping,[status(esa)],[c_1468])).

cnf(c_3829,plain,
    ( m1_subset_1(sK0(k1_yellow19(sK5,sK6),sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),k1_yellow19(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_2521])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2550,plain,
    ( r2_hidden(sK0(X0_54,X1_54),X0_54)
    | r1_tarski(X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3590,plain,
    ( r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),k1_yellow19(sK5,sK6))
    | r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_2550])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_500,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_7,c_6])).

cnf(c_1063,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_500,c_34])).

cnf(c_1064,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_1063])).

cnf(c_2525,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
    inference(subtyping,[status(esa)],[c_1064])).

cnf(c_2553,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_2588,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_2553])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5)))))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_32,negated_conjecture,
    ( v13_waybel_0(sK7,k3_lattice3(k1_lattice3(k2_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f95])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35570,c_31610,c_18157,c_17319,c_10222,c_7425,c_7422,c_6461,c_5443,c_4804,c_4706,c_4707,c_4708,c_4691,c_4295,c_3828,c_3829,c_3590,c_2525,c_2588,c_29,c_31,c_32,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:14:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 12.12/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
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
% 12.12/1.98  ------ Parsing...
% 12.12/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.12/1.98  
% 12.12/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 12.12/1.98  
% 12.12/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.12/1.98  
% 12.12/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.12/1.98  ------ Proving...
% 12.12/1.98  ------ Problem Properties 
% 12.12/1.98  
% 12.12/1.98  
% 12.12/1.98  clauses                                 32
% 12.12/1.98  conjectures                             5
% 12.12/1.98  EPR                                     1
% 12.12/1.98  Horn                                    24
% 12.12/1.98  unary                                   4
% 12.12/1.98  binary                                  10
% 12.12/1.98  lits                                    89
% 12.12/1.98  lits eq                                 1
% 12.12/1.98  fd_pure                                 0
% 12.12/1.98  fd_pseudo                               0
% 12.12/1.98  fd_cond                                 0
% 12.12/1.98  fd_pseudo_cond                          0
% 12.12/1.98  AC symbols                              0
% 12.12/1.98  
% 12.12/1.98  ------ Input Options Time Limit: Unbounded
% 12.12/1.98  
% 12.12/1.98  
% 12.12/1.98  ------ 
% 12.12/1.98  Current options:
% 12.12/1.98  ------ 
% 12.12/1.98  
% 12.12/1.98  
% 12.12/1.98  
% 12.12/1.98  
% 12.12/1.98  ------ Proving...
% 12.12/1.98  
% 12.12/1.98  
% 12.12/1.98  % SZS status Theorem for theBenchmark.p
% 12.12/1.98  
% 12.12/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 12.12/1.98  
% 12.12/1.98  fof(f12,axiom,(
% 12.12/1.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) => (v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : ((r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => r2_hidden(X3,X1))))),
% 12.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.12/1.98  
% 12.12/1.98  fof(f31,plain,(
% 12.12/1.98    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | (~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 12.12/1.98    inference(ennf_transformation,[],[f12])).
% 12.12/1.98  
% 12.12/1.98  fof(f32,plain,(
% 12.12/1.98    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 12.12/1.98    inference(flattening,[],[f31])).
% 12.12/1.98  
% 12.12/1.98  fof(f51,plain,(
% 12.12/1.98    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 12.12/1.98    inference(nnf_transformation,[],[f32])).
% 12.12/1.98  
% 12.12/1.98  fof(f52,plain,(
% 12.12/1.98    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 12.12/1.98    inference(rectify,[],[f51])).
% 12.12/1.98  
% 12.12/1.98  fof(f53,plain,(
% 12.12/1.98    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK3(X0,X1),X1) & r1_tarski(sK4(X0,X1),X0) & r1_tarski(sK3(X0,X1),sK4(X0,X1))))),
% 12.12/1.98    introduced(choice_axiom,[])).
% 12.12/1.98  
% 12.12/1.98  fof(f54,plain,(
% 12.12/1.98    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK3(X0,X1),X1) & r1_tarski(sK4(X0,X1),X0) & r1_tarski(sK3(X0,X1),sK4(X0,X1)))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 12.12/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f52,f53])).
% 12.12/1.98  
% 12.12/1.98  fof(f85,plain,(
% 12.12/1.98    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))) )),
% 12.12/1.98    inference(cnf_transformation,[],[f54])).
% 12.12/1.98  
% 12.12/1.98  fof(f10,axiom,(
% 12.12/1.98    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 12.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.12/1.98  
% 12.12/1.98  fof(f79,plain,(
% 12.12/1.98    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 12.12/1.98    inference(cnf_transformation,[],[f10])).
% 12.12/1.98  
% 12.12/1.98  fof(f104,plain,(
% 12.12/1.98    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))) )),
% 12.12/1.98    inference(definition_unfolding,[],[f85,f79,f79])).
% 12.12/1.98  
% 12.12/1.98  fof(f1,axiom,(
% 12.12/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 12.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.12/1.98  
% 12.12/1.98  fof(f16,plain,(
% 12.12/1.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 12.12/1.98    inference(ennf_transformation,[],[f1])).
% 12.12/1.98  
% 12.12/1.98  fof(f37,plain,(
% 12.12/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 12.12/1.98    inference(nnf_transformation,[],[f16])).
% 12.12/1.98  
% 12.12/1.98  fof(f38,plain,(
% 12.12/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.12/1.98    inference(rectify,[],[f37])).
% 12.12/1.98  
% 12.12/1.98  fof(f39,plain,(
% 12.12/1.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 12.12/1.98    introduced(choice_axiom,[])).
% 12.12/1.98  
% 12.12/1.98  fof(f40,plain,(
% 12.12/1.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.12/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 12.12/1.98  
% 12.12/1.98  fof(f64,plain,(
% 12.12/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f40])).
% 12.12/1.98  
% 12.12/1.98  fof(f2,axiom,(
% 12.12/1.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 12.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.12/1.98  
% 12.12/1.98  fof(f41,plain,(
% 12.12/1.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 12.12/1.98    inference(nnf_transformation,[],[f2])).
% 12.12/1.98  
% 12.12/1.98  fof(f65,plain,(
% 12.12/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 12.12/1.98    inference(cnf_transformation,[],[f41])).
% 12.12/1.98  
% 12.12/1.98  fof(f11,axiom,(
% 12.12/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,X3) & v3_pre_topc(X3,X0)) => r2_hidden(X3,X1)))))),
% 12.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.12/1.98  
% 12.12/1.98  fof(f29,plain,(
% 12.12/1.98    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : ((r2_hidden(X3,X1) | (~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 12.12/1.98    inference(ennf_transformation,[],[f11])).
% 12.12/1.98  
% 12.12/1.98  fof(f30,plain,(
% 12.12/1.98    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.12/1.98    inference(flattening,[],[f29])).
% 12.12/1.98  
% 12.12/1.98  fof(f47,plain,(
% 12.12/1.98    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | ? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.12/1.98    inference(nnf_transformation,[],[f30])).
% 12.12/1.98  
% 12.12/1.98  fof(f48,plain,(
% 12.12/1.98    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | ? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.12/1.98    inference(rectify,[],[f47])).
% 12.12/1.98  
% 12.12/1.98  fof(f49,plain,(
% 12.12/1.98    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(X2,sK2(X0,X1,X2)) & v3_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 12.12/1.98    introduced(choice_axiom,[])).
% 12.12/1.98  
% 12.12/1.98  fof(f50,plain,(
% 12.12/1.98    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | (~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(X2,sK2(X0,X1,X2)) & v3_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.12/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).
% 12.12/1.98  
% 12.12/1.98  fof(f80,plain,(
% 12.12/1.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_waybel_7(X0,X1,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f50])).
% 12.12/1.98  
% 12.12/1.98  fof(f14,conjecture,(
% 12.12/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => (r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)))))),
% 12.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.12/1.98  
% 12.12/1.98  fof(f15,negated_conjecture,(
% 12.12/1.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => (r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)))))),
% 12.12/1.98    inference(negated_conjecture,[],[f14])).
% 12.12/1.98  
% 12.12/1.98  fof(f35,plain,(
% 12.12/1.98    ? [X0] : (? [X1] : (? [X2] : ((r2_waybel_7(X0,X2,X1) <~> r1_tarski(k1_yellow19(X0,X1),X2)) & (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 12.12/1.98    inference(ennf_transformation,[],[f15])).
% 12.12/1.98  
% 12.12/1.98  fof(f36,plain,(
% 12.12/1.98    ? [X0] : (? [X1] : (? [X2] : ((r2_waybel_7(X0,X2,X1) <~> r1_tarski(k1_yellow19(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 12.12/1.98    inference(flattening,[],[f35])).
% 12.12/1.98  
% 12.12/1.98  fof(f56,plain,(
% 12.12/1.98    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 12.12/1.98    inference(nnf_transformation,[],[f36])).
% 12.12/1.98  
% 12.12/1.98  fof(f57,plain,(
% 12.12/1.98    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 12.12/1.98    inference(flattening,[],[f56])).
% 12.12/1.98  
% 12.12/1.98  fof(f60,plain,(
% 12.12/1.98    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => ((~r1_tarski(k1_yellow19(X0,X1),sK7) | ~r2_waybel_7(X0,sK7,X1)) & (r1_tarski(k1_yellow19(X0,X1),sK7) | r2_waybel_7(X0,sK7,X1)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK7,k3_yellow_1(k2_struct_0(X0))))) )),
% 12.12/1.98    introduced(choice_axiom,[])).
% 12.12/1.98  
% 12.12/1.98  fof(f59,plain,(
% 12.12/1.98    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~r1_tarski(k1_yellow19(X0,sK6),X2) | ~r2_waybel_7(X0,X2,sK6)) & (r1_tarski(k1_yellow19(X0,sK6),X2) | r2_waybel_7(X0,X2,sK6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 12.12/1.98    introduced(choice_axiom,[])).
% 12.12/1.98  
% 12.12/1.98  fof(f58,plain,(
% 12.12/1.98    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(sK5,X1),X2) | ~r2_waybel_7(sK5,X2,X1)) & (r1_tarski(k1_yellow19(sK5,X1),X2) | r2_waybel_7(sK5,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK5))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK5)))) & m1_subset_1(X1,u1_struct_0(sK5))) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 12.12/1.98    introduced(choice_axiom,[])).
% 12.12/1.98  
% 12.12/1.98  fof(f61,plain,(
% 12.12/1.98    (((~r1_tarski(k1_yellow19(sK5,sK6),sK7) | ~r2_waybel_7(sK5,sK7,sK6)) & (r1_tarski(k1_yellow19(sK5,sK6),sK7) | r2_waybel_7(sK5,sK7,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK5))))) & v13_waybel_0(sK7,k3_yellow_1(k2_struct_0(sK5)))) & m1_subset_1(sK6,u1_struct_0(sK5))) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 12.12/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f57,f60,f59,f58])).
% 12.12/1.98  
% 12.12/1.98  fof(f93,plain,(
% 12.12/1.98    v2_pre_topc(sK5)),
% 12.12/1.98    inference(cnf_transformation,[],[f61])).
% 12.12/1.98  
% 12.12/1.98  fof(f94,plain,(
% 12.12/1.98    l1_pre_topc(sK5)),
% 12.12/1.98    inference(cnf_transformation,[],[f61])).
% 12.12/1.98  
% 12.12/1.98  fof(f6,axiom,(
% 12.12/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 12.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.12/1.98  
% 12.12/1.98  fof(f21,plain,(
% 12.12/1.98    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 12.12/1.98    inference(ennf_transformation,[],[f6])).
% 12.12/1.98  
% 12.12/1.98  fof(f22,plain,(
% 12.12/1.98    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.12/1.98    inference(flattening,[],[f21])).
% 12.12/1.98  
% 12.12/1.98  fof(f42,plain,(
% 12.12/1.98    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.12/1.98    inference(nnf_transformation,[],[f22])).
% 12.12/1.98  
% 12.12/1.98  fof(f43,plain,(
% 12.12/1.98    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.12/1.98    inference(rectify,[],[f42])).
% 12.12/1.98  
% 12.12/1.98  fof(f44,plain,(
% 12.12/1.98    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 12.12/1.98    introduced(choice_axiom,[])).
% 12.12/1.98  
% 12.12/1.98  fof(f45,plain,(
% 12.12/1.98    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.12/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 12.12/1.98  
% 12.12/1.98  fof(f72,plain,(
% 12.12/1.98    ( ! [X2,X0,X1] : (r1_tarski(sK1(X0,X1,X2),X2) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f45])).
% 12.12/1.98  
% 12.12/1.98  fof(f73,plain,(
% 12.12/1.98    ( ! [X2,X0,X1] : (r2_hidden(X1,sK1(X0,X1,X2)) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f45])).
% 12.12/1.98  
% 12.12/1.98  fof(f70,plain,(
% 12.12/1.98    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f45])).
% 12.12/1.98  
% 12.12/1.98  fof(f71,plain,(
% 12.12/1.98    ( ! [X2,X0,X1] : (v3_pre_topc(sK1(X0,X1,X2),X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f45])).
% 12.12/1.98  
% 12.12/1.98  fof(f98,plain,(
% 12.12/1.98    r1_tarski(k1_yellow19(sK5,sK6),sK7) | r2_waybel_7(sK5,sK7,sK6)),
% 12.12/1.98    inference(cnf_transformation,[],[f61])).
% 12.12/1.98  
% 12.12/1.98  fof(f99,plain,(
% 12.12/1.98    ~r1_tarski(k1_yellow19(sK5,sK6),sK7) | ~r2_waybel_7(sK5,sK7,sK6)),
% 12.12/1.98    inference(cnf_transformation,[],[f61])).
% 12.12/1.98  
% 12.12/1.98  fof(f84,plain,(
% 12.12/1.98    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f50])).
% 12.12/1.98  
% 12.12/1.98  fof(f82,plain,(
% 12.12/1.98    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | v3_pre_topc(sK2(X0,X1,X2),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f50])).
% 12.12/1.98  
% 12.12/1.98  fof(f81,plain,(
% 12.12/1.98    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f50])).
% 12.12/1.98  
% 12.12/1.98  fof(f83,plain,(
% 12.12/1.98    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,sK2(X0,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f50])).
% 12.12/1.98  
% 12.12/1.98  fof(f9,axiom,(
% 12.12/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 12.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.12/1.98  
% 12.12/1.98  fof(f27,plain,(
% 12.12/1.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 12.12/1.98    inference(ennf_transformation,[],[f9])).
% 12.12/1.98  
% 12.12/1.98  fof(f28,plain,(
% 12.12/1.98    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 12.12/1.98    inference(flattening,[],[f27])).
% 12.12/1.98  
% 12.12/1.98  fof(f78,plain,(
% 12.12/1.98    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f28])).
% 12.12/1.98  
% 12.12/1.98  fof(f92,plain,(
% 12.12/1.98    ~v2_struct_0(sK5)),
% 12.12/1.98    inference(cnf_transformation,[],[f61])).
% 12.12/1.98  
% 12.12/1.98  fof(f3,axiom,(
% 12.12/1.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 12.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.12/1.98  
% 12.12/1.98  fof(f17,plain,(
% 12.12/1.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 12.12/1.98    inference(ennf_transformation,[],[f3])).
% 12.12/1.98  
% 12.12/1.98  fof(f18,plain,(
% 12.12/1.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 12.12/1.98    inference(flattening,[],[f17])).
% 12.12/1.98  
% 12.12/1.98  fof(f67,plain,(
% 12.12/1.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f18])).
% 12.12/1.98  
% 12.12/1.98  fof(f13,axiom,(
% 12.12/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1))))),
% 12.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.12/1.98  
% 12.12/1.98  fof(f33,plain,(
% 12.12/1.98    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 12.12/1.98    inference(ennf_transformation,[],[f13])).
% 12.12/1.98  
% 12.12/1.98  fof(f34,plain,(
% 12.12/1.98    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 12.12/1.98    inference(flattening,[],[f33])).
% 12.12/1.98  
% 12.12/1.98  fof(f55,plain,(
% 12.12/1.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_connsp_2(X2,X0,X1)) & (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X2,k1_yellow19(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 12.12/1.98    inference(nnf_transformation,[],[f34])).
% 12.12/1.98  
% 12.12/1.98  fof(f91,plain,(
% 12.12/1.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f55])).
% 12.12/1.98  
% 12.12/1.98  fof(f62,plain,(
% 12.12/1.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f40])).
% 12.12/1.98  
% 12.12/1.98  fof(f90,plain,(
% 12.12/1.98    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f55])).
% 12.12/1.98  
% 12.12/1.98  fof(f7,axiom,(
% 12.12/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 12.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.12/1.98  
% 12.12/1.98  fof(f23,plain,(
% 12.12/1.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 12.12/1.98    inference(ennf_transformation,[],[f7])).
% 12.12/1.98  
% 12.12/1.98  fof(f24,plain,(
% 12.12/1.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 12.12/1.98    inference(flattening,[],[f23])).
% 12.12/1.98  
% 12.12/1.98  fof(f46,plain,(
% 12.12/1.98    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 12.12/1.98    inference(nnf_transformation,[],[f24])).
% 12.12/1.98  
% 12.12/1.98  fof(f75,plain,(
% 12.12/1.98    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f46])).
% 12.12/1.98  
% 12.12/1.98  fof(f8,axiom,(
% 12.12/1.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 12.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.12/1.98  
% 12.12/1.98  fof(f25,plain,(
% 12.12/1.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 12.12/1.98    inference(ennf_transformation,[],[f8])).
% 12.12/1.98  
% 12.12/1.98  fof(f26,plain,(
% 12.12/1.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 12.12/1.98    inference(flattening,[],[f25])).
% 12.12/1.98  
% 12.12/1.98  fof(f77,plain,(
% 12.12/1.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f26])).
% 12.12/1.98  
% 12.12/1.98  fof(f63,plain,(
% 12.12/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f40])).
% 12.12/1.98  
% 12.12/1.98  fof(f5,axiom,(
% 12.12/1.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 12.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.12/1.98  
% 12.12/1.98  fof(f20,plain,(
% 12.12/1.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 12.12/1.98    inference(ennf_transformation,[],[f5])).
% 12.12/1.98  
% 12.12/1.98  fof(f69,plain,(
% 12.12/1.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f20])).
% 12.12/1.98  
% 12.12/1.98  fof(f4,axiom,(
% 12.12/1.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 12.12/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.12/1.98  
% 12.12/1.98  fof(f19,plain,(
% 12.12/1.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 12.12/1.98    inference(ennf_transformation,[],[f4])).
% 12.12/1.98  
% 12.12/1.98  fof(f68,plain,(
% 12.12/1.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 12.12/1.98    inference(cnf_transformation,[],[f19])).
% 12.12/1.98  
% 12.12/1.98  fof(f97,plain,(
% 12.12/1.98    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK5)))))),
% 12.12/1.98    inference(cnf_transformation,[],[f61])).
% 12.12/1.98  
% 12.12/1.98  fof(f105,plain,(
% 12.12/1.98    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))))),
% 12.12/1.98    inference(definition_unfolding,[],[f97,f79])).
% 12.12/1.98  
% 12.12/1.98  fof(f96,plain,(
% 12.12/1.98    v13_waybel_0(sK7,k3_yellow_1(k2_struct_0(sK5)))),
% 12.12/1.98    inference(cnf_transformation,[],[f61])).
% 12.12/1.98  
% 12.12/1.98  fof(f106,plain,(
% 12.12/1.98    v13_waybel_0(sK7,k3_lattice3(k1_lattice3(k2_struct_0(sK5))))),
% 12.12/1.98    inference(definition_unfolding,[],[f96,f79])).
% 12.12/1.98  
% 12.12/1.98  fof(f95,plain,(
% 12.12/1.98    m1_subset_1(sK6,u1_struct_0(sK5))),
% 12.12/1.98    inference(cnf_transformation,[],[f61])).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2560,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0_54,X1_54)
% 12.12/1.98      | m1_subset_1(X2_54,X3_54)
% 12.12/1.98      | X2_54 != X0_54
% 12.12/1.98      | X3_54 != X1_54 ),
% 12.12/1.98      theory(equality) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3608,plain,
% 12.12/1.98      ( m1_subset_1(X0_54,X1_54)
% 12.12/1.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))))
% 12.12/1.98      | X1_54 != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5)))))
% 12.12/1.98      | X0_54 != sK7 ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2560]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3694,plain,
% 12.12/1.98      ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 12.12/1.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))))
% 12.12/1.98      | X0_54 != sK7
% 12.12/1.98      | k1_zfmisc_1(X1_54) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_3608]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_35568,plain,
% 12.12/1.98      ( m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK5))))))
% 12.12/1.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))))
% 12.12/1.98      | X0_54 != sK7
% 12.12/1.98      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK5))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_3694]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_35570,plain,
% 12.12/1.98      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK5))))))
% 12.12/1.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))))
% 12.12/1.98      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK5))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5)))))
% 12.12/1.98      | sK7 != sK7 ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_35568]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_26,plain,
% 12.12/1.98      ( ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 12.12/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 12.12/1.98      | ~ r2_hidden(X2,X0)
% 12.12/1.98      | r2_hidden(X3,X0)
% 12.12/1.98      | ~ r1_tarski(X3,X1)
% 12.12/1.98      | ~ r1_tarski(X2,X3) ),
% 12.12/1.98      inference(cnf_transformation,[],[f104]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2541,plain,
% 12.12/1.98      ( ~ v13_waybel_0(X0_54,k3_lattice3(k1_lattice3(X1_54)))
% 12.12/1.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1_54)))))
% 12.12/1.98      | ~ r2_hidden(X2_54,X0_54)
% 12.12/1.98      | r2_hidden(X3_54,X0_54)
% 12.12/1.98      | ~ r1_tarski(X3_54,X1_54)
% 12.12/1.98      | ~ r1_tarski(X2_54,X3_54) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_26]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_8394,plain,
% 12.12/1.98      ( ~ v13_waybel_0(X0_54,k3_lattice3(k1_lattice3(X1_54)))
% 12.12/1.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1_54)))))
% 12.12/1.98      | ~ r2_hidden(X2_54,X0_54)
% 12.12/1.98      | r2_hidden(sK0(X3_54,X4_54),X0_54)
% 12.12/1.98      | ~ r1_tarski(X2_54,sK0(X3_54,X4_54))
% 12.12/1.98      | ~ r1_tarski(sK0(X3_54,X4_54),X1_54) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2541]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_18617,plain,
% 12.12/1.98      ( ~ v13_waybel_0(X0_54,k3_lattice3(k1_lattice3(X1_54)))
% 12.12/1.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1_54)))))
% 12.12/1.98      | ~ r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),X0_54)
% 12.12/1.98      | r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),X0_54)
% 12.12/1.98      | ~ r1_tarski(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK0(k1_yellow19(sK5,sK6),sK7))
% 12.12/1.98      | ~ r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),X1_54) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_8394]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_31608,plain,
% 12.12/1.98      ( ~ v13_waybel_0(X0_54,k3_lattice3(k1_lattice3(u1_struct_0(sK5))))
% 12.12/1.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK5))))))
% 12.12/1.98      | ~ r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),X0_54)
% 12.12/1.98      | r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),X0_54)
% 12.12/1.98      | ~ r1_tarski(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK0(k1_yellow19(sK5,sK6),sK7))
% 12.12/1.98      | ~ r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),u1_struct_0(sK5)) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_18617]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_31610,plain,
% 12.12/1.98      ( ~ v13_waybel_0(sK7,k3_lattice3(k1_lattice3(u1_struct_0(sK5))))
% 12.12/1.98      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK5))))))
% 12.12/1.98      | ~ r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK7)
% 12.12/1.98      | r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),sK7)
% 12.12/1.98      | ~ r1_tarski(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK0(k1_yellow19(sK5,sK6),sK7))
% 12.12/1.98      | ~ r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),u1_struct_0(sK5)) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_31608]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_0,plain,
% 12.12/1.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 12.12/1.98      inference(cnf_transformation,[],[f64]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2551,plain,
% 12.12/1.98      ( ~ r2_hidden(sK0(X0_54,X1_54),X1_54) | r1_tarski(X0_54,X1_54) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_0]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_18157,plain,
% 12.12/1.98      ( ~ r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),sK7)
% 12.12/1.98      | r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2551]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2559,plain,
% 12.12/1.98      ( X0_54 != X1_54 | k1_zfmisc_1(X0_54) = k1_zfmisc_1(X1_54) ),
% 12.12/1.98      theory(equality) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3695,plain,
% 12.12/1.98      ( X0_54 != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))
% 12.12/1.98      | k1_zfmisc_1(X0_54) = k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2559]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_4111,plain,
% 12.12/1.98      ( u1_struct_0(X0_55) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))
% 12.12/1.98      | k1_zfmisc_1(u1_struct_0(X0_55)) = k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_3695]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_17319,plain,
% 12.12/1.98      ( u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK5)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))
% 12.12/1.98      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK5))))) = k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_4111]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_4,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 12.12/1.98      inference(cnf_transformation,[],[f65]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2547,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 12.12/1.98      | r1_tarski(X0_54,X1_54) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_4]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_5551,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | r1_tarski(X0_54,u1_struct_0(sK5)) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2547]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_10222,plain,
% 12.12/1.98      ( ~ m1_subset_1(sK0(k1_yellow19(sK5,sK6),sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),u1_struct_0(sK5)) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_5551]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2570,plain,
% 12.12/1.98      ( ~ v13_waybel_0(X0_54,X0_55)
% 12.12/1.98      | v13_waybel_0(X1_54,X1_55)
% 12.12/1.98      | X1_55 != X0_55
% 12.12/1.98      | X1_54 != X0_54 ),
% 12.12/1.98      theory(equality) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_4154,plain,
% 12.12/1.98      ( v13_waybel_0(X0_54,X0_55)
% 12.12/1.98      | ~ v13_waybel_0(X1_54,k3_lattice3(k1_lattice3(k2_struct_0(sK5))))
% 12.12/1.98      | X0_55 != k3_lattice3(k1_lattice3(k2_struct_0(sK5)))
% 12.12/1.98      | X0_54 != X1_54 ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2570]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_7421,plain,
% 12.12/1.98      ( v13_waybel_0(X0_54,k3_lattice3(k1_lattice3(u1_struct_0(sK5))))
% 12.12/1.98      | ~ v13_waybel_0(X1_54,k3_lattice3(k1_lattice3(k2_struct_0(sK5))))
% 12.12/1.98      | k3_lattice3(k1_lattice3(u1_struct_0(sK5))) != k3_lattice3(k1_lattice3(k2_struct_0(sK5)))
% 12.12/1.98      | X0_54 != X1_54 ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_4154]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_7425,plain,
% 12.12/1.98      ( v13_waybel_0(sK7,k3_lattice3(k1_lattice3(u1_struct_0(sK5))))
% 12.12/1.98      | ~ v13_waybel_0(sK7,k3_lattice3(k1_lattice3(k2_struct_0(sK5))))
% 12.12/1.98      | k3_lattice3(k1_lattice3(u1_struct_0(sK5))) != k3_lattice3(k1_lattice3(k2_struct_0(sK5)))
% 12.12/1.98      | sK7 != sK7 ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_7421]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2562,plain,
% 12.12/1.98      ( X0_55 != X1_55 | u1_struct_0(X0_55) = u1_struct_0(X1_55) ),
% 12.12/1.98      theory(equality) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_4112,plain,
% 12.12/1.98      ( X0_55 != k3_lattice3(k1_lattice3(k2_struct_0(sK5)))
% 12.12/1.98      | u1_struct_0(X0_55) = u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5)))) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2562]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_7422,plain,
% 12.12/1.98      ( k3_lattice3(k1_lattice3(u1_struct_0(sK5))) != k3_lattice3(k1_lattice3(k2_struct_0(sK5)))
% 12.12/1.98      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK5)))) = u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5)))) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_4112]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2569,plain,
% 12.12/1.98      ( X0_56 != X1_56 | k3_lattice3(X0_56) = k3_lattice3(X1_56) ),
% 12.12/1.98      theory(equality) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3714,plain,
% 12.12/1.98      ( X0_56 != k1_lattice3(k2_struct_0(sK5))
% 12.12/1.98      | k3_lattice3(X0_56) = k3_lattice3(k1_lattice3(k2_struct_0(sK5))) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2569]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_4158,plain,
% 12.12/1.98      ( k1_lattice3(X0_54) != k1_lattice3(k2_struct_0(sK5))
% 12.12/1.98      | k3_lattice3(k1_lattice3(X0_54)) = k3_lattice3(k1_lattice3(k2_struct_0(sK5))) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_3714]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_6461,plain,
% 12.12/1.98      ( k1_lattice3(u1_struct_0(sK5)) != k1_lattice3(k2_struct_0(sK5))
% 12.12/1.98      | k3_lattice3(k1_lattice3(u1_struct_0(sK5))) = k3_lattice3(k1_lattice3(k2_struct_0(sK5))) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_4158]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2568,plain,
% 12.12/1.98      ( k1_lattice3(X0_54) = k1_lattice3(X1_54) | X0_54 != X1_54 ),
% 12.12/1.98      theory(equality) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_4159,plain,
% 12.12/1.98      ( k1_lattice3(X0_54) = k1_lattice3(k2_struct_0(sK5))
% 12.12/1.98      | X0_54 != k2_struct_0(sK5) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2568]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_5443,plain,
% 12.12/1.98      ( k1_lattice3(u1_struct_0(sK5)) = k1_lattice3(k2_struct_0(sK5))
% 12.12/1.98      | u1_struct_0(sK5) != k2_struct_0(sK5) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_4159]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_21,plain,
% 12.12/1.98      ( ~ r2_waybel_7(X0,X1,X2)
% 12.12/1.98      | ~ v3_pre_topc(X3,X0)
% 12.12/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 12.12/1.98      | ~ r2_hidden(X2,X3)
% 12.12/1.98      | r2_hidden(X3,X1)
% 12.12/1.98      | ~ v2_pre_topc(X0)
% 12.12/1.98      | ~ l1_pre_topc(X0) ),
% 12.12/1.98      inference(cnf_transformation,[],[f80]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_35,negated_conjecture,
% 12.12/1.98      ( v2_pre_topc(sK5) ),
% 12.12/1.98      inference(cnf_transformation,[],[f93]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_813,plain,
% 12.12/1.98      ( ~ r2_waybel_7(X0,X1,X2)
% 12.12/1.98      | ~ v3_pre_topc(X3,X0)
% 12.12/1.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 12.12/1.98      | ~ r2_hidden(X2,X3)
% 12.12/1.98      | r2_hidden(X3,X1)
% 12.12/1.98      | ~ l1_pre_topc(X0)
% 12.12/1.98      | sK5 != X0 ),
% 12.12/1.98      inference(resolution_lifted,[status(thm)],[c_21,c_35]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_814,plain,
% 12.12/1.98      ( ~ r2_waybel_7(sK5,X0,X1)
% 12.12/1.98      | ~ v3_pre_topc(X2,sK5)
% 12.12/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X1,X2)
% 12.12/1.98      | r2_hidden(X2,X0)
% 12.12/1.98      | ~ l1_pre_topc(sK5) ),
% 12.12/1.98      inference(unflattening,[status(thm)],[c_813]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_34,negated_conjecture,
% 12.12/1.98      ( l1_pre_topc(sK5) ),
% 12.12/1.98      inference(cnf_transformation,[],[f94]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_816,plain,
% 12.12/1.98      ( r2_hidden(X2,X0)
% 12.12/1.98      | ~ r2_hidden(X1,X2)
% 12.12/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ v3_pre_topc(X2,sK5)
% 12.12/1.98      | ~ r2_waybel_7(sK5,X0,X1) ),
% 12.12/1.98      inference(global_propositional_subsumption,
% 12.12/1.98                [status(thm)],
% 12.12/1.98                [c_814,c_34]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_817,plain,
% 12.12/1.98      ( ~ r2_waybel_7(sK5,X0,X1)
% 12.12/1.98      | ~ v3_pre_topc(X2,sK5)
% 12.12/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X1,X2)
% 12.12/1.98      | r2_hidden(X2,X0) ),
% 12.12/1.98      inference(renaming,[status(thm)],[c_816]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2535,plain,
% 12.12/1.98      ( ~ r2_waybel_7(sK5,X0_54,X1_54)
% 12.12/1.98      | ~ v3_pre_topc(X2_54,sK5)
% 12.12/1.98      | ~ m1_subset_1(X2_54,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X1_54,X2_54)
% 12.12/1.98      | r2_hidden(X2_54,X0_54) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_817]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_4802,plain,
% 12.12/1.98      ( ~ r2_waybel_7(sK5,X0_54,sK6)
% 12.12/1.98      | ~ v3_pre_topc(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK5)
% 12.12/1.98      | ~ m1_subset_1(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),X0_54)
% 12.12/1.98      | ~ r2_hidden(sK6,sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7))) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2535]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_4804,plain,
% 12.12/1.98      ( ~ r2_waybel_7(sK5,sK7,sK6)
% 12.12/1.98      | ~ v3_pre_topc(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK5)
% 12.12/1.98      | ~ m1_subset_1(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK7)
% 12.12/1.98      | ~ r2_hidden(sK6,sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7))) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_4802]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_10,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.12/1.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 12.12/1.98      | r1_tarski(sK1(X1,X2,X0),X0)
% 12.12/1.98      | ~ v2_pre_topc(X1)
% 12.12/1.98      | ~ l1_pre_topc(X1) ),
% 12.12/1.98      inference(cnf_transformation,[],[f72]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_950,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.12/1.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 12.12/1.98      | r1_tarski(sK1(X1,X2,X0),X0)
% 12.12/1.98      | ~ l1_pre_topc(X1)
% 12.12/1.98      | sK5 != X1 ),
% 12.12/1.98      inference(resolution_lifted,[status(thm)],[c_10,c_35]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_951,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X1,k1_tops_1(sK5,X0))
% 12.12/1.98      | r1_tarski(sK1(sK5,X1,X0),X0)
% 12.12/1.98      | ~ l1_pre_topc(sK5) ),
% 12.12/1.98      inference(unflattening,[status(thm)],[c_950]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_955,plain,
% 12.12/1.98      ( r1_tarski(sK1(sK5,X1,X0),X0)
% 12.12/1.98      | ~ r2_hidden(X1,k1_tops_1(sK5,X0))
% 12.12/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 12.12/1.98      inference(global_propositional_subsumption,
% 12.12/1.98                [status(thm)],
% 12.12/1.98                [c_951,c_34]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_956,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X1,k1_tops_1(sK5,X0))
% 12.12/1.98      | r1_tarski(sK1(sK5,X1,X0),X0) ),
% 12.12/1.98      inference(renaming,[status(thm)],[c_955]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2528,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X1_54,k1_tops_1(sK5,X0_54))
% 12.12/1.98      | r1_tarski(sK1(sK5,X1_54,X0_54),X0_54) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_956]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_4706,plain,
% 12.12/1.98      ( ~ m1_subset_1(sK0(k1_yellow19(sK5,sK6),sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(sK6,k1_tops_1(sK5,sK0(k1_yellow19(sK5,sK6),sK7)))
% 12.12/1.98      | r1_tarski(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK0(k1_yellow19(sK5,sK6),sK7)) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2528]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_9,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.12/1.98      | r2_hidden(X2,sK1(X1,X2,X0))
% 12.12/1.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 12.12/1.98      | ~ v2_pre_topc(X1)
% 12.12/1.98      | ~ l1_pre_topc(X1) ),
% 12.12/1.98      inference(cnf_transformation,[],[f73]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_971,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.12/1.98      | r2_hidden(X2,sK1(X1,X2,X0))
% 12.12/1.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 12.12/1.98      | ~ l1_pre_topc(X1)
% 12.12/1.98      | sK5 != X1 ),
% 12.12/1.98      inference(resolution_lifted,[status(thm)],[c_9,c_35]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_972,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | r2_hidden(X1,sK1(sK5,X1,X0))
% 12.12/1.98      | ~ r2_hidden(X1,k1_tops_1(sK5,X0))
% 12.12/1.98      | ~ l1_pre_topc(sK5) ),
% 12.12/1.98      inference(unflattening,[status(thm)],[c_971]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_976,plain,
% 12.12/1.98      ( ~ r2_hidden(X1,k1_tops_1(sK5,X0))
% 12.12/1.98      | r2_hidden(X1,sK1(sK5,X1,X0))
% 12.12/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 12.12/1.98      inference(global_propositional_subsumption,
% 12.12/1.98                [status(thm)],
% 12.12/1.98                [c_972,c_34]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_977,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | r2_hidden(X1,sK1(sK5,X1,X0))
% 12.12/1.98      | ~ r2_hidden(X1,k1_tops_1(sK5,X0)) ),
% 12.12/1.98      inference(renaming,[status(thm)],[c_976]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2527,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | r2_hidden(X1_54,sK1(sK5,X1_54,X0_54))
% 12.12/1.98      | ~ r2_hidden(X1_54,k1_tops_1(sK5,X0_54)) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_977]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_4707,plain,
% 12.12/1.98      ( ~ m1_subset_1(sK0(k1_yellow19(sK5,sK6),sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | r2_hidden(sK6,sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)))
% 12.12/1.98      | ~ r2_hidden(sK6,k1_tops_1(sK5,sK0(k1_yellow19(sK5,sK6),sK7))) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2527]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_12,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.12/1.98      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 12.12/1.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 12.12/1.98      | ~ v2_pre_topc(X1)
% 12.12/1.98      | ~ l1_pre_topc(X1) ),
% 12.12/1.98      inference(cnf_transformation,[],[f70]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_929,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.12/1.98      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 12.12/1.98      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 12.12/1.98      | ~ l1_pre_topc(X1)
% 12.12/1.98      | sK5 != X1 ),
% 12.12/1.98      inference(resolution_lifted,[status(thm)],[c_12,c_35]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_930,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | m1_subset_1(sK1(sK5,X1,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X1,k1_tops_1(sK5,X0))
% 12.12/1.98      | ~ l1_pre_topc(sK5) ),
% 12.12/1.98      inference(unflattening,[status(thm)],[c_929]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_934,plain,
% 12.12/1.98      ( ~ r2_hidden(X1,k1_tops_1(sK5,X0))
% 12.12/1.98      | m1_subset_1(sK1(sK5,X1,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 12.12/1.98      inference(global_propositional_subsumption,
% 12.12/1.98                [status(thm)],
% 12.12/1.98                [c_930,c_34]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_935,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | m1_subset_1(sK1(sK5,X1,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X1,k1_tops_1(sK5,X0)) ),
% 12.12/1.98      inference(renaming,[status(thm)],[c_934]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2529,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | m1_subset_1(sK1(sK5,X1_54,X0_54),k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X1_54,k1_tops_1(sK5,X0_54)) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_935]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_4708,plain,
% 12.12/1.98      ( m1_subset_1(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ m1_subset_1(sK0(k1_yellow19(sK5,sK6),sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(sK6,k1_tops_1(sK5,sK0(k1_yellow19(sK5,sK6),sK7))) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2529]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_11,plain,
% 12.12/1.98      ( v3_pre_topc(sK1(X0,X1,X2),X0)
% 12.12/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 12.12/1.98      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
% 12.12/1.98      | ~ v2_pre_topc(X0)
% 12.12/1.98      | ~ l1_pre_topc(X0) ),
% 12.12/1.98      inference(cnf_transformation,[],[f71]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_908,plain,
% 12.12/1.98      ( v3_pre_topc(sK1(X0,X1,X2),X0)
% 12.12/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 12.12/1.98      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
% 12.12/1.98      | ~ l1_pre_topc(X0)
% 12.12/1.98      | sK5 != X0 ),
% 12.12/1.98      inference(resolution_lifted,[status(thm)],[c_11,c_35]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_909,plain,
% 12.12/1.98      ( v3_pre_topc(sK1(sK5,X0,X1),sK5)
% 12.12/1.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X0,k1_tops_1(sK5,X1))
% 12.12/1.98      | ~ l1_pre_topc(sK5) ),
% 12.12/1.98      inference(unflattening,[status(thm)],[c_908]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_913,plain,
% 12.12/1.98      ( ~ r2_hidden(X0,k1_tops_1(sK5,X1))
% 12.12/1.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | v3_pre_topc(sK1(sK5,X0,X1),sK5) ),
% 12.12/1.98      inference(global_propositional_subsumption,
% 12.12/1.98                [status(thm)],
% 12.12/1.98                [c_909,c_34]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_914,plain,
% 12.12/1.98      ( v3_pre_topc(sK1(sK5,X0,X1),sK5)
% 12.12/1.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X0,k1_tops_1(sK5,X1)) ),
% 12.12/1.98      inference(renaming,[status(thm)],[c_913]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2530,plain,
% 12.12/1.98      ( v3_pre_topc(sK1(sK5,X0_54,X1_54),sK5)
% 12.12/1.98      | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X0_54,k1_tops_1(sK5,X1_54)) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_914]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_4691,plain,
% 12.12/1.98      ( v3_pre_topc(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK5)
% 12.12/1.98      | ~ m1_subset_1(sK0(k1_yellow19(sK5,sK6),sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(sK6,k1_tops_1(sK5,sK0(k1_yellow19(sK5,sK6),sK7))) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2530]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_30,negated_conjecture,
% 12.12/1.98      ( r2_waybel_7(sK5,sK7,sK6) | r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
% 12.12/1.98      inference(cnf_transformation,[],[f98]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2539,negated_conjecture,
% 12.12/1.98      ( r2_waybel_7(sK5,sK7,sK6) | r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_30]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3423,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
% 12.12/1.98      | r1_tarski(k1_yellow19(sK5,sK6),sK7) = iProver_top ),
% 12.12/1.98      inference(predicate_to_equality,[status(thm)],[c_2539]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_29,negated_conjecture,
% 12.12/1.98      ( ~ r2_waybel_7(sK5,sK7,sK6)
% 12.12/1.98      | ~ r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
% 12.12/1.98      inference(cnf_transformation,[],[f99]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2540,negated_conjecture,
% 12.12/1.98      ( ~ r2_waybel_7(sK5,sK7,sK6)
% 12.12/1.98      | ~ r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_29]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3422,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,sK7,sK6) != iProver_top
% 12.12/1.98      | r1_tarski(k1_yellow19(sK5,sK6),sK7) != iProver_top ),
% 12.12/1.98      inference(predicate_to_equality,[status(thm)],[c_2540]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3663,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,sK7,sK6) != iProver_top
% 12.12/1.98      | r2_waybel_7(sK5,sK7,sK6) = iProver_top ),
% 12.12/1.98      inference(superposition,[status(thm)],[c_3423,c_3422]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_43,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
% 12.12/1.98      | r1_tarski(k1_yellow19(sK5,sK6),sK7) = iProver_top ),
% 12.12/1.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_292,plain,
% 12.12/1.98      ( ~ r2_waybel_7(sK5,sK7,sK6)
% 12.12/1.98      | ~ r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
% 12.12/1.98      inference(prop_impl,[status(thm)],[c_29]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_17,plain,
% 12.12/1.98      ( r2_waybel_7(X0,X1,X2)
% 12.12/1.98      | ~ r2_hidden(sK2(X0,X1,X2),X1)
% 12.12/1.98      | ~ v2_pre_topc(X0)
% 12.12/1.98      | ~ l1_pre_topc(X0) ),
% 12.12/1.98      inference(cnf_transformation,[],[f84]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_890,plain,
% 12.12/1.98      ( r2_waybel_7(X0,X1,X2)
% 12.12/1.98      | ~ r2_hidden(sK2(X0,X1,X2),X1)
% 12.12/1.98      | ~ l1_pre_topc(X0)
% 12.12/1.98      | sK5 != X0 ),
% 12.12/1.98      inference(resolution_lifted,[status(thm)],[c_17,c_35]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_891,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,X0,X1)
% 12.12/1.98      | ~ r2_hidden(sK2(sK5,X0,X1),X0)
% 12.12/1.98      | ~ l1_pre_topc(sK5) ),
% 12.12/1.98      inference(unflattening,[status(thm)],[c_890]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_895,plain,
% 12.12/1.98      ( ~ r2_hidden(sK2(sK5,X0,X1),X0) | r2_waybel_7(sK5,X0,X1) ),
% 12.12/1.98      inference(global_propositional_subsumption,
% 12.12/1.98                [status(thm)],
% 12.12/1.98                [c_891,c_34]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_896,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,X0,X1) | ~ r2_hidden(sK2(sK5,X0,X1),X0) ),
% 12.12/1.98      inference(renaming,[status(thm)],[c_895]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_1331,plain,
% 12.12/1.98      ( ~ r2_hidden(sK2(sK5,X0,X1),X0)
% 12.12/1.98      | ~ r1_tarski(k1_yellow19(sK5,sK6),sK7)
% 12.12/1.98      | sK7 != X0
% 12.12/1.98      | sK6 != X1
% 12.12/1.98      | sK5 != sK5 ),
% 12.12/1.98      inference(resolution_lifted,[status(thm)],[c_292,c_896]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_1332,plain,
% 12.12/1.98      ( ~ r2_hidden(sK2(sK5,sK7,sK6),sK7)
% 12.12/1.98      | ~ r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
% 12.12/1.98      inference(unflattening,[status(thm)],[c_1331]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_1333,plain,
% 12.12/1.98      ( r2_hidden(sK2(sK5,sK7,sK6),sK7) != iProver_top
% 12.12/1.98      | r1_tarski(k1_yellow19(sK5,sK6),sK7) != iProver_top ),
% 12.12/1.98      inference(predicate_to_equality,[status(thm)],[c_1332]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_19,plain,
% 12.12/1.98      ( r2_waybel_7(X0,X1,X2)
% 12.12/1.98      | v3_pre_topc(sK2(X0,X1,X2),X0)
% 12.12/1.98      | ~ v2_pre_topc(X0)
% 12.12/1.98      | ~ l1_pre_topc(X0) ),
% 12.12/1.98      inference(cnf_transformation,[],[f82]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_854,plain,
% 12.12/1.98      ( r2_waybel_7(X0,X1,X2)
% 12.12/1.98      | v3_pre_topc(sK2(X0,X1,X2),X0)
% 12.12/1.98      | ~ l1_pre_topc(X0)
% 12.12/1.98      | sK5 != X0 ),
% 12.12/1.98      inference(resolution_lifted,[status(thm)],[c_19,c_35]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_855,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,X0,X1)
% 12.12/1.98      | v3_pre_topc(sK2(sK5,X0,X1),sK5)
% 12.12/1.98      | ~ l1_pre_topc(sK5) ),
% 12.12/1.98      inference(unflattening,[status(thm)],[c_854]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_859,plain,
% 12.12/1.98      ( v3_pre_topc(sK2(sK5,X0,X1),sK5) | r2_waybel_7(sK5,X0,X1) ),
% 12.12/1.98      inference(global_propositional_subsumption,
% 12.12/1.98                [status(thm)],
% 12.12/1.98                [c_855,c_34]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_860,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,X0,X1) | v3_pre_topc(sK2(sK5,X0,X1),sK5) ),
% 12.12/1.98      inference(renaming,[status(thm)],[c_859]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2533,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,X0_54,X1_54)
% 12.12/1.98      | v3_pre_topc(sK2(sK5,X0_54,X1_54),sK5) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_860]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3676,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,sK7,sK6) | v3_pre_topc(sK2(sK5,sK7,sK6),sK5) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2533]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3677,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
% 12.12/1.98      | v3_pre_topc(sK2(sK5,sK7,sK6),sK5) = iProver_top ),
% 12.12/1.98      inference(predicate_to_equality,[status(thm)],[c_3676]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_20,plain,
% 12.12/1.98      ( r2_waybel_7(X0,X1,X2)
% 12.12/1.98      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 12.12/1.98      | ~ v2_pre_topc(X0)
% 12.12/1.98      | ~ l1_pre_topc(X0) ),
% 12.12/1.98      inference(cnf_transformation,[],[f81]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_836,plain,
% 12.12/1.98      ( r2_waybel_7(X0,X1,X2)
% 12.12/1.98      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 12.12/1.98      | ~ l1_pre_topc(X0)
% 12.12/1.98      | sK5 != X0 ),
% 12.12/1.98      inference(resolution_lifted,[status(thm)],[c_20,c_35]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_837,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,X0,X1)
% 12.12/1.98      | m1_subset_1(sK2(sK5,X0,X1),k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ l1_pre_topc(sK5) ),
% 12.12/1.98      inference(unflattening,[status(thm)],[c_836]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_841,plain,
% 12.12/1.98      ( m1_subset_1(sK2(sK5,X0,X1),k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | r2_waybel_7(sK5,X0,X1) ),
% 12.12/1.98      inference(global_propositional_subsumption,
% 12.12/1.98                [status(thm)],
% 12.12/1.98                [c_837,c_34]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_842,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,X0,X1)
% 12.12/1.98      | m1_subset_1(sK2(sK5,X0,X1),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 12.12/1.98      inference(renaming,[status(thm)],[c_841]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2534,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,X0_54,X1_54)
% 12.12/1.98      | m1_subset_1(sK2(sK5,X0_54,X1_54),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_842]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3675,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,sK7,sK6)
% 12.12/1.98      | m1_subset_1(sK2(sK5,sK7,sK6),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2534]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3679,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
% 12.12/1.98      | m1_subset_1(sK2(sK5,sK7,sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 12.12/1.98      inference(predicate_to_equality,[status(thm)],[c_3675]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_18,plain,
% 12.12/1.98      ( r2_waybel_7(X0,X1,X2)
% 12.12/1.98      | r2_hidden(X2,sK2(X0,X1,X2))
% 12.12/1.98      | ~ v2_pre_topc(X0)
% 12.12/1.98      | ~ l1_pre_topc(X0) ),
% 12.12/1.98      inference(cnf_transformation,[],[f83]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_872,plain,
% 12.12/1.98      ( r2_waybel_7(X0,X1,X2)
% 12.12/1.98      | r2_hidden(X2,sK2(X0,X1,X2))
% 12.12/1.98      | ~ l1_pre_topc(X0)
% 12.12/1.98      | sK5 != X0 ),
% 12.12/1.98      inference(resolution_lifted,[status(thm)],[c_18,c_35]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_873,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,X0,X1)
% 12.12/1.98      | r2_hidden(X1,sK2(sK5,X0,X1))
% 12.12/1.98      | ~ l1_pre_topc(sK5) ),
% 12.12/1.98      inference(unflattening,[status(thm)],[c_872]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_877,plain,
% 12.12/1.98      ( r2_hidden(X1,sK2(sK5,X0,X1)) | r2_waybel_7(sK5,X0,X1) ),
% 12.12/1.98      inference(global_propositional_subsumption,
% 12.12/1.98                [status(thm)],
% 12.12/1.98                [c_873,c_34]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_878,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,X0,X1) | r2_hidden(X1,sK2(sK5,X0,X1)) ),
% 12.12/1.98      inference(renaming,[status(thm)],[c_877]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2532,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,X0_54,X1_54)
% 12.12/1.98      | r2_hidden(X1_54,sK2(sK5,X0_54,X1_54)) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_878]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3674,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,sK7,sK6) | r2_hidden(sK6,sK2(sK5,sK7,sK6)) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2532]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3681,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
% 12.12/1.98      | r2_hidden(sK6,sK2(sK5,sK7,sK6)) = iProver_top ),
% 12.12/1.98      inference(predicate_to_equality,[status(thm)],[c_3674]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_16,plain,
% 12.12/1.98      ( m1_connsp_2(X0,X1,X2)
% 12.12/1.98      | ~ v3_pre_topc(X0,X1)
% 12.12/1.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 12.12/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.12/1.98      | ~ r2_hidden(X2,X0)
% 12.12/1.98      | v2_struct_0(X1)
% 12.12/1.98      | ~ v2_pre_topc(X1)
% 12.12/1.98      | ~ l1_pre_topc(X1) ),
% 12.12/1.98      inference(cnf_transformation,[],[f78]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_36,negated_conjecture,
% 12.12/1.98      ( ~ v2_struct_0(sK5) ),
% 12.12/1.98      inference(cnf_transformation,[],[f92]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_577,plain,
% 12.12/1.98      ( m1_connsp_2(X0,X1,X2)
% 12.12/1.98      | ~ v3_pre_topc(X0,X1)
% 12.12/1.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 12.12/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.12/1.98      | ~ r2_hidden(X2,X0)
% 12.12/1.98      | ~ v2_pre_topc(X1)
% 12.12/1.98      | ~ l1_pre_topc(X1)
% 12.12/1.98      | sK5 != X1 ),
% 12.12/1.98      inference(resolution_lifted,[status(thm)],[c_16,c_36]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_578,plain,
% 12.12/1.98      ( m1_connsp_2(X0,sK5,X1)
% 12.12/1.98      | ~ v3_pre_topc(X0,sK5)
% 12.12/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 12.12/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X1,X0)
% 12.12/1.98      | ~ v2_pre_topc(sK5)
% 12.12/1.98      | ~ l1_pre_topc(sK5) ),
% 12.12/1.98      inference(unflattening,[status(thm)],[c_577]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_582,plain,
% 12.12/1.98      ( m1_connsp_2(X0,sK5,X1)
% 12.12/1.98      | ~ v3_pre_topc(X0,sK5)
% 12.12/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 12.12/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X1,X0) ),
% 12.12/1.98      inference(global_propositional_subsumption,
% 12.12/1.98                [status(thm)],
% 12.12/1.98                [c_578,c_35,c_34]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_5,plain,
% 12.12/1.98      ( m1_subset_1(X0,X1)
% 12.12/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 12.12/1.98      | ~ r2_hidden(X0,X2) ),
% 12.12/1.98      inference(cnf_transformation,[],[f67]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_598,plain,
% 12.12/1.98      ( m1_connsp_2(X0,sK5,X1)
% 12.12/1.98      | ~ v3_pre_topc(X0,sK5)
% 12.12/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X1,X0) ),
% 12.12/1.98      inference(forward_subsumption_resolution,[status(thm)],[c_582,c_5]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_27,plain,
% 12.12/1.98      ( ~ m1_connsp_2(X0,X1,X2)
% 12.12/1.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 12.12/1.98      | r2_hidden(X0,k1_yellow19(X1,X2))
% 12.12/1.98      | v2_struct_0(X1)
% 12.12/1.98      | ~ v2_pre_topc(X1)
% 12.12/1.98      | ~ l1_pre_topc(X1) ),
% 12.12/1.98      inference(cnf_transformation,[],[f91]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_556,plain,
% 12.12/1.98      ( ~ m1_connsp_2(X0,X1,X2)
% 12.12/1.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 12.12/1.98      | r2_hidden(X0,k1_yellow19(X1,X2))
% 12.12/1.98      | ~ v2_pre_topc(X1)
% 12.12/1.98      | ~ l1_pre_topc(X1)
% 12.12/1.98      | sK5 != X1 ),
% 12.12/1.98      inference(resolution_lifted,[status(thm)],[c_27,c_36]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_557,plain,
% 12.12/1.98      ( ~ m1_connsp_2(X0,sK5,X1)
% 12.12/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 12.12/1.98      | r2_hidden(X0,k1_yellow19(sK5,X1))
% 12.12/1.98      | ~ v2_pre_topc(sK5)
% 12.12/1.98      | ~ l1_pre_topc(sK5) ),
% 12.12/1.98      inference(unflattening,[status(thm)],[c_556]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_561,plain,
% 12.12/1.98      ( ~ m1_connsp_2(X0,sK5,X1)
% 12.12/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 12.12/1.98      | r2_hidden(X0,k1_yellow19(sK5,X1)) ),
% 12.12/1.98      inference(global_propositional_subsumption,
% 12.12/1.98                [status(thm)],
% 12.12/1.98                [c_557,c_35,c_34]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_1424,plain,
% 12.12/1.98      ( ~ v3_pre_topc(X0,sK5)
% 12.12/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 12.12/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X1,X0)
% 12.12/1.98      | r2_hidden(X0,k1_yellow19(sK5,X1)) ),
% 12.12/1.98      inference(resolution,[status(thm)],[c_598,c_561]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_1438,plain,
% 12.12/1.98      ( ~ v3_pre_topc(X0,sK5)
% 12.12/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X1,X0)
% 12.12/1.98      | r2_hidden(X0,k1_yellow19(sK5,X1)) ),
% 12.12/1.98      inference(forward_subsumption_resolution,
% 12.12/1.98                [status(thm)],
% 12.12/1.98                [c_1424,c_5]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2523,plain,
% 12.12/1.98      ( ~ v3_pre_topc(X0_54,sK5)
% 12.12/1.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X1_54,X0_54)
% 12.12/1.98      | r2_hidden(X0_54,k1_yellow19(sK5,X1_54)) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_1438]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3783,plain,
% 12.12/1.98      ( ~ v3_pre_topc(sK2(sK5,sK7,sK6),sK5)
% 12.12/1.98      | ~ m1_subset_1(sK2(sK5,sK7,sK6),k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6))
% 12.12/1.98      | ~ r2_hidden(sK6,sK2(sK5,sK7,sK6)) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2523]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3787,plain,
% 12.12/1.98      ( v3_pre_topc(sK2(sK5,sK7,sK6),sK5) != iProver_top
% 12.12/1.98      | m1_subset_1(sK2(sK5,sK7,sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 12.12/1.98      | r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6)) = iProver_top
% 12.12/1.98      | r2_hidden(sK6,sK2(sK5,sK7,sK6)) != iProver_top ),
% 12.12/1.98      inference(predicate_to_equality,[status(thm)],[c_3783]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2,plain,
% 12.12/1.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 12.12/1.98      inference(cnf_transformation,[],[f62]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2549,plain,
% 12.12/1.98      ( ~ r2_hidden(X0_54,X1_54)
% 12.12/1.98      | r2_hidden(X0_54,X2_54)
% 12.12/1.98      | ~ r1_tarski(X1_54,X2_54) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_2]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3989,plain,
% 12.12/1.98      ( r2_hidden(sK2(sK5,sK7,sK6),X0_54)
% 12.12/1.98      | ~ r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6))
% 12.12/1.98      | ~ r1_tarski(k1_yellow19(sK5,sK6),X0_54) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2549]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3990,plain,
% 12.12/1.98      ( r2_hidden(sK2(sK5,sK7,sK6),X0_54) = iProver_top
% 12.12/1.98      | r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6)) != iProver_top
% 12.12/1.98      | r1_tarski(k1_yellow19(sK5,sK6),X0_54) != iProver_top ),
% 12.12/1.98      inference(predicate_to_equality,[status(thm)],[c_3989]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3992,plain,
% 12.12/1.98      ( r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6)) != iProver_top
% 12.12/1.98      | r2_hidden(sK2(sK5,sK7,sK6),sK7) = iProver_top
% 12.12/1.98      | r1_tarski(k1_yellow19(sK5,sK6),sK7) != iProver_top ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_3990]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_4293,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,sK7,sK6) = iProver_top ),
% 12.12/1.98      inference(global_propositional_subsumption,
% 12.12/1.98                [status(thm)],
% 12.12/1.98                [c_3663,c_43,c_1333,c_3677,c_3679,c_3681,c_3787,c_3992]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_4295,plain,
% 12.12/1.98      ( r2_waybel_7(sK5,sK7,sK6) ),
% 12.12/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_4293]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_28,plain,
% 12.12/1.98      ( m1_connsp_2(X0,X1,X2)
% 12.12/1.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 12.12/1.98      | ~ r2_hidden(X0,k1_yellow19(X1,X2))
% 12.12/1.98      | v2_struct_0(X1)
% 12.12/1.98      | ~ v2_pre_topc(X1)
% 12.12/1.98      | ~ l1_pre_topc(X1) ),
% 12.12/1.98      inference(cnf_transformation,[],[f90]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_535,plain,
% 12.12/1.98      ( m1_connsp_2(X0,X1,X2)
% 12.12/1.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 12.12/1.98      | ~ r2_hidden(X0,k1_yellow19(X1,X2))
% 12.12/1.98      | ~ v2_pre_topc(X1)
% 12.12/1.98      | ~ l1_pre_topc(X1)
% 12.12/1.98      | sK5 != X1 ),
% 12.12/1.98      inference(resolution_lifted,[status(thm)],[c_28,c_36]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_536,plain,
% 12.12/1.98      ( m1_connsp_2(X0,sK5,X1)
% 12.12/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 12.12/1.98      | ~ r2_hidden(X0,k1_yellow19(sK5,X1))
% 12.12/1.98      | ~ v2_pre_topc(sK5)
% 12.12/1.98      | ~ l1_pre_topc(sK5) ),
% 12.12/1.98      inference(unflattening,[status(thm)],[c_535]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_540,plain,
% 12.12/1.98      ( m1_connsp_2(X0,sK5,X1)
% 12.12/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 12.12/1.98      | ~ r2_hidden(X0,k1_yellow19(sK5,X1)) ),
% 12.12/1.98      inference(global_propositional_subsumption,
% 12.12/1.98                [status(thm)],
% 12.12/1.98                [c_536,c_35,c_34]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_14,plain,
% 12.12/1.98      ( ~ m1_connsp_2(X0,X1,X2)
% 12.12/1.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 12.12/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.12/1.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 12.12/1.98      | v2_struct_0(X1)
% 12.12/1.98      | ~ v2_pre_topc(X1)
% 12.12/1.98      | ~ l1_pre_topc(X1) ),
% 12.12/1.98      inference(cnf_transformation,[],[f75]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_15,plain,
% 12.12/1.98      ( ~ m1_connsp_2(X0,X1,X2)
% 12.12/1.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 12.12/1.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.12/1.98      | v2_struct_0(X1)
% 12.12/1.98      | ~ v2_pre_topc(X1)
% 12.12/1.98      | ~ l1_pre_topc(X1) ),
% 12.12/1.98      inference(cnf_transformation,[],[f77]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_223,plain,
% 12.12/1.98      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 12.12/1.98      | ~ m1_connsp_2(X0,X1,X2)
% 12.12/1.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 12.12/1.98      | v2_struct_0(X1)
% 12.12/1.98      | ~ v2_pre_topc(X1)
% 12.12/1.98      | ~ l1_pre_topc(X1) ),
% 12.12/1.98      inference(global_propositional_subsumption,
% 12.12/1.98                [status(thm)],
% 12.12/1.98                [c_14,c_15]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_224,plain,
% 12.12/1.98      ( ~ m1_connsp_2(X0,X1,X2)
% 12.12/1.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 12.12/1.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 12.12/1.98      | v2_struct_0(X1)
% 12.12/1.98      | ~ v2_pre_topc(X1)
% 12.12/1.98      | ~ l1_pre_topc(X1) ),
% 12.12/1.98      inference(renaming,[status(thm)],[c_223]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_514,plain,
% 12.12/1.98      ( ~ m1_connsp_2(X0,X1,X2)
% 12.12/1.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 12.12/1.98      | r2_hidden(X2,k1_tops_1(X1,X0))
% 12.12/1.98      | ~ v2_pre_topc(X1)
% 12.12/1.98      | ~ l1_pre_topc(X1)
% 12.12/1.98      | sK5 != X1 ),
% 12.12/1.98      inference(resolution_lifted,[status(thm)],[c_224,c_36]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_515,plain,
% 12.12/1.98      ( ~ m1_connsp_2(X0,sK5,X1)
% 12.12/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 12.12/1.98      | r2_hidden(X1,k1_tops_1(sK5,X0))
% 12.12/1.98      | ~ v2_pre_topc(sK5)
% 12.12/1.98      | ~ l1_pre_topc(sK5) ),
% 12.12/1.98      inference(unflattening,[status(thm)],[c_514]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_519,plain,
% 12.12/1.98      ( ~ m1_connsp_2(X0,sK5,X1)
% 12.12/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 12.12/1.98      | r2_hidden(X1,k1_tops_1(sK5,X0)) ),
% 12.12/1.98      inference(global_propositional_subsumption,
% 12.12/1.98                [status(thm)],
% 12.12/1.98                [c_515,c_35,c_34]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_1483,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 12.12/1.98      | ~ r2_hidden(X1,k1_yellow19(sK5,X0))
% 12.12/1.98      | r2_hidden(X0,k1_tops_1(sK5,X1)) ),
% 12.12/1.98      inference(resolution,[status(thm)],[c_540,c_519]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2520,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 12.12/1.98      | ~ r2_hidden(X1_54,k1_yellow19(sK5,X0_54))
% 12.12/1.98      | r2_hidden(X0_54,k1_tops_1(sK5,X1_54)) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_1483]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3828,plain,
% 12.12/1.98      ( ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 12.12/1.98      | ~ r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),k1_yellow19(sK5,sK6))
% 12.12/1.98      | r2_hidden(sK6,k1_tops_1(sK5,sK0(k1_yellow19(sK5,sK6),sK7))) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2520]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_606,plain,
% 12.12/1.98      ( ~ m1_connsp_2(X0,X1,X2)
% 12.12/1.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 12.12/1.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.12/1.98      | ~ v2_pre_topc(X1)
% 12.12/1.98      | ~ l1_pre_topc(X1)
% 12.12/1.98      | sK5 != X1 ),
% 12.12/1.98      inference(resolution_lifted,[status(thm)],[c_15,c_36]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_607,plain,
% 12.12/1.98      ( ~ m1_connsp_2(X0,sK5,X1)
% 12.12/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 12.12/1.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ v2_pre_topc(sK5)
% 12.12/1.98      | ~ l1_pre_topc(sK5) ),
% 12.12/1.98      inference(unflattening,[status(thm)],[c_606]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_611,plain,
% 12.12/1.98      ( ~ m1_connsp_2(X0,sK5,X1)
% 12.12/1.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 12.12/1.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 12.12/1.98      inference(global_propositional_subsumption,
% 12.12/1.98                [status(thm)],
% 12.12/1.98                [c_607,c_35,c_34]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_1468,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 12.12/1.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X1,k1_yellow19(sK5,X0)) ),
% 12.12/1.98      inference(resolution,[status(thm)],[c_540,c_611]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2521,plain,
% 12.12/1.98      ( ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 12.12/1.98      | m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ r2_hidden(X1_54,k1_yellow19(sK5,X0_54)) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_1468]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3829,plain,
% 12.12/1.98      ( m1_subset_1(sK0(k1_yellow19(sK5,sK6),sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 12.12/1.98      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 12.12/1.98      | ~ r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),k1_yellow19(sK5,sK6)) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2521]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_1,plain,
% 12.12/1.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 12.12/1.98      inference(cnf_transformation,[],[f63]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2550,plain,
% 12.12/1.98      ( r2_hidden(sK0(X0_54,X1_54),X0_54) | r1_tarski(X0_54,X1_54) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_1]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_3590,plain,
% 12.12/1.98      ( r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),k1_yellow19(sK5,sK6))
% 12.12/1.98      | r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2550]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_7,plain,
% 12.12/1.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 12.12/1.98      inference(cnf_transformation,[],[f69]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_6,plain,
% 12.12/1.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 12.12/1.98      inference(cnf_transformation,[],[f68]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_500,plain,
% 12.12/1.98      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 12.12/1.98      inference(resolution,[status(thm)],[c_7,c_6]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_1063,plain,
% 12.12/1.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK5 != X0 ),
% 12.12/1.98      inference(resolution_lifted,[status(thm)],[c_500,c_34]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_1064,plain,
% 12.12/1.98      ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
% 12.12/1.98      inference(unflattening,[status(thm)],[c_1063]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2525,plain,
% 12.12/1.98      ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
% 12.12/1.98      inference(subtyping,[status(esa)],[c_1064]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2553,plain,( X0_54 = X0_54 ),theory(equality) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_2588,plain,
% 12.12/1.98      ( sK7 = sK7 ),
% 12.12/1.98      inference(instantiation,[status(thm)],[c_2553]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_31,negated_conjecture,
% 12.12/1.98      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5)))))) ),
% 12.12/1.98      inference(cnf_transformation,[],[f105]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_32,negated_conjecture,
% 12.12/1.98      ( v13_waybel_0(sK7,k3_lattice3(k1_lattice3(k2_struct_0(sK5)))) ),
% 12.12/1.98      inference(cnf_transformation,[],[f106]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(c_33,negated_conjecture,
% 12.12/1.98      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 12.12/1.98      inference(cnf_transformation,[],[f95]) ).
% 12.12/1.98  
% 12.12/1.98  cnf(contradiction,plain,
% 12.12/1.98      ( $false ),
% 12.12/1.98      inference(minisat,
% 12.12/1.98                [status(thm)],
% 12.12/1.98                [c_35570,c_31610,c_18157,c_17319,c_10222,c_7425,c_7422,
% 12.12/1.98                 c_6461,c_5443,c_4804,c_4706,c_4707,c_4708,c_4691,c_4295,
% 12.12/1.98                 c_3828,c_3829,c_3590,c_2525,c_2588,c_29,c_31,c_32,c_33]) ).
% 12.12/1.98  
% 12.12/1.98  
% 12.12/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 12.12/1.98  
% 12.12/1.98  ------                               Statistics
% 12.12/1.98  
% 12.12/1.98  ------ Selected
% 12.12/1.98  
% 12.12/1.98  total_time:                             1.474
% 12.12/1.98  
%------------------------------------------------------------------------------
