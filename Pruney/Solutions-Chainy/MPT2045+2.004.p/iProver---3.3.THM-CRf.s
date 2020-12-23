%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:03 EST 2020

% Result     : Theorem 7.29s
% Output     : CNFRefutation 7.29s
% Verified   : 
% Statistics : Number of formulae       :  247 ( 907 expanded)
%              Number of clauses        :  161 ( 217 expanded)
%              Number of leaves         :   24 ( 239 expanded)
%              Depth                    :   19
%              Number of atoms          : 1112 (6993 expanded)
%              Number of equality atoms :  102 ( 118 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
     => ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) )
           => r2_hidden(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(flattening,[],[f25])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
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

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f45,f46])).

fof(f75,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f94,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) ) ),
    inference(definition_unfolding,[],[f75,f69,f69])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
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

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,
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

fof(f54,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f50,f53,f52,f51])).

fof(f83,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f88,plain,
    ( r1_tarski(k1_yellow19(sK5,sK6),sK7)
    | r2_waybel_7(sK5,sK7,sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,
    ( ~ r1_tarski(k1_yellow19(sK5,sK6),sK7)
    | ~ r2_waybel_7(sK5,sK7,sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | v3_pre_topc(sK2(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | r2_hidden(X2,sK2(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
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
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
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
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
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

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK1(X0,X1,X2))
                    & r1_tarski(sK1(X0,X1,X2),X2)
                    & v3_pre_topc(sK1(X0,X1,X2),X0)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK1(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK1(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK5))))) ),
    inference(cnf_transformation,[],[f54])).

fof(f95,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5)))))) ),
    inference(definition_unfolding,[],[f87,f69])).

fof(f86,plain,(
    v13_waybel_0(sK7,k3_yellow_1(k2_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f54])).

fof(f96,plain,(
    v13_waybel_0(sK7,k3_lattice3(k1_lattice3(k2_struct_0(sK5)))) ),
    inference(definition_unfolding,[],[f86,f69])).

cnf(c_2848,plain,
    ( ~ r1_tarski(X0_53,X1_53)
    | r1_tarski(X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_5659,plain,
    ( ~ r1_tarski(X0_53,X1_53)
    | r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),X2_53)
    | X2_53 != X1_53
    | sK0(k1_yellow19(sK5,sK6),sK7) != X0_53 ),
    inference(instantiation,[status(thm)],[c_2848])).

cnf(c_12448,plain,
    ( ~ r1_tarski(X0_53,X1_53)
    | r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),k2_struct_0(sK5))
    | sK0(k1_yellow19(sK5,sK6),sK7) != X0_53
    | k2_struct_0(sK5) != X1_53 ),
    inference(instantiation,[status(thm)],[c_5659])).

cnf(c_14464,plain,
    ( ~ r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),X0_53)
    | r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),k2_struct_0(sK5))
    | sK0(k1_yellow19(sK5,sK6),sK7) != sK0(k1_yellow19(sK5,sK6),sK7)
    | k2_struct_0(sK5) != X0_53 ),
    inference(instantiation,[status(thm)],[c_12448])).

cnf(c_33381,plain,
    ( ~ r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),u1_struct_0(sK5))
    | r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),k2_struct_0(sK5))
    | sK0(k1_yellow19(sK5,sK6),sK7) != sK0(k1_yellow19(sK5,sK6),sK7)
    | k2_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_14464])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2842,plain,
    ( ~ r2_hidden(sK0(X0_53,X1_53),X1_53)
    | r1_tarski(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_30006,plain,
    ( ~ r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),sK7)
    | r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_2842])).

cnf(c_23,plain,
    ( ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X3,X0)
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2833,plain,
    ( ~ v13_waybel_0(X0_53,k3_lattice3(k1_lattice3(X1_53)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1_53)))))
    | ~ r2_hidden(X2_53,X0_53)
    | r2_hidden(X3_53,X0_53)
    | ~ r1_tarski(X3_53,X1_53)
    | ~ r1_tarski(X2_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_8361,plain,
    ( ~ v13_waybel_0(X0_53,k3_lattice3(k1_lattice3(X1_53)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1_53)))))
    | r2_hidden(X2_53,X0_53)
    | ~ r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),X0_53)
    | ~ r1_tarski(X2_53,X1_53)
    | ~ r1_tarski(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),X2_53) ),
    inference(instantiation,[status(thm)],[c_2833])).

cnf(c_23198,plain,
    ( ~ v13_waybel_0(sK7,k3_lattice3(k1_lattice3(k2_struct_0(sK5))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))))
    | r2_hidden(X0_53,sK7)
    | ~ r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK7)
    | ~ r1_tarski(X0_53,k2_struct_0(sK5))
    | ~ r1_tarski(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),X0_53) ),
    inference(instantiation,[status(thm)],[c_8361])).

cnf(c_28010,plain,
    ( ~ v13_waybel_0(sK7,k3_lattice3(k1_lattice3(k2_struct_0(sK5))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))))
    | ~ r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK7)
    | r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),sK7)
    | ~ r1_tarski(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK0(k1_yellow19(sK5,sK6),sK7))
    | ~ r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),k2_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_23198])).

cnf(c_2847,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_4510,plain,
    ( X0_53 != X1_53
    | X0_53 = u1_struct_0(sK5)
    | u1_struct_0(sK5) != X1_53 ),
    inference(instantiation,[status(thm)],[c_2847])).

cnf(c_6081,plain,
    ( X0_53 = u1_struct_0(sK5)
    | X0_53 != k2_struct_0(sK5)
    | u1_struct_0(sK5) != k2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_4510])).

cnf(c_6834,plain,
    ( u1_struct_0(sK5) != k2_struct_0(sK5)
    | k2_struct_0(sK5) = u1_struct_0(sK5)
    | k2_struct_0(sK5) != k2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_6081])).

cnf(c_18,plain,
    ( ~ r2_waybel_7(X0,X1,X2)
    | ~ v3_pre_topc(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_876,plain,
    ( ~ r2_waybel_7(X0,X1,X2)
    | ~ v3_pre_topc(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,X1)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_32])).

cnf(c_877,plain,
    ( ~ r2_waybel_7(sK5,X0,X1)
    | ~ v3_pre_topc(X2,sK5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X2,X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_876])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_879,plain,
    ( r2_hidden(X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(X2,sK5)
    | ~ r2_waybel_7(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_877,c_31])).

cnf(c_880,plain,
    ( ~ r2_waybel_7(sK5,X0,X1)
    | ~ v3_pre_topc(X2,sK5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X2,X0) ),
    inference(renaming,[status(thm)],[c_879])).

cnf(c_2818,plain,
    ( ~ r2_waybel_7(sK5,X0_53,X1_53)
    | ~ v3_pre_topc(X2_53,sK5)
    | ~ m1_subset_1(X2_53,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1_53,X2_53)
    | r2_hidden(X2_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_880])).

cnf(c_5179,plain,
    ( ~ r2_waybel_7(sK5,X0_53,sK6)
    | ~ v3_pre_topc(X1_53,sK5)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(X1_53,X0_53)
    | ~ r2_hidden(sK6,X1_53) ),
    inference(instantiation,[status(thm)],[c_2818])).

cnf(c_6802,plain,
    ( ~ r2_waybel_7(sK5,X0_53,sK6)
    | ~ v3_pre_topc(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK5)
    | ~ m1_subset_1(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),X0_53)
    | ~ r2_hidden(sK6,sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7))) ),
    inference(instantiation,[status(thm)],[c_5179])).

cnf(c_6804,plain,
    ( ~ r2_waybel_7(sK5,sK7,sK6)
    | ~ v3_pre_topc(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK5)
    | ~ m1_subset_1(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK7)
    | ~ r2_hidden(sK6,sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7))) ),
    inference(instantiation,[status(thm)],[c_6802])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2838,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | r1_tarski(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_5222,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(X0_53,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2838])).

cnf(c_6481,plain,
    ( ~ m1_subset_1(sK0(k1_yellow19(sK5,sK6),sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_5222])).

cnf(c_27,negated_conjecture,
    ( r2_waybel_7(sK5,sK7,sK6)
    | r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2831,negated_conjecture,
    ( r2_waybel_7(sK5,sK7,sK6)
    | r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_3681,plain,
    ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
    | r1_tarski(k1_yellow19(sK5,sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2831])).

cnf(c_24,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X0,k1_yellow19(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_732,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X0,k1_yellow19(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_733,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X0,k1_yellow19(sK5,X1))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_737,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X0,k1_yellow19(sK5,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_733,c_32,c_31])).

cnf(c_2822,plain,
    ( ~ m1_connsp_2(X0_53,sK5,X1_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
    | r2_hidden(X0_53,k1_yellow19(sK5,X1_53)) ),
    inference(subtyping,[status(esa)],[c_737])).

cnf(c_3690,plain,
    ( m1_connsp_2(X0_53,sK5,X1_53) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0_53,k1_yellow19(sK5,X1_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2822])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_477,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_6,c_5])).

cnf(c_989,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_477,c_31])).

cnf(c_990,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_989])).

cnf(c_2813,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
    inference(subtyping,[status(esa)],[c_990])).

cnf(c_3762,plain,
    ( m1_connsp_2(X0_53,sK5,X1_53) != iProver_top
    | m1_subset_1(X1_53,k2_struct_0(sK5)) != iProver_top
    | r2_hidden(X0_53,k1_yellow19(sK5,X1_53)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3690,c_2813])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2840,plain,
    ( ~ r2_hidden(X0_53,X1_53)
    | r2_hidden(X0_53,X2_53)
    | ~ r1_tarski(X1_53,X2_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3672,plain,
    ( r2_hidden(X0_53,X1_53) != iProver_top
    | r2_hidden(X0_53,X2_53) = iProver_top
    | r1_tarski(X1_53,X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2840])).

cnf(c_4416,plain,
    ( m1_connsp_2(X0_53,sK5,X1_53) != iProver_top
    | m1_subset_1(X1_53,k2_struct_0(sK5)) != iProver_top
    | r2_hidden(X0_53,X2_53) = iProver_top
    | r1_tarski(k1_yellow19(sK5,X1_53),X2_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_3762,c_3672])).

cnf(c_6138,plain,
    ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
    | m1_connsp_2(X0_53,sK5,sK6) != iProver_top
    | m1_subset_1(sK6,k2_struct_0(sK5)) != iProver_top
    | r2_hidden(X0_53,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3681,c_4416])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_37,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_40,plain,
    ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
    | r1_tarski(k1_yellow19(sK5,sK6),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( ~ r2_waybel_7(sK5,sK7,sK6)
    | ~ r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_286,plain,
    ( ~ r2_waybel_7(sK5,sK7,sK6)
    | ~ r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_14,plain,
    ( r2_waybel_7(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_953,plain,
    ( r2_waybel_7(X0,X1,X2)
    | ~ r2_hidden(sK2(X0,X1,X2),X1)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_32])).

cnf(c_954,plain,
    ( r2_waybel_7(sK5,X0,X1)
    | ~ r2_hidden(sK2(sK5,X0,X1),X0)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_953])).

cnf(c_958,plain,
    ( ~ r2_hidden(sK2(sK5,X0,X1),X0)
    | r2_waybel_7(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_954,c_31])).

cnf(c_959,plain,
    ( r2_waybel_7(sK5,X0,X1)
    | ~ r2_hidden(sK2(sK5,X0,X1),X0) ),
    inference(renaming,[status(thm)],[c_958])).

cnf(c_1089,plain,
    ( ~ r2_hidden(sK2(sK5,X0,X1),X0)
    | ~ r1_tarski(k1_yellow19(sK5,sK6),sK7)
    | sK7 != X0
    | sK6 != X1
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_286,c_959])).

cnf(c_1090,plain,
    ( ~ r2_hidden(sK2(sK5,sK7,sK6),sK7)
    | ~ r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
    inference(unflattening,[status(thm)],[c_1089])).

cnf(c_1091,plain,
    ( r2_hidden(sK2(sK5,sK7,sK6),sK7) != iProver_top
    | r1_tarski(k1_yellow19(sK5,sK6),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1090])).

cnf(c_16,plain,
    ( r2_waybel_7(X0,X1,X2)
    | v3_pre_topc(sK2(X0,X1,X2),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_917,plain,
    ( r2_waybel_7(X0,X1,X2)
    | v3_pre_topc(sK2(X0,X1,X2),X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_918,plain,
    ( r2_waybel_7(sK5,X0,X1)
    | v3_pre_topc(sK2(sK5,X0,X1),sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_917])).

cnf(c_922,plain,
    ( v3_pre_topc(sK2(sK5,X0,X1),sK5)
    | r2_waybel_7(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_918,c_31])).

cnf(c_923,plain,
    ( r2_waybel_7(sK5,X0,X1)
    | v3_pre_topc(sK2(sK5,X0,X1),sK5) ),
    inference(renaming,[status(thm)],[c_922])).

cnf(c_2816,plain,
    ( r2_waybel_7(sK5,X0_53,X1_53)
    | v3_pre_topc(sK2(sK5,X0_53,X1_53),sK5) ),
    inference(subtyping,[status(esa)],[c_923])).

cnf(c_4133,plain,
    ( r2_waybel_7(sK5,sK7,sK6)
    | v3_pre_topc(sK2(sK5,sK7,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_2816])).

cnf(c_4134,plain,
    ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
    | v3_pre_topc(sK2(sK5,sK7,sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4133])).

cnf(c_17,plain,
    ( r2_waybel_7(X0,X1,X2)
    | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_899,plain,
    ( r2_waybel_7(X0,X1,X2)
    | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_32])).

cnf(c_900,plain,
    ( r2_waybel_7(sK5,X0,X1)
    | m1_subset_1(sK2(sK5,X0,X1),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_899])).

cnf(c_904,plain,
    ( m1_subset_1(sK2(sK5,X0,X1),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_waybel_7(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_900,c_31])).

cnf(c_905,plain,
    ( r2_waybel_7(sK5,X0,X1)
    | m1_subset_1(sK2(sK5,X0,X1),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(renaming,[status(thm)],[c_904])).

cnf(c_2817,plain,
    ( r2_waybel_7(sK5,X0_53,X1_53)
    | m1_subset_1(sK2(sK5,X0_53,X1_53),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_905])).

cnf(c_4132,plain,
    ( r2_waybel_7(sK5,sK7,sK6)
    | m1_subset_1(sK2(sK5,sK7,sK6),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_2817])).

cnf(c_4136,plain,
    ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
    | m1_subset_1(sK2(sK5,sK7,sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4132])).

cnf(c_15,plain,
    ( r2_waybel_7(X0,X1,X2)
    | r2_hidden(X2,sK2(X0,X1,X2))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_935,plain,
    ( r2_waybel_7(X0,X1,X2)
    | r2_hidden(X2,sK2(X0,X1,X2))
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_936,plain,
    ( r2_waybel_7(sK5,X0,X1)
    | r2_hidden(X1,sK2(sK5,X0,X1))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_935])).

cnf(c_940,plain,
    ( r2_hidden(X1,sK2(sK5,X0,X1))
    | r2_waybel_7(sK5,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_936,c_31])).

cnf(c_941,plain,
    ( r2_waybel_7(sK5,X0,X1)
    | r2_hidden(X1,sK2(sK5,X0,X1)) ),
    inference(renaming,[status(thm)],[c_940])).

cnf(c_2815,plain,
    ( r2_waybel_7(sK5,X0_53,X1_53)
    | r2_hidden(X1_53,sK2(sK5,X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_941])).

cnf(c_4131,plain,
    ( r2_waybel_7(sK5,sK7,sK6)
    | r2_hidden(sK6,sK2(sK5,sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_2815])).

cnf(c_4138,plain,
    ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
    | r2_hidden(sK6,sK2(sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4131])).

cnf(c_8,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_786,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_33])).

cnf(c_787,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_786])).

cnf(c_791,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_787,c_32,c_31])).

cnf(c_2820,plain,
    ( m1_connsp_2(X0_53,sK5,X1_53)
    | ~ v3_pre_topc(X0_53,sK5)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_791])).

cnf(c_4242,plain,
    ( m1_connsp_2(sK2(sK5,sK7,sK6),sK5,sK6)
    | ~ v3_pre_topc(sK2(sK5,sK7,sK6),sK5)
    | ~ m1_subset_1(sK2(sK5,sK7,sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(sK6,sK2(sK5,sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_2820])).

cnf(c_4243,plain,
    ( m1_connsp_2(sK2(sK5,sK7,sK6),sK5,sK6) = iProver_top
    | v3_pre_topc(sK2(sK5,sK7,sK6),sK5) != iProver_top
    | m1_subset_1(sK2(sK5,sK7,sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK6,sK2(sK5,sK7,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4242])).

cnf(c_4393,plain,
    ( ~ m1_connsp_2(sK2(sK5,sK7,sK6),sK5,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_2822])).

cnf(c_4397,plain,
    ( m1_connsp_2(sK2(sK5,sK7,sK6),sK5,sK6) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4393])).

cnf(c_4913,plain,
    ( r2_hidden(sK2(sK5,sK7,sK6),X0_53)
    | ~ r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6))
    | ~ r1_tarski(k1_yellow19(sK5,sK6),X0_53) ),
    inference(instantiation,[status(thm)],[c_2840])).

cnf(c_4914,plain,
    ( r2_hidden(sK2(sK5,sK7,sK6),X0_53) = iProver_top
    | r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6)) != iProver_top
    | r1_tarski(k1_yellow19(sK5,sK6),X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4913])).

cnf(c_4916,plain,
    ( r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6)) != iProver_top
    | r2_hidden(sK2(sK5,sK7,sK6),sK7) = iProver_top
    | r1_tarski(k1_yellow19(sK5,sK6),sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4914])).

cnf(c_6253,plain,
    ( r2_waybel_7(sK5,sK7,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6138,c_37,c_40,c_1091,c_4134,c_4136,c_4138,c_4243,c_4397,c_4916])).

cnf(c_6255,plain,
    ( r2_waybel_7(sK5,sK7,sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6253])).

cnf(c_2844,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_5652,plain,
    ( sK0(k1_yellow19(sK5,sK6),sK7) = sK0(k1_yellow19(sK5,sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_2844])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,sK1(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_7,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_224,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,sK1(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_7])).

cnf(c_225,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,sK1(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_224])).

cnf(c_627,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,sK1(X1,X2,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_225,c_33])).

cnf(c_628,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,sK1(sK5,X1,X0))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_627])).

cnf(c_632,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,sK1(sK5,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_628,c_32,c_31])).

cnf(c_2827,plain,
    ( ~ m1_connsp_2(X0_53,sK5,X1_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
    | r2_hidden(X1_53,sK1(sK5,X1_53,X0_53)) ),
    inference(subtyping,[status(esa)],[c_632])).

cnf(c_5402,plain,
    ( ~ m1_connsp_2(sK0(k1_yellow19(sK5,sK6),sK7),sK5,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | r2_hidden(sK6,sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7))) ),
    inference(instantiation,[status(thm)],[c_2827])).

cnf(c_11,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X2,X0),X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK1(X1,X2,X0),X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_7])).

cnf(c_218,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r1_tarski(sK1(X1,X2,X0),X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_217])).

cnf(c_648,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_218,c_33])).

cnf(c_649,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r1_tarski(sK1(sK5,X1,X0),X0)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_653,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r1_tarski(sK1(sK5,X1,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_649,c_32,c_31])).

cnf(c_2826,plain,
    ( ~ m1_connsp_2(X0_53,sK5,X1_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
    | r1_tarski(sK1(sK5,X1_53,X0_53),X0_53) ),
    inference(subtyping,[status(esa)],[c_653])).

cnf(c_5403,plain,
    ( ~ m1_connsp_2(sK0(k1_yellow19(sK5,sK6),sK7),sK5,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | r1_tarski(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK0(k1_yellow19(sK5,sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_2826])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_210,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_7])).

cnf(c_211,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_669,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_211,c_33])).

cnf(c_670,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | v3_pre_topc(sK1(sK5,X1,X0),sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_674,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | v3_pre_topc(sK1(sK5,X1,X0),sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_670,c_32,c_31])).

cnf(c_2825,plain,
    ( ~ m1_connsp_2(X0_53,sK5,X1_53)
    | v3_pre_topc(sK1(sK5,X1_53,X0_53),sK5)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_674])).

cnf(c_5404,plain,
    ( ~ m1_connsp_2(sK0(k1_yellow19(sK5,sK6),sK7),sK5,sK6)
    | v3_pre_topc(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK5)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2825])).

cnf(c_13,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_203,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_7])).

cnf(c_204,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_203])).

cnf(c_690,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_204,c_33])).

cnf(c_691,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X1,X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_690])).

cnf(c_695,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X1,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_691,c_32,c_31])).

cnf(c_2824,plain,
    ( ~ m1_connsp_2(X0_53,sK5,X1_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
    | m1_subset_1(sK1(sK5,X1_53,X0_53),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_695])).

cnf(c_5405,plain,
    ( ~ m1_connsp_2(sK0(k1_yellow19(sK5,sK6),sK7),sK5,sK6)
    | m1_subset_1(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2824])).

cnf(c_813,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_33])).

cnf(c_814,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_813])).

cnf(c_818,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_814,c_32,c_31])).

cnf(c_2819,plain,
    ( ~ m1_connsp_2(X0_53,sK5,X1_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_818])).

cnf(c_5407,plain,
    ( ~ m1_connsp_2(sK0(k1_yellow19(sK5,sK6),sK7),sK5,sK6)
    | m1_subset_1(sK0(k1_yellow19(sK5,sK6),sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2819])).

cnf(c_25,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k1_yellow19(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_711,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k1_yellow19(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_712,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X0,k1_yellow19(sK5,X1))
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_711])).

cnf(c_716,plain,
    ( m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ r2_hidden(X0,k1_yellow19(sK5,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_712,c_32,c_31])).

cnf(c_2823,plain,
    ( m1_connsp_2(X0_53,sK5,X1_53)
    | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
    | ~ r2_hidden(X0_53,k1_yellow19(sK5,X1_53)) ),
    inference(subtyping,[status(esa)],[c_716])).

cnf(c_4282,plain,
    ( m1_connsp_2(sK0(k1_yellow19(sK5,sK6),sK7),sK5,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),k1_yellow19(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_2823])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2841,plain,
    ( r2_hidden(sK0(X0_53,X1_53),X0_53)
    | r1_tarski(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_4015,plain,
    ( r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),k1_yellow19(sK5,sK6))
    | r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_2841])).

cnf(c_2845,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_2880,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2845])).

cnf(c_2852,plain,
    ( X0_54 != X1_54
    | k2_struct_0(X0_54) = k2_struct_0(X1_54) ),
    theory(equality)).

cnf(c_2867,plain,
    ( sK5 != sK5
    | k2_struct_0(sK5) = k2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2852])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5)))))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_29,negated_conjecture,
    ( v13_waybel_0(sK7,k3_lattice3(k1_lattice3(k2_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f96])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33381,c_30006,c_28010,c_6834,c_6804,c_6481,c_6255,c_5652,c_5402,c_5403,c_5404,c_5405,c_5407,c_4282,c_4015,c_2813,c_2880,c_2867,c_26,c_28,c_29,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:56:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.29/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.29/1.49  
% 7.29/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.29/1.49  
% 7.29/1.49  ------  iProver source info
% 7.29/1.49  
% 7.29/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.29/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.29/1.49  git: non_committed_changes: false
% 7.29/1.49  git: last_make_outside_of_git: false
% 7.29/1.49  
% 7.29/1.49  ------ 
% 7.29/1.49  ------ Parsing...
% 7.29/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.29/1.49  
% 7.29/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.29/1.49  
% 7.29/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.29/1.49  
% 7.29/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.29/1.49  ------ Proving...
% 7.29/1.49  ------ Problem Properties 
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  clauses                                 30
% 7.29/1.49  conjectures                             5
% 7.29/1.49  EPR                                     1
% 7.29/1.49  Horn                                    22
% 7.29/1.49  unary                                   4
% 7.29/1.49  binary                                  10
% 7.29/1.49  lits                                    83
% 7.29/1.49  lits eq                                 1
% 7.29/1.49  fd_pure                                 0
% 7.29/1.49  fd_pseudo                               0
% 7.29/1.49  fd_cond                                 0
% 7.29/1.49  fd_pseudo_cond                          0
% 7.29/1.49  AC symbols                              0
% 7.29/1.49  
% 7.29/1.49  ------ Input Options Time Limit: Unbounded
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  ------ 
% 7.29/1.49  Current options:
% 7.29/1.49  ------ 
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  ------ Proving...
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  % SZS status Theorem for theBenchmark.p
% 7.29/1.49  
% 7.29/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.29/1.49  
% 7.29/1.49  fof(f1,axiom,(
% 7.29/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f14,plain,(
% 7.29/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.29/1.49    inference(ennf_transformation,[],[f1])).
% 7.29/1.49  
% 7.29/1.49  fof(f31,plain,(
% 7.29/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.29/1.49    inference(nnf_transformation,[],[f14])).
% 7.29/1.49  
% 7.29/1.49  fof(f32,plain,(
% 7.29/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.29/1.49    inference(rectify,[],[f31])).
% 7.29/1.49  
% 7.29/1.49  fof(f33,plain,(
% 7.29/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.29/1.49    introduced(choice_axiom,[])).
% 7.29/1.49  
% 7.29/1.49  fof(f34,plain,(
% 7.29/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.29/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 7.29/1.49  
% 7.29/1.49  fof(f57,plain,(
% 7.29/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f34])).
% 7.29/1.49  
% 7.29/1.49  fof(f10,axiom,(
% 7.29/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) => (v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : ((r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => r2_hidden(X3,X1))))),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f25,plain,(
% 7.29/1.49    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | (~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 7.29/1.49    inference(ennf_transformation,[],[f10])).
% 7.29/1.49  
% 7.29/1.49  fof(f26,plain,(
% 7.29/1.49    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 7.29/1.49    inference(flattening,[],[f25])).
% 7.29/1.49  
% 7.29/1.49  fof(f44,plain,(
% 7.29/1.49    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 7.29/1.49    inference(nnf_transformation,[],[f26])).
% 7.29/1.49  
% 7.29/1.49  fof(f45,plain,(
% 7.29/1.49    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 7.29/1.49    inference(rectify,[],[f44])).
% 7.29/1.49  
% 7.29/1.49  fof(f46,plain,(
% 7.29/1.49    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK3(X0,X1),X1) & r1_tarski(sK4(X0,X1),X0) & r1_tarski(sK3(X0,X1),sK4(X0,X1))))),
% 7.29/1.49    introduced(choice_axiom,[])).
% 7.29/1.49  
% 7.29/1.49  fof(f47,plain,(
% 7.29/1.49    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK3(X0,X1),X1) & r1_tarski(sK4(X0,X1),X0) & r1_tarski(sK3(X0,X1),sK4(X0,X1)))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 7.29/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f45,f46])).
% 7.29/1.49  
% 7.29/1.49  fof(f75,plain,(
% 7.29/1.49    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))) )),
% 7.29/1.49    inference(cnf_transformation,[],[f47])).
% 7.29/1.49  
% 7.29/1.49  fof(f8,axiom,(
% 7.29/1.49    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f69,plain,(
% 7.29/1.49    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 7.29/1.49    inference(cnf_transformation,[],[f8])).
% 7.29/1.49  
% 7.29/1.49  fof(f94,plain,(
% 7.29/1.49    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))) )),
% 7.29/1.49    inference(definition_unfolding,[],[f75,f69,f69])).
% 7.29/1.49  
% 7.29/1.49  fof(f9,axiom,(
% 7.29/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,X3) & v3_pre_topc(X3,X0)) => r2_hidden(X3,X1)))))),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f23,plain,(
% 7.29/1.49    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : ((r2_hidden(X3,X1) | (~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.29/1.49    inference(ennf_transformation,[],[f9])).
% 7.29/1.49  
% 7.29/1.49  fof(f24,plain,(
% 7.29/1.49    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.29/1.49    inference(flattening,[],[f23])).
% 7.29/1.49  
% 7.29/1.49  fof(f40,plain,(
% 7.29/1.49    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | ? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.29/1.49    inference(nnf_transformation,[],[f24])).
% 7.29/1.49  
% 7.29/1.49  fof(f41,plain,(
% 7.29/1.49    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | ? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.29/1.49    inference(rectify,[],[f40])).
% 7.29/1.49  
% 7.29/1.49  fof(f42,plain,(
% 7.29/1.49    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(X2,sK2(X0,X1,X2)) & v3_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.29/1.49    introduced(choice_axiom,[])).
% 7.29/1.49  
% 7.29/1.49  fof(f43,plain,(
% 7.29/1.49    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | (~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(X2,sK2(X0,X1,X2)) & v3_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.29/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 7.29/1.49  
% 7.29/1.49  fof(f70,plain,(
% 7.29/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_waybel_7(X0,X1,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f43])).
% 7.29/1.49  
% 7.29/1.49  fof(f12,conjecture,(
% 7.29/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => (r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)))))),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f13,negated_conjecture,(
% 7.29/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => (r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)))))),
% 7.29/1.49    inference(negated_conjecture,[],[f12])).
% 7.29/1.49  
% 7.29/1.49  fof(f29,plain,(
% 7.29/1.49    ? [X0] : (? [X1] : (? [X2] : ((r2_waybel_7(X0,X2,X1) <~> r1_tarski(k1_yellow19(X0,X1),X2)) & (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.29/1.49    inference(ennf_transformation,[],[f13])).
% 7.29/1.49  
% 7.29/1.49  fof(f30,plain,(
% 7.29/1.49    ? [X0] : (? [X1] : (? [X2] : ((r2_waybel_7(X0,X2,X1) <~> r1_tarski(k1_yellow19(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.29/1.49    inference(flattening,[],[f29])).
% 7.29/1.49  
% 7.29/1.49  fof(f49,plain,(
% 7.29/1.49    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.29/1.49    inference(nnf_transformation,[],[f30])).
% 7.29/1.49  
% 7.29/1.49  fof(f50,plain,(
% 7.29/1.49    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.29/1.49    inference(flattening,[],[f49])).
% 7.29/1.49  
% 7.29/1.49  fof(f53,plain,(
% 7.29/1.49    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => ((~r1_tarski(k1_yellow19(X0,X1),sK7) | ~r2_waybel_7(X0,sK7,X1)) & (r1_tarski(k1_yellow19(X0,X1),sK7) | r2_waybel_7(X0,sK7,X1)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK7,k3_yellow_1(k2_struct_0(X0))))) )),
% 7.29/1.49    introduced(choice_axiom,[])).
% 7.29/1.49  
% 7.29/1.49  fof(f52,plain,(
% 7.29/1.49    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~r1_tarski(k1_yellow19(X0,sK6),X2) | ~r2_waybel_7(X0,X2,sK6)) & (r1_tarski(k1_yellow19(X0,sK6),X2) | r2_waybel_7(X0,X2,sK6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 7.29/1.49    introduced(choice_axiom,[])).
% 7.29/1.49  
% 7.29/1.49  fof(f51,plain,(
% 7.29/1.49    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(sK5,X1),X2) | ~r2_waybel_7(sK5,X2,X1)) & (r1_tarski(k1_yellow19(sK5,X1),X2) | r2_waybel_7(sK5,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK5))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK5)))) & m1_subset_1(X1,u1_struct_0(sK5))) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 7.29/1.49    introduced(choice_axiom,[])).
% 7.29/1.49  
% 7.29/1.49  fof(f54,plain,(
% 7.29/1.49    (((~r1_tarski(k1_yellow19(sK5,sK6),sK7) | ~r2_waybel_7(sK5,sK7,sK6)) & (r1_tarski(k1_yellow19(sK5,sK6),sK7) | r2_waybel_7(sK5,sK7,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK5))))) & v13_waybel_0(sK7,k3_yellow_1(k2_struct_0(sK5)))) & m1_subset_1(sK6,u1_struct_0(sK5))) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 7.29/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f50,f53,f52,f51])).
% 7.29/1.49  
% 7.29/1.49  fof(f83,plain,(
% 7.29/1.49    v2_pre_topc(sK5)),
% 7.29/1.49    inference(cnf_transformation,[],[f54])).
% 7.29/1.49  
% 7.29/1.49  fof(f84,plain,(
% 7.29/1.49    l1_pre_topc(sK5)),
% 7.29/1.49    inference(cnf_transformation,[],[f54])).
% 7.29/1.49  
% 7.29/1.49  fof(f2,axiom,(
% 7.29/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f35,plain,(
% 7.29/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.29/1.49    inference(nnf_transformation,[],[f2])).
% 7.29/1.49  
% 7.29/1.49  fof(f58,plain,(
% 7.29/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.29/1.49    inference(cnf_transformation,[],[f35])).
% 7.29/1.49  
% 7.29/1.49  fof(f88,plain,(
% 7.29/1.49    r1_tarski(k1_yellow19(sK5,sK6),sK7) | r2_waybel_7(sK5,sK7,sK6)),
% 7.29/1.49    inference(cnf_transformation,[],[f54])).
% 7.29/1.49  
% 7.29/1.49  fof(f11,axiom,(
% 7.29/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1))))),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f27,plain,(
% 7.29/1.49    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.29/1.49    inference(ennf_transformation,[],[f11])).
% 7.29/1.49  
% 7.29/1.49  fof(f28,plain,(
% 7.29/1.49    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.29/1.49    inference(flattening,[],[f27])).
% 7.29/1.49  
% 7.29/1.49  fof(f48,plain,(
% 7.29/1.49    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_connsp_2(X2,X0,X1)) & (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X2,k1_yellow19(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.29/1.49    inference(nnf_transformation,[],[f28])).
% 7.29/1.49  
% 7.29/1.49  fof(f81,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f48])).
% 7.29/1.49  
% 7.29/1.49  fof(f82,plain,(
% 7.29/1.49    ~v2_struct_0(sK5)),
% 7.29/1.49    inference(cnf_transformation,[],[f54])).
% 7.29/1.49  
% 7.29/1.49  fof(f4,axiom,(
% 7.29/1.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f16,plain,(
% 7.29/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.29/1.49    inference(ennf_transformation,[],[f4])).
% 7.29/1.49  
% 7.29/1.49  fof(f61,plain,(
% 7.29/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f16])).
% 7.29/1.49  
% 7.29/1.49  fof(f3,axiom,(
% 7.29/1.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f15,plain,(
% 7.29/1.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.29/1.49    inference(ennf_transformation,[],[f3])).
% 7.29/1.49  
% 7.29/1.49  fof(f60,plain,(
% 7.29/1.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f15])).
% 7.29/1.49  
% 7.29/1.49  fof(f55,plain,(
% 7.29/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f34])).
% 7.29/1.49  
% 7.29/1.49  fof(f85,plain,(
% 7.29/1.49    m1_subset_1(sK6,u1_struct_0(sK5))),
% 7.29/1.49    inference(cnf_transformation,[],[f54])).
% 7.29/1.49  
% 7.29/1.49  fof(f89,plain,(
% 7.29/1.49    ~r1_tarski(k1_yellow19(sK5,sK6),sK7) | ~r2_waybel_7(sK5,sK7,sK6)),
% 7.29/1.49    inference(cnf_transformation,[],[f54])).
% 7.29/1.49  
% 7.29/1.49  fof(f74,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f43])).
% 7.29/1.49  
% 7.29/1.49  fof(f72,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | v3_pre_topc(sK2(X0,X1,X2),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f43])).
% 7.29/1.49  
% 7.29/1.49  fof(f71,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f43])).
% 7.29/1.49  
% 7.29/1.49  fof(f73,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,sK2(X0,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f43])).
% 7.29/1.49  
% 7.29/1.49  fof(f6,axiom,(
% 7.29/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f19,plain,(
% 7.29/1.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.29/1.49    inference(ennf_transformation,[],[f6])).
% 7.29/1.49  
% 7.29/1.49  fof(f20,plain,(
% 7.29/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.29/1.49    inference(flattening,[],[f19])).
% 7.29/1.49  
% 7.29/1.49  fof(f63,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f20])).
% 7.29/1.49  
% 7.29/1.49  fof(f7,axiom,(
% 7.29/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f21,plain,(
% 7.29/1.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.29/1.49    inference(ennf_transformation,[],[f7])).
% 7.29/1.49  
% 7.29/1.49  fof(f22,plain,(
% 7.29/1.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.29/1.49    inference(flattening,[],[f21])).
% 7.29/1.49  
% 7.29/1.49  fof(f36,plain,(
% 7.29/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.29/1.49    inference(nnf_transformation,[],[f22])).
% 7.29/1.49  
% 7.29/1.49  fof(f37,plain,(
% 7.29/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.29/1.49    inference(rectify,[],[f36])).
% 7.29/1.49  
% 7.29/1.49  fof(f38,plain,(
% 7.29/1.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.29/1.49    introduced(choice_axiom,[])).
% 7.29/1.49  
% 7.29/1.49  fof(f39,plain,(
% 7.29/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.29/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 7.29/1.49  
% 7.29/1.49  fof(f67,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (r2_hidden(X1,sK1(X0,X1,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f39])).
% 7.29/1.49  
% 7.29/1.49  fof(f5,axiom,(
% 7.29/1.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.29/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f17,plain,(
% 7.29/1.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.29/1.49    inference(ennf_transformation,[],[f5])).
% 7.29/1.49  
% 7.29/1.49  fof(f18,plain,(
% 7.29/1.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.29/1.49    inference(flattening,[],[f17])).
% 7.29/1.49  
% 7.29/1.49  fof(f62,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f18])).
% 7.29/1.49  
% 7.29/1.49  fof(f66,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (r1_tarski(sK1(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f39])).
% 7.29/1.49  
% 7.29/1.49  fof(f65,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (v3_pre_topc(sK1(X0,X1,X2),X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f39])).
% 7.29/1.49  
% 7.29/1.49  fof(f64,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f39])).
% 7.29/1.49  
% 7.29/1.49  fof(f80,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f48])).
% 7.29/1.49  
% 7.29/1.49  fof(f56,plain,(
% 7.29/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f34])).
% 7.29/1.49  
% 7.29/1.49  fof(f87,plain,(
% 7.29/1.49    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK5)))))),
% 7.29/1.49    inference(cnf_transformation,[],[f54])).
% 7.29/1.49  
% 7.29/1.49  fof(f95,plain,(
% 7.29/1.49    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))))),
% 7.29/1.49    inference(definition_unfolding,[],[f87,f69])).
% 7.29/1.49  
% 7.29/1.49  fof(f86,plain,(
% 7.29/1.49    v13_waybel_0(sK7,k3_yellow_1(k2_struct_0(sK5)))),
% 7.29/1.49    inference(cnf_transformation,[],[f54])).
% 7.29/1.49  
% 7.29/1.49  fof(f96,plain,(
% 7.29/1.49    v13_waybel_0(sK7,k3_lattice3(k1_lattice3(k2_struct_0(sK5))))),
% 7.29/1.49    inference(definition_unfolding,[],[f86,f69])).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2848,plain,
% 7.29/1.49      ( ~ r1_tarski(X0_53,X1_53)
% 7.29/1.49      | r1_tarski(X2_53,X3_53)
% 7.29/1.49      | X2_53 != X0_53
% 7.29/1.49      | X3_53 != X1_53 ),
% 7.29/1.49      theory(equality) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_5659,plain,
% 7.29/1.49      ( ~ r1_tarski(X0_53,X1_53)
% 7.29/1.49      | r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),X2_53)
% 7.29/1.49      | X2_53 != X1_53
% 7.29/1.49      | sK0(k1_yellow19(sK5,sK6),sK7) != X0_53 ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2848]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_12448,plain,
% 7.29/1.49      ( ~ r1_tarski(X0_53,X1_53)
% 7.29/1.49      | r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),k2_struct_0(sK5))
% 7.29/1.49      | sK0(k1_yellow19(sK5,sK6),sK7) != X0_53
% 7.29/1.49      | k2_struct_0(sK5) != X1_53 ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_5659]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_14464,plain,
% 7.29/1.49      ( ~ r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),X0_53)
% 7.29/1.49      | r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),k2_struct_0(sK5))
% 7.29/1.49      | sK0(k1_yellow19(sK5,sK6),sK7) != sK0(k1_yellow19(sK5,sK6),sK7)
% 7.29/1.49      | k2_struct_0(sK5) != X0_53 ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_12448]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_33381,plain,
% 7.29/1.49      ( ~ r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),u1_struct_0(sK5))
% 7.29/1.49      | r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),k2_struct_0(sK5))
% 7.29/1.49      | sK0(k1_yellow19(sK5,sK6),sK7) != sK0(k1_yellow19(sK5,sK6),sK7)
% 7.29/1.49      | k2_struct_0(sK5) != u1_struct_0(sK5) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_14464]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_0,plain,
% 7.29/1.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2842,plain,
% 7.29/1.49      ( ~ r2_hidden(sK0(X0_53,X1_53),X1_53) | r1_tarski(X0_53,X1_53) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_0]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_30006,plain,
% 7.29/1.49      ( ~ r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),sK7)
% 7.29/1.49      | r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2842]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_23,plain,
% 7.29/1.49      ( ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 7.29/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 7.29/1.49      | ~ r2_hidden(X2,X0)
% 7.29/1.49      | r2_hidden(X3,X0)
% 7.29/1.49      | ~ r1_tarski(X3,X1)
% 7.29/1.49      | ~ r1_tarski(X2,X3) ),
% 7.29/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2833,plain,
% 7.29/1.49      ( ~ v13_waybel_0(X0_53,k3_lattice3(k1_lattice3(X1_53)))
% 7.29/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1_53)))))
% 7.29/1.49      | ~ r2_hidden(X2_53,X0_53)
% 7.29/1.49      | r2_hidden(X3_53,X0_53)
% 7.29/1.49      | ~ r1_tarski(X3_53,X1_53)
% 7.29/1.49      | ~ r1_tarski(X2_53,X3_53) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_23]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_8361,plain,
% 7.29/1.49      ( ~ v13_waybel_0(X0_53,k3_lattice3(k1_lattice3(X1_53)))
% 7.29/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1_53)))))
% 7.29/1.49      | r2_hidden(X2_53,X0_53)
% 7.29/1.49      | ~ r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),X0_53)
% 7.29/1.49      | ~ r1_tarski(X2_53,X1_53)
% 7.29/1.49      | ~ r1_tarski(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),X2_53) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2833]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_23198,plain,
% 7.29/1.49      ( ~ v13_waybel_0(sK7,k3_lattice3(k1_lattice3(k2_struct_0(sK5))))
% 7.29/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))))
% 7.29/1.49      | r2_hidden(X0_53,sK7)
% 7.29/1.49      | ~ r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK7)
% 7.29/1.49      | ~ r1_tarski(X0_53,k2_struct_0(sK5))
% 7.29/1.49      | ~ r1_tarski(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),X0_53) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_8361]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_28010,plain,
% 7.29/1.49      ( ~ v13_waybel_0(sK7,k3_lattice3(k1_lattice3(k2_struct_0(sK5))))
% 7.29/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5))))))
% 7.29/1.49      | ~ r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK7)
% 7.29/1.49      | r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),sK7)
% 7.29/1.49      | ~ r1_tarski(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK0(k1_yellow19(sK5,sK6),sK7))
% 7.29/1.49      | ~ r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),k2_struct_0(sK5)) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_23198]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2847,plain,
% 7.29/1.49      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 7.29/1.49      theory(equality) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4510,plain,
% 7.29/1.49      ( X0_53 != X1_53
% 7.29/1.49      | X0_53 = u1_struct_0(sK5)
% 7.29/1.49      | u1_struct_0(sK5) != X1_53 ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2847]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_6081,plain,
% 7.29/1.49      ( X0_53 = u1_struct_0(sK5)
% 7.29/1.49      | X0_53 != k2_struct_0(sK5)
% 7.29/1.49      | u1_struct_0(sK5) != k2_struct_0(sK5) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_4510]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_6834,plain,
% 7.29/1.49      ( u1_struct_0(sK5) != k2_struct_0(sK5)
% 7.29/1.49      | k2_struct_0(sK5) = u1_struct_0(sK5)
% 7.29/1.49      | k2_struct_0(sK5) != k2_struct_0(sK5) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_6081]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_18,plain,
% 7.29/1.49      ( ~ r2_waybel_7(X0,X1,X2)
% 7.29/1.49      | ~ v3_pre_topc(X3,X0)
% 7.29/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 7.29/1.49      | ~ r2_hidden(X2,X3)
% 7.29/1.49      | r2_hidden(X3,X1)
% 7.29/1.49      | ~ v2_pre_topc(X0)
% 7.29/1.49      | ~ l1_pre_topc(X0) ),
% 7.29/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_32,negated_conjecture,
% 7.29/1.49      ( v2_pre_topc(sK5) ),
% 7.29/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_876,plain,
% 7.29/1.49      ( ~ r2_waybel_7(X0,X1,X2)
% 7.29/1.49      | ~ v3_pre_topc(X3,X0)
% 7.29/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 7.29/1.49      | ~ r2_hidden(X2,X3)
% 7.29/1.49      | r2_hidden(X3,X1)
% 7.29/1.49      | ~ l1_pre_topc(X0)
% 7.29/1.49      | sK5 != X0 ),
% 7.29/1.49      inference(resolution_lifted,[status(thm)],[c_18,c_32]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_877,plain,
% 7.29/1.49      ( ~ r2_waybel_7(sK5,X0,X1)
% 7.29/1.49      | ~ v3_pre_topc(X2,sK5)
% 7.29/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | ~ r2_hidden(X1,X2)
% 7.29/1.49      | r2_hidden(X2,X0)
% 7.29/1.49      | ~ l1_pre_topc(sK5) ),
% 7.29/1.49      inference(unflattening,[status(thm)],[c_876]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_31,negated_conjecture,
% 7.29/1.49      ( l1_pre_topc(sK5) ),
% 7.29/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_879,plain,
% 7.29/1.49      ( r2_hidden(X2,X0)
% 7.29/1.49      | ~ r2_hidden(X1,X2)
% 7.29/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | ~ v3_pre_topc(X2,sK5)
% 7.29/1.49      | ~ r2_waybel_7(sK5,X0,X1) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_877,c_31]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_880,plain,
% 7.29/1.49      ( ~ r2_waybel_7(sK5,X0,X1)
% 7.29/1.49      | ~ v3_pre_topc(X2,sK5)
% 7.29/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | ~ r2_hidden(X1,X2)
% 7.29/1.49      | r2_hidden(X2,X0) ),
% 7.29/1.49      inference(renaming,[status(thm)],[c_879]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2818,plain,
% 7.29/1.49      ( ~ r2_waybel_7(sK5,X0_53,X1_53)
% 7.29/1.49      | ~ v3_pre_topc(X2_53,sK5)
% 7.29/1.49      | ~ m1_subset_1(X2_53,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | ~ r2_hidden(X1_53,X2_53)
% 7.29/1.49      | r2_hidden(X2_53,X0_53) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_880]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_5179,plain,
% 7.29/1.49      ( ~ r2_waybel_7(sK5,X0_53,sK6)
% 7.29/1.49      | ~ v3_pre_topc(X1_53,sK5)
% 7.29/1.49      | ~ m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | r2_hidden(X1_53,X0_53)
% 7.29/1.49      | ~ r2_hidden(sK6,X1_53) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2818]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_6802,plain,
% 7.29/1.49      ( ~ r2_waybel_7(sK5,X0_53,sK6)
% 7.29/1.49      | ~ v3_pre_topc(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK5)
% 7.29/1.49      | ~ m1_subset_1(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),X0_53)
% 7.29/1.49      | ~ r2_hidden(sK6,sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7))) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_5179]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_6804,plain,
% 7.29/1.49      ( ~ r2_waybel_7(sK5,sK7,sK6)
% 7.29/1.49      | ~ v3_pre_topc(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK5)
% 7.29/1.49      | ~ m1_subset_1(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | r2_hidden(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK7)
% 7.29/1.49      | ~ r2_hidden(sK6,sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7))) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_6802]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4,plain,
% 7.29/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2838,plain,
% 7.29/1.49      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 7.29/1.49      | r1_tarski(X0_53,X1_53) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_5222,plain,
% 7.29/1.49      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | r1_tarski(X0_53,u1_struct_0(sK5)) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2838]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_6481,plain,
% 7.29/1.49      ( ~ m1_subset_1(sK0(k1_yellow19(sK5,sK6),sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | r1_tarski(sK0(k1_yellow19(sK5,sK6),sK7),u1_struct_0(sK5)) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_5222]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_27,negated_conjecture,
% 7.29/1.49      ( r2_waybel_7(sK5,sK7,sK6) | r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
% 7.29/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2831,negated_conjecture,
% 7.29/1.49      ( r2_waybel_7(sK5,sK7,sK6) | r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_27]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_3681,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
% 7.29/1.49      | r1_tarski(k1_yellow19(sK5,sK6),sK7) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_2831]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_24,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | r2_hidden(X0,k1_yellow19(X1,X2))
% 7.29/1.49      | v2_struct_0(X1)
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_33,negated_conjecture,
% 7.29/1.49      ( ~ v2_struct_0(sK5) ),
% 7.29/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_732,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | r2_hidden(X0,k1_yellow19(X1,X2))
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1)
% 7.29/1.49      | sK5 != X1 ),
% 7.29/1.49      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_733,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,sK5,X1)
% 7.29/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 7.29/1.49      | r2_hidden(X0,k1_yellow19(sK5,X1))
% 7.29/1.49      | ~ v2_pre_topc(sK5)
% 7.29/1.49      | ~ l1_pre_topc(sK5) ),
% 7.29/1.49      inference(unflattening,[status(thm)],[c_732]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_737,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,sK5,X1)
% 7.29/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 7.29/1.49      | r2_hidden(X0,k1_yellow19(sK5,X1)) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_733,c_32,c_31]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2822,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0_53,sK5,X1_53)
% 7.29/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
% 7.29/1.49      | r2_hidden(X0_53,k1_yellow19(sK5,X1_53)) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_737]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_3690,plain,
% 7.29/1.49      ( m1_connsp_2(X0_53,sK5,X1_53) != iProver_top
% 7.29/1.49      | m1_subset_1(X1_53,u1_struct_0(sK5)) != iProver_top
% 7.29/1.49      | r2_hidden(X0_53,k1_yellow19(sK5,X1_53)) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_2822]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_6,plain,
% 7.29/1.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.29/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_5,plain,
% 7.29/1.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.29/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_477,plain,
% 7.29/1.49      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.29/1.49      inference(resolution,[status(thm)],[c_6,c_5]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_989,plain,
% 7.29/1.49      ( u1_struct_0(X0) = k2_struct_0(X0) | sK5 != X0 ),
% 7.29/1.49      inference(resolution_lifted,[status(thm)],[c_477,c_31]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_990,plain,
% 7.29/1.49      ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
% 7.29/1.49      inference(unflattening,[status(thm)],[c_989]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2813,plain,
% 7.29/1.49      ( u1_struct_0(sK5) = k2_struct_0(sK5) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_990]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_3762,plain,
% 7.29/1.49      ( m1_connsp_2(X0_53,sK5,X1_53) != iProver_top
% 7.29/1.49      | m1_subset_1(X1_53,k2_struct_0(sK5)) != iProver_top
% 7.29/1.49      | r2_hidden(X0_53,k1_yellow19(sK5,X1_53)) = iProver_top ),
% 7.29/1.49      inference(light_normalisation,[status(thm)],[c_3690,c_2813]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2,plain,
% 7.29/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.29/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2840,plain,
% 7.29/1.49      ( ~ r2_hidden(X0_53,X1_53)
% 7.29/1.49      | r2_hidden(X0_53,X2_53)
% 7.29/1.49      | ~ r1_tarski(X1_53,X2_53) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_3672,plain,
% 7.29/1.49      ( r2_hidden(X0_53,X1_53) != iProver_top
% 7.29/1.49      | r2_hidden(X0_53,X2_53) = iProver_top
% 7.29/1.49      | r1_tarski(X1_53,X2_53) != iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_2840]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4416,plain,
% 7.29/1.49      ( m1_connsp_2(X0_53,sK5,X1_53) != iProver_top
% 7.29/1.49      | m1_subset_1(X1_53,k2_struct_0(sK5)) != iProver_top
% 7.29/1.49      | r2_hidden(X0_53,X2_53) = iProver_top
% 7.29/1.49      | r1_tarski(k1_yellow19(sK5,X1_53),X2_53) != iProver_top ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_3762,c_3672]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_6138,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
% 7.29/1.49      | m1_connsp_2(X0_53,sK5,sK6) != iProver_top
% 7.29/1.49      | m1_subset_1(sK6,k2_struct_0(sK5)) != iProver_top
% 7.29/1.49      | r2_hidden(X0_53,sK7) = iProver_top ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_3681,c_4416]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_30,negated_conjecture,
% 7.29/1.49      ( m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 7.29/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_37,plain,
% 7.29/1.49      ( m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_40,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
% 7.29/1.49      | r1_tarski(k1_yellow19(sK5,sK6),sK7) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_26,negated_conjecture,
% 7.29/1.49      ( ~ r2_waybel_7(sK5,sK7,sK6)
% 7.29/1.49      | ~ r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
% 7.29/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_286,plain,
% 7.29/1.49      ( ~ r2_waybel_7(sK5,sK7,sK6)
% 7.29/1.49      | ~ r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
% 7.29/1.49      inference(prop_impl,[status(thm)],[c_26]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_14,plain,
% 7.29/1.49      ( r2_waybel_7(X0,X1,X2)
% 7.29/1.49      | ~ r2_hidden(sK2(X0,X1,X2),X1)
% 7.29/1.49      | ~ v2_pre_topc(X0)
% 7.29/1.49      | ~ l1_pre_topc(X0) ),
% 7.29/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_953,plain,
% 7.29/1.49      ( r2_waybel_7(X0,X1,X2)
% 7.29/1.49      | ~ r2_hidden(sK2(X0,X1,X2),X1)
% 7.29/1.49      | ~ l1_pre_topc(X0)
% 7.29/1.49      | sK5 != X0 ),
% 7.29/1.49      inference(resolution_lifted,[status(thm)],[c_14,c_32]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_954,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,X0,X1)
% 7.29/1.49      | ~ r2_hidden(sK2(sK5,X0,X1),X0)
% 7.29/1.49      | ~ l1_pre_topc(sK5) ),
% 7.29/1.49      inference(unflattening,[status(thm)],[c_953]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_958,plain,
% 7.29/1.49      ( ~ r2_hidden(sK2(sK5,X0,X1),X0) | r2_waybel_7(sK5,X0,X1) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_954,c_31]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_959,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,X0,X1) | ~ r2_hidden(sK2(sK5,X0,X1),X0) ),
% 7.29/1.49      inference(renaming,[status(thm)],[c_958]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1089,plain,
% 7.29/1.49      ( ~ r2_hidden(sK2(sK5,X0,X1),X0)
% 7.29/1.49      | ~ r1_tarski(k1_yellow19(sK5,sK6),sK7)
% 7.29/1.49      | sK7 != X0
% 7.29/1.49      | sK6 != X1
% 7.29/1.49      | sK5 != sK5 ),
% 7.29/1.49      inference(resolution_lifted,[status(thm)],[c_286,c_959]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1090,plain,
% 7.29/1.49      ( ~ r2_hidden(sK2(sK5,sK7,sK6),sK7)
% 7.29/1.49      | ~ r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
% 7.29/1.49      inference(unflattening,[status(thm)],[c_1089]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1091,plain,
% 7.29/1.49      ( r2_hidden(sK2(sK5,sK7,sK6),sK7) != iProver_top
% 7.29/1.49      | r1_tarski(k1_yellow19(sK5,sK6),sK7) != iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_1090]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_16,plain,
% 7.29/1.49      ( r2_waybel_7(X0,X1,X2)
% 7.29/1.49      | v3_pre_topc(sK2(X0,X1,X2),X0)
% 7.29/1.49      | ~ v2_pre_topc(X0)
% 7.29/1.49      | ~ l1_pre_topc(X0) ),
% 7.29/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_917,plain,
% 7.29/1.49      ( r2_waybel_7(X0,X1,X2)
% 7.29/1.49      | v3_pre_topc(sK2(X0,X1,X2),X0)
% 7.29/1.49      | ~ l1_pre_topc(X0)
% 7.29/1.49      | sK5 != X0 ),
% 7.29/1.49      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_918,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,X0,X1)
% 7.29/1.49      | v3_pre_topc(sK2(sK5,X0,X1),sK5)
% 7.29/1.49      | ~ l1_pre_topc(sK5) ),
% 7.29/1.49      inference(unflattening,[status(thm)],[c_917]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_922,plain,
% 7.29/1.49      ( v3_pre_topc(sK2(sK5,X0,X1),sK5) | r2_waybel_7(sK5,X0,X1) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_918,c_31]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_923,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,X0,X1) | v3_pre_topc(sK2(sK5,X0,X1),sK5) ),
% 7.29/1.49      inference(renaming,[status(thm)],[c_922]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2816,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,X0_53,X1_53)
% 7.29/1.49      | v3_pre_topc(sK2(sK5,X0_53,X1_53),sK5) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_923]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4133,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,sK7,sK6) | v3_pre_topc(sK2(sK5,sK7,sK6),sK5) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2816]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4134,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
% 7.29/1.49      | v3_pre_topc(sK2(sK5,sK7,sK6),sK5) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_4133]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_17,plain,
% 7.29/1.49      ( r2_waybel_7(X0,X1,X2)
% 7.29/1.49      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 7.29/1.49      | ~ v2_pre_topc(X0)
% 7.29/1.49      | ~ l1_pre_topc(X0) ),
% 7.29/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_899,plain,
% 7.29/1.49      ( r2_waybel_7(X0,X1,X2)
% 7.29/1.49      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 7.29/1.49      | ~ l1_pre_topc(X0)
% 7.29/1.49      | sK5 != X0 ),
% 7.29/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_32]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_900,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,X0,X1)
% 7.29/1.49      | m1_subset_1(sK2(sK5,X0,X1),k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | ~ l1_pre_topc(sK5) ),
% 7.29/1.49      inference(unflattening,[status(thm)],[c_899]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_904,plain,
% 7.29/1.49      ( m1_subset_1(sK2(sK5,X0,X1),k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | r2_waybel_7(sK5,X0,X1) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_900,c_31]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_905,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,X0,X1)
% 7.29/1.49      | m1_subset_1(sK2(sK5,X0,X1),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 7.29/1.49      inference(renaming,[status(thm)],[c_904]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2817,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,X0_53,X1_53)
% 7.29/1.49      | m1_subset_1(sK2(sK5,X0_53,X1_53),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_905]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4132,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,sK7,sK6)
% 7.29/1.49      | m1_subset_1(sK2(sK5,sK7,sK6),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2817]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4136,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
% 7.29/1.49      | m1_subset_1(sK2(sK5,sK7,sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_4132]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_15,plain,
% 7.29/1.49      ( r2_waybel_7(X0,X1,X2)
% 7.29/1.49      | r2_hidden(X2,sK2(X0,X1,X2))
% 7.29/1.49      | ~ v2_pre_topc(X0)
% 7.29/1.49      | ~ l1_pre_topc(X0) ),
% 7.29/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_935,plain,
% 7.29/1.49      ( r2_waybel_7(X0,X1,X2)
% 7.29/1.49      | r2_hidden(X2,sK2(X0,X1,X2))
% 7.29/1.49      | ~ l1_pre_topc(X0)
% 7.29/1.49      | sK5 != X0 ),
% 7.29/1.49      inference(resolution_lifted,[status(thm)],[c_15,c_32]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_936,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,X0,X1)
% 7.29/1.49      | r2_hidden(X1,sK2(sK5,X0,X1))
% 7.29/1.49      | ~ l1_pre_topc(sK5) ),
% 7.29/1.49      inference(unflattening,[status(thm)],[c_935]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_940,plain,
% 7.29/1.49      ( r2_hidden(X1,sK2(sK5,X0,X1)) | r2_waybel_7(sK5,X0,X1) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_936,c_31]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_941,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,X0,X1) | r2_hidden(X1,sK2(sK5,X0,X1)) ),
% 7.29/1.49      inference(renaming,[status(thm)],[c_940]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2815,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,X0_53,X1_53)
% 7.29/1.49      | r2_hidden(X1_53,sK2(sK5,X0_53,X1_53)) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_941]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4131,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,sK7,sK6) | r2_hidden(sK6,sK2(sK5,sK7,sK6)) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2815]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4138,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,sK7,sK6) = iProver_top
% 7.29/1.49      | r2_hidden(sK6,sK2(sK5,sK7,sK6)) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_4131]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_8,plain,
% 7.29/1.49      ( m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | ~ v3_pre_topc(X0,X1)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.29/1.49      | ~ r2_hidden(X2,X0)
% 7.29/1.49      | v2_struct_0(X1)
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_786,plain,
% 7.29/1.49      ( m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | ~ v3_pre_topc(X0,X1)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.29/1.49      | ~ r2_hidden(X2,X0)
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1)
% 7.29/1.49      | sK5 != X1 ),
% 7.29/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_33]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_787,plain,
% 7.29/1.49      ( m1_connsp_2(X0,sK5,X1)
% 7.29/1.49      | ~ v3_pre_topc(X0,sK5)
% 7.29/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 7.29/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | ~ r2_hidden(X1,X0)
% 7.29/1.49      | ~ v2_pre_topc(sK5)
% 7.29/1.49      | ~ l1_pre_topc(sK5) ),
% 7.29/1.49      inference(unflattening,[status(thm)],[c_786]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_791,plain,
% 7.29/1.49      ( m1_connsp_2(X0,sK5,X1)
% 7.29/1.49      | ~ v3_pre_topc(X0,sK5)
% 7.29/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 7.29/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | ~ r2_hidden(X1,X0) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_787,c_32,c_31]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2820,plain,
% 7.29/1.49      ( m1_connsp_2(X0_53,sK5,X1_53)
% 7.29/1.49      | ~ v3_pre_topc(X0_53,sK5)
% 7.29/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
% 7.29/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | ~ r2_hidden(X1_53,X0_53) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_791]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4242,plain,
% 7.29/1.49      ( m1_connsp_2(sK2(sK5,sK7,sK6),sK5,sK6)
% 7.29/1.49      | ~ v3_pre_topc(sK2(sK5,sK7,sK6),sK5)
% 7.29/1.49      | ~ m1_subset_1(sK2(sK5,sK7,sK6),k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 7.29/1.49      | ~ r2_hidden(sK6,sK2(sK5,sK7,sK6)) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2820]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4243,plain,
% 7.29/1.49      ( m1_connsp_2(sK2(sK5,sK7,sK6),sK5,sK6) = iProver_top
% 7.29/1.49      | v3_pre_topc(sK2(sK5,sK7,sK6),sK5) != iProver_top
% 7.29/1.49      | m1_subset_1(sK2(sK5,sK7,sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 7.29/1.49      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 7.29/1.49      | r2_hidden(sK6,sK2(sK5,sK7,sK6)) != iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_4242]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4393,plain,
% 7.29/1.49      ( ~ m1_connsp_2(sK2(sK5,sK7,sK6),sK5,sK6)
% 7.29/1.49      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 7.29/1.49      | r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6)) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2822]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4397,plain,
% 7.29/1.49      ( m1_connsp_2(sK2(sK5,sK7,sK6),sK5,sK6) != iProver_top
% 7.29/1.49      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 7.29/1.49      | r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6)) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_4393]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4913,plain,
% 7.29/1.49      ( r2_hidden(sK2(sK5,sK7,sK6),X0_53)
% 7.29/1.49      | ~ r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6))
% 7.29/1.49      | ~ r1_tarski(k1_yellow19(sK5,sK6),X0_53) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2840]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4914,plain,
% 7.29/1.49      ( r2_hidden(sK2(sK5,sK7,sK6),X0_53) = iProver_top
% 7.29/1.49      | r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6)) != iProver_top
% 7.29/1.49      | r1_tarski(k1_yellow19(sK5,sK6),X0_53) != iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_4913]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4916,plain,
% 7.29/1.49      ( r2_hidden(sK2(sK5,sK7,sK6),k1_yellow19(sK5,sK6)) != iProver_top
% 7.29/1.49      | r2_hidden(sK2(sK5,sK7,sK6),sK7) = iProver_top
% 7.29/1.49      | r1_tarski(k1_yellow19(sK5,sK6),sK7) != iProver_top ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_4914]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_6253,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,sK7,sK6) = iProver_top ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_6138,c_37,c_40,c_1091,c_4134,c_4136,c_4138,c_4243,
% 7.29/1.49                 c_4397,c_4916]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_6255,plain,
% 7.29/1.49      ( r2_waybel_7(sK5,sK7,sK6) ),
% 7.29/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_6253]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2844,plain,( X0_53 = X0_53 ),theory(equality) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_5652,plain,
% 7.29/1.49      ( sK0(k1_yellow19(sK5,sK6),sK7) = sK0(k1_yellow19(sK5,sK6),sK7) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2844]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_10,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.29/1.49      | r2_hidden(X2,sK1(X1,X2,X0))
% 7.29/1.49      | v2_struct_0(X1)
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_7,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.29/1.49      | v2_struct_0(X1)
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_224,plain,
% 7.29/1.49      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | r2_hidden(X2,sK1(X1,X2,X0))
% 7.29/1.49      | v2_struct_0(X1)
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_10,c_7]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_225,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | r2_hidden(X2,sK1(X1,X2,X0))
% 7.29/1.49      | v2_struct_0(X1)
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1) ),
% 7.29/1.49      inference(renaming,[status(thm)],[c_224]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_627,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | r2_hidden(X2,sK1(X1,X2,X0))
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1)
% 7.29/1.49      | sK5 != X1 ),
% 7.29/1.49      inference(resolution_lifted,[status(thm)],[c_225,c_33]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_628,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,sK5,X1)
% 7.29/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 7.29/1.49      | r2_hidden(X1,sK1(sK5,X1,X0))
% 7.29/1.49      | ~ v2_pre_topc(sK5)
% 7.29/1.49      | ~ l1_pre_topc(sK5) ),
% 7.29/1.49      inference(unflattening,[status(thm)],[c_627]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_632,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,sK5,X1)
% 7.29/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 7.29/1.49      | r2_hidden(X1,sK1(sK5,X1,X0)) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_628,c_32,c_31]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2827,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0_53,sK5,X1_53)
% 7.29/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
% 7.29/1.49      | r2_hidden(X1_53,sK1(sK5,X1_53,X0_53)) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_632]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_5402,plain,
% 7.29/1.49      ( ~ m1_connsp_2(sK0(k1_yellow19(sK5,sK6),sK7),sK5,sK6)
% 7.29/1.49      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 7.29/1.49      | r2_hidden(sK6,sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7))) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2827]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_11,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.29/1.49      | r1_tarski(sK1(X1,X2,X0),X0)
% 7.29/1.49      | v2_struct_0(X1)
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_217,plain,
% 7.29/1.49      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | r1_tarski(sK1(X1,X2,X0),X0)
% 7.29/1.49      | v2_struct_0(X1)
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_11,c_7]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_218,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | r1_tarski(sK1(X1,X2,X0),X0)
% 7.29/1.49      | v2_struct_0(X1)
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1) ),
% 7.29/1.49      inference(renaming,[status(thm)],[c_217]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_648,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | r1_tarski(sK1(X1,X2,X0),X0)
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1)
% 7.29/1.49      | sK5 != X1 ),
% 7.29/1.49      inference(resolution_lifted,[status(thm)],[c_218,c_33]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_649,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,sK5,X1)
% 7.29/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 7.29/1.49      | r1_tarski(sK1(sK5,X1,X0),X0)
% 7.29/1.49      | ~ v2_pre_topc(sK5)
% 7.29/1.49      | ~ l1_pre_topc(sK5) ),
% 7.29/1.49      inference(unflattening,[status(thm)],[c_648]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_653,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,sK5,X1)
% 7.29/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 7.29/1.49      | r1_tarski(sK1(sK5,X1,X0),X0) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_649,c_32,c_31]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2826,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0_53,sK5,X1_53)
% 7.29/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
% 7.29/1.49      | r1_tarski(sK1(sK5,X1_53,X0_53),X0_53) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_653]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_5403,plain,
% 7.29/1.49      ( ~ m1_connsp_2(sK0(k1_yellow19(sK5,sK6),sK7),sK5,sK6)
% 7.29/1.49      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 7.29/1.49      | r1_tarski(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK0(k1_yellow19(sK5,sK6),sK7)) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2826]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_12,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.29/1.49      | v2_struct_0(X1)
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_210,plain,
% 7.29/1.49      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 7.29/1.49      | ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | v2_struct_0(X1)
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_12,c_7]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_211,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | v2_struct_0(X1)
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1) ),
% 7.29/1.49      inference(renaming,[status(thm)],[c_210]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_669,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1)
% 7.29/1.49      | sK5 != X1 ),
% 7.29/1.49      inference(resolution_lifted,[status(thm)],[c_211,c_33]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_670,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,sK5,X1)
% 7.29/1.49      | v3_pre_topc(sK1(sK5,X1,X0),sK5)
% 7.29/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 7.29/1.49      | ~ v2_pre_topc(sK5)
% 7.29/1.49      | ~ l1_pre_topc(sK5) ),
% 7.29/1.49      inference(unflattening,[status(thm)],[c_669]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_674,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,sK5,X1)
% 7.29/1.49      | v3_pre_topc(sK1(sK5,X1,X0),sK5)
% 7.29/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK5)) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_670,c_32,c_31]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2825,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0_53,sK5,X1_53)
% 7.29/1.49      | v3_pre_topc(sK1(sK5,X1_53,X0_53),sK5)
% 7.29/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(sK5)) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_674]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_5404,plain,
% 7.29/1.49      ( ~ m1_connsp_2(sK0(k1_yellow19(sK5,sK6),sK7),sK5,sK6)
% 7.29/1.49      | v3_pre_topc(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),sK5)
% 7.29/1.49      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2825]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_13,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.29/1.49      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.29/1.49      | v2_struct_0(X1)
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_203,plain,
% 7.29/1.49      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.29/1.49      | v2_struct_0(X1)
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_13,c_7]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_204,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.29/1.49      | v2_struct_0(X1)
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1) ),
% 7.29/1.49      inference(renaming,[status(thm)],[c_203]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_690,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1)
% 7.29/1.49      | sK5 != X1 ),
% 7.29/1.49      inference(resolution_lifted,[status(thm)],[c_204,c_33]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_691,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,sK5,X1)
% 7.29/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 7.29/1.49      | m1_subset_1(sK1(sK5,X1,X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | ~ v2_pre_topc(sK5)
% 7.29/1.49      | ~ l1_pre_topc(sK5) ),
% 7.29/1.49      inference(unflattening,[status(thm)],[c_690]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_695,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,sK5,X1)
% 7.29/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 7.29/1.49      | m1_subset_1(sK1(sK5,X1,X0),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_691,c_32,c_31]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2824,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0_53,sK5,X1_53)
% 7.29/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
% 7.29/1.49      | m1_subset_1(sK1(sK5,X1_53,X0_53),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_695]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_5405,plain,
% 7.29/1.49      ( ~ m1_connsp_2(sK0(k1_yellow19(sK5,sK6),sK7),sK5,sK6)
% 7.29/1.49      | m1_subset_1(sK1(sK5,sK6,sK0(k1_yellow19(sK5,sK6),sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2824]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_813,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1)
% 7.29/1.49      | sK5 != X1 ),
% 7.29/1.49      inference(resolution_lifted,[status(thm)],[c_7,c_33]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_814,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,sK5,X1)
% 7.29/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 7.29/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | ~ v2_pre_topc(sK5)
% 7.29/1.49      | ~ l1_pre_topc(sK5) ),
% 7.29/1.49      inference(unflattening,[status(thm)],[c_813]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_818,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0,sK5,X1)
% 7.29/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 7.29/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_814,c_32,c_31]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2819,plain,
% 7.29/1.49      ( ~ m1_connsp_2(X0_53,sK5,X1_53)
% 7.29/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
% 7.29/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_818]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_5407,plain,
% 7.29/1.49      ( ~ m1_connsp_2(sK0(k1_yellow19(sK5,sK6),sK7),sK5,sK6)
% 7.29/1.49      | m1_subset_1(sK0(k1_yellow19(sK5,sK6),sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 7.29/1.49      | ~ m1_subset_1(sK6,u1_struct_0(sK5)) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2819]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_25,plain,
% 7.29/1.49      ( m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | ~ r2_hidden(X0,k1_yellow19(X1,X2))
% 7.29/1.49      | v2_struct_0(X1)
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_711,plain,
% 7.29/1.49      ( m1_connsp_2(X0,X1,X2)
% 7.29/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.29/1.49      | ~ r2_hidden(X0,k1_yellow19(X1,X2))
% 7.29/1.49      | ~ v2_pre_topc(X1)
% 7.29/1.49      | ~ l1_pre_topc(X1)
% 7.29/1.49      | sK5 != X1 ),
% 7.29/1.49      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_712,plain,
% 7.29/1.49      ( m1_connsp_2(X0,sK5,X1)
% 7.29/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 7.29/1.49      | ~ r2_hidden(X0,k1_yellow19(sK5,X1))
% 7.29/1.49      | ~ v2_pre_topc(sK5)
% 7.29/1.49      | ~ l1_pre_topc(sK5) ),
% 7.29/1.49      inference(unflattening,[status(thm)],[c_711]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_716,plain,
% 7.29/1.49      ( m1_connsp_2(X0,sK5,X1)
% 7.29/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 7.29/1.49      | ~ r2_hidden(X0,k1_yellow19(sK5,X1)) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_712,c_32,c_31]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2823,plain,
% 7.29/1.49      ( m1_connsp_2(X0_53,sK5,X1_53)
% 7.29/1.49      | ~ m1_subset_1(X1_53,u1_struct_0(sK5))
% 7.29/1.49      | ~ r2_hidden(X0_53,k1_yellow19(sK5,X1_53)) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_716]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4282,plain,
% 7.29/1.49      ( m1_connsp_2(sK0(k1_yellow19(sK5,sK6),sK7),sK5,sK6)
% 7.29/1.49      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 7.29/1.49      | ~ r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),k1_yellow19(sK5,sK6)) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2823]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1,plain,
% 7.29/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2841,plain,
% 7.29/1.49      ( r2_hidden(sK0(X0_53,X1_53),X0_53) | r1_tarski(X0_53,X1_53) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4015,plain,
% 7.29/1.49      ( r2_hidden(sK0(k1_yellow19(sK5,sK6),sK7),k1_yellow19(sK5,sK6))
% 7.29/1.49      | r1_tarski(k1_yellow19(sK5,sK6),sK7) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2841]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2845,plain,( X0_54 = X0_54 ),theory(equality) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2880,plain,
% 7.29/1.49      ( sK5 = sK5 ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2845]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2852,plain,
% 7.29/1.49      ( X0_54 != X1_54 | k2_struct_0(X0_54) = k2_struct_0(X1_54) ),
% 7.29/1.49      theory(equality) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2867,plain,
% 7.29/1.49      ( sK5 != sK5 | k2_struct_0(sK5) = k2_struct_0(sK5) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_2852]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_28,negated_conjecture,
% 7.29/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK5)))))) ),
% 7.29/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_29,negated_conjecture,
% 7.29/1.49      ( v13_waybel_0(sK7,k3_lattice3(k1_lattice3(k2_struct_0(sK5)))) ),
% 7.29/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(contradiction,plain,
% 7.29/1.49      ( $false ),
% 7.29/1.49      inference(minisat,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_33381,c_30006,c_28010,c_6834,c_6804,c_6481,c_6255,
% 7.29/1.49                 c_5652,c_5402,c_5403,c_5404,c_5405,c_5407,c_4282,c_4015,
% 7.29/1.49                 c_2813,c_2880,c_2867,c_26,c_28,c_29,c_30]) ).
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.29/1.49  
% 7.29/1.49  ------                               Statistics
% 7.29/1.49  
% 7.29/1.49  ------ Selected
% 7.29/1.49  
% 7.29/1.49  total_time:                             0.908
% 7.29/1.49  
%------------------------------------------------------------------------------
