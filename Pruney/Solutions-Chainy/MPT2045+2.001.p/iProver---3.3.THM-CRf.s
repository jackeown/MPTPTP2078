%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:02 EST 2020

% Result     : Theorem 27.63s
% Output     : CNFRefutation 27.63s
% Verified   : 
% Statistics : Number of formulae       :  253 (1213 expanded)
%              Number of clauses        :  149 ( 282 expanded)
%              Number of leaves         :   31 ( 326 expanded)
%              Depth                    :   21
%              Number of atoms          : 1024 (8828 expanded)
%              Number of equality atoms :   60 ( 127 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
     => ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) )
           => r2_hidden(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(flattening,[],[f41])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & r1_tarski(X3,X0)
          & r1_tarski(X2,X3) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X1)
        & r1_tarski(sK3(X0,X1),X0)
        & r1_tarski(sK2(X0,X1),sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ( ~ r2_hidden(sK3(X0,X1),X1)
            & r2_hidden(sK2(X0,X1),X1)
            & r1_tarski(sK3(X0,X1),X0)
            & r1_tarski(sK2(X0,X1),sK3(X0,X1)) ) )
        & ( ! [X4,X5] :
              ( r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1)
              | ~ r1_tarski(X5,X0)
              | ~ r1_tarski(X4,X5) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f58,f59])).

fof(f92,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f15,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f111,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) ) ),
    inference(definition_unfolding,[],[f92,f86,f86])).

fof(f16,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(X2,sK1(X0,X1,X2))
        & v3_pre_topc(sK1(X0,X1,X2),X0)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(X2,sK1(X0,X1,X2))
              & v3_pre_topc(sK1(X0,X1,X2),X0)
              & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f54,f55])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k1_yellow19(X0,X1),X2)
            | ~ r2_waybel_7(X0,X2,X1) )
          & ( r1_tarski(k1_yellow19(X0,X1),X2)
            | r2_waybel_7(X0,X2,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
     => ( ( ~ r1_tarski(k1_yellow19(X0,X1),sK6)
          | ~ r2_waybel_7(X0,sK6,X1) )
        & ( r1_tarski(k1_yellow19(X0,X1),sK6)
          | r2_waybel_7(X0,sK6,X1) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK6,k3_yellow_1(k2_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
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
            ( ( ~ r1_tarski(k1_yellow19(X0,sK5),X2)
              | ~ r2_waybel_7(X0,X2,sK5) )
            & ( r1_tarski(k1_yellow19(X0,sK5),X2)
              | r2_waybel_7(X0,X2,sK5) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
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
              ( ( ~ r1_tarski(k1_yellow19(sK4,X1),X2)
                | ~ r2_waybel_7(sK4,X2,X1) )
              & ( r1_tarski(k1_yellow19(sK4,X1),X2)
                | r2_waybel_7(sK4,X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK4))) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ( ~ r1_tarski(k1_yellow19(sK4,sK5),sK6)
      | ~ r2_waybel_7(sK4,sK6,sK5) )
    & ( r1_tarski(k1_yellow19(sK4,sK5),sK6)
      | r2_waybel_7(sK4,sK6,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))
    & v13_waybel_0(sK6,k3_yellow_1(k2_struct_0(sK4)))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f63,f66,f65,f64])).

fof(f100,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f101,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f78,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f77,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f105,plain,
    ( r1_tarski(k1_yellow19(sK4,sK5),sK6)
    | r2_waybel_7(sK4,sK6,sK5) ),
    inference(cnf_transformation,[],[f67])).

fof(f14,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f99,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f18,axiom,(
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

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | v3_pre_topc(sK1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | r2_hidden(X2,sK1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f106,plain,
    ( ~ r1_tarski(k1_yellow19(sK4,sK5),sK6)
    | ~ r2_waybel_7(sK4,sK6,sK5) ),
    inference(cnf_transformation,[],[f67])).

fof(f104,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) ),
    inference(cnf_transformation,[],[f67])).

fof(f112,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) ),
    inference(definition_unfolding,[],[f104,f86])).

fof(f103,plain,(
    v13_waybel_0(sK6,k3_yellow_1(k2_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f67])).

fof(f113,plain,(
    v13_waybel_0(sK6,k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
    inference(definition_unfolding,[],[f103,f86])).

fof(f102,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,plain,
    ( ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X3,X0)
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_106170,plain,
    ( ~ v13_waybel_0(sK6,k3_lattice3(k1_lattice3(k2_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))))
    | ~ r2_hidden(X0,sK6)
    | r2_hidden(X1,sK6)
    | ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_108822,plain,
    ( ~ v13_waybel_0(sK6,k3_lattice3(k1_lattice3(k2_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))))
    | r2_hidden(X0,sK6)
    | ~ r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK6)
    | ~ r1_tarski(X0,k2_struct_0(sK4))
    | ~ r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),X0) ),
    inference(instantiation,[status(thm)],[c_106170])).

cnf(c_113726,plain,
    ( ~ v13_waybel_0(sK6,k3_lattice3(k1_lattice3(k2_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))))
    | ~ r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK6)
    | r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),sK6)
    | ~ r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK0(k1_yellow19(sK4,sK5),sK6))
    | ~ r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_108822])).

cnf(c_22,plain,
    ( ~ r2_waybel_7(X0,X1,X2)
    | ~ v3_pre_topc(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_676,plain,
    ( ~ r2_waybel_7(X0,X1,X2)
    | ~ v3_pre_topc(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_36])).

cnf(c_677,plain,
    ( ~ r2_waybel_7(sK4,X0,X1)
    | ~ v3_pre_topc(X2,sK4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X2,X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_679,plain,
    ( r2_hidden(X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_pre_topc(X2,sK4)
    | ~ r2_waybel_7(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_677,c_35])).

cnf(c_680,plain,
    ( ~ r2_waybel_7(sK4,X0,X1)
    | ~ v3_pre_topc(X2,sK4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X2,X0) ),
    inference(renaming,[status(thm)],[c_679])).

cnf(c_5828,plain,
    ( ~ r2_waybel_7(sK4,X0,sK5)
    | ~ v3_pre_topc(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK4)
    | ~ m1_subset_1(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),X0)
    | ~ r2_hidden(sK5,k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6))) ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_57627,plain,
    ( ~ r2_waybel_7(sK4,sK6,sK5)
    | ~ v3_pre_topc(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK4)
    | ~ m1_subset_1(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK6)
    | ~ r2_hidden(sK5,k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6))) ),
    inference(instantiation,[status(thm)],[c_5828])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_6475,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),X0)
    | r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_16129,plain,
    ( r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),X0)
    | ~ r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_6475])).

cnf(c_29534,plain,
    ( ~ r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),u1_struct_0(sK4))
    | r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),k2_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK4),k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_16129])).

cnf(c_3444,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_7686,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK4,u1_struct_0(sK4)))
    | r1_tarski(X0,u1_struct_0(sK4))
    | ~ r1_tarski(k1_tops_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3444])).

cnf(c_14433,plain,
    ( ~ r1_tarski(k1_tops_1(sK4,X0),k1_tops_1(sK4,u1_struct_0(sK4)))
    | r1_tarski(k1_tops_1(sK4,X0),u1_struct_0(sK4))
    | ~ r1_tarski(k1_tops_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_7686])).

cnf(c_27231,plain,
    ( ~ r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_tops_1(sK4,u1_struct_0(sK4)))
    | r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),u1_struct_0(sK4))
    | ~ r1_tarski(k1_tops_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_14433])).

cnf(c_2229,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2228,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_7112,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_2229,c_2228])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_9,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_499,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_10,c_9])).

cnf(c_810,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_499,c_35])).

cnf(c_811,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_810])).

cnf(c_22942,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK4)))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_7112,c_811])).

cnf(c_5,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_23305,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | X0 != k2_subset_1(k2_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_22942,c_5])).

cnf(c_2225,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_6022,plain,
    ( X0 != k2_struct_0(sK4)
    | u1_struct_0(sK4) = X0 ),
    inference(resolution,[status(thm)],[c_2225,c_811])).

cnf(c_4,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_6307,plain,
    ( u1_struct_0(sK4) = k2_subset_1(k2_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_6022,c_4])).

cnf(c_23654,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(resolution,[status(thm)],[c_23305,c_6307])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_815,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_35])).

cnf(c_816,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK4,X0),k1_tops_1(sK4,X1)) ),
    inference(unflattening,[status(thm)],[c_815])).

cnf(c_7185,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_tops_1(sK4,X0))
    | ~ r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),X0) ),
    inference(instantiation,[status(thm)],[c_816])).

cnf(c_12880,plain,
    ( ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_tops_1(sK4,u1_struct_0(sK4)))
    | ~ r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_7185])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3189,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_12570,plain,
    ( m1_subset_1(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3189])).

cnf(c_2224,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6024,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_2225,c_2224])).

cnf(c_10011,plain,
    ( k2_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(resolution,[status(thm)],[c_6024,c_811])).

cnf(c_2226,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_10032,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK4))
    | r1_tarski(X1,k2_struct_0(sK4))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_10011,c_2226])).

cnf(c_2231,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_11020,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK4))
    | r1_tarski(u1_struct_0(X1),k2_struct_0(sK4))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_10032,c_2231])).

cnf(c_11022,plain,
    ( ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
    | r1_tarski(u1_struct_0(sK4),k2_struct_0(sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_11020])).

cnf(c_6249,plain,
    ( r1_tarski(X0,u1_struct_0(sK4))
    | ~ r1_tarski(X1,k2_struct_0(sK4))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_2226,c_811])).

cnf(c_6772,plain,
    ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ r1_tarski(k2_subset_1(k2_struct_0(sK4)),k2_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_6307,c_6249])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3434,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(sK4)),X0)
    | r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_7515,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3434])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_7516,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_7762,plain,
    ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6772,c_7515,c_7516])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_833,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_35])).

cnf(c_834,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k1_tops_1(sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_833])).

cnf(c_7195,plain,
    ( ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK0(k1_yellow19(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_834])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3435,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6989,plain,
    ( ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3435])).

cnf(c_11,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_771,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_36])).

cnf(c_772,plain,
    ( v3_pre_topc(k1_tops_1(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_771])).

cnf(c_776,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v3_pre_topc(k1_tops_1(sK4,X0),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_772,c_35])).

cnf(c_777,plain,
    ( v3_pre_topc(k1_tops_1(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_776])).

cnf(c_6375,plain,
    ( v3_pre_topc(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK4)
    | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_6066,plain,
    ( ~ r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),sK6)
    | r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,negated_conjecture,
    ( r2_waybel_7(sK4,sK6,sK5)
    | r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_4204,plain,
    ( r2_waybel_7(sK4,sK6,sK5)
    | ~ r2_hidden(X0,k1_yellow19(sK4,sK5))
    | r2_hidden(X0,sK6) ),
    inference(resolution,[status(thm)],[c_2,c_31])).

cnf(c_17,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_576,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_37])).

cnf(c_577,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_581,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_577,c_36,c_35])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_597,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_581,c_8])).

cnf(c_28,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X0,k1_yellow19(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_555,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X0,k1_yellow19(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_37])).

cnf(c_556,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X0,k1_yellow19(sK4,X1))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_560,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X0,k1_yellow19(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_556,c_36,c_35])).

cnf(c_1272,plain,
    ( ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,k1_yellow19(sK4,X1)) ),
    inference(resolution,[status(thm)],[c_597,c_560])).

cnf(c_1286,plain,
    ( ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,k1_yellow19(sK4,X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1272,c_8])).

cnf(c_21,plain,
    ( r2_waybel_7(X0,X1,X2)
    | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_699,plain,
    ( r2_waybel_7(X0,X1,X2)
    | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_36])).

cnf(c_700,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | m1_subset_1(sK1(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_699])).

cnf(c_704,plain,
    ( m1_subset_1(sK1(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_waybel_7(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_700,c_35])).

cnf(c_705,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | m1_subset_1(sK1(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_704])).

cnf(c_3768,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | ~ v3_pre_topc(sK1(sK4,X0,X1),sK4)
    | ~ r2_hidden(X2,sK1(sK4,X0,X1))
    | r2_hidden(sK1(sK4,X0,X1),k1_yellow19(sK4,X2)) ),
    inference(resolution,[status(thm)],[c_1286,c_705])).

cnf(c_20,plain,
    ( r2_waybel_7(X0,X1,X2)
    | v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_717,plain,
    ( r2_waybel_7(X0,X1,X2)
    | v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_36])).

cnf(c_718,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | v3_pre_topc(sK1(sK4,X0,X1),sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_717])).

cnf(c_722,plain,
    ( v3_pre_topc(sK1(sK4,X0,X1),sK4)
    | r2_waybel_7(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_718,c_35])).

cnf(c_723,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | v3_pre_topc(sK1(sK4,X0,X1),sK4) ),
    inference(renaming,[status(thm)],[c_722])).

cnf(c_1389,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X3,X2)
    | r2_hidden(X2,k1_yellow19(sK4,X3))
    | sK1(sK4,X0,X1) != X2
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_1286,c_723])).

cnf(c_1390,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | ~ m1_subset_1(sK1(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X2,sK1(sK4,X0,X1))
    | r2_hidden(sK1(sK4,X0,X1),k1_yellow19(sK4,X2)) ),
    inference(unflattening,[status(thm)],[c_1389])).

cnf(c_1394,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | ~ r2_hidden(X2,sK1(sK4,X0,X1))
    | r2_hidden(sK1(sK4,X0,X1),k1_yellow19(sK4,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1390,c_35,c_700])).

cnf(c_3773,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | ~ r2_hidden(X2,sK1(sK4,X0,X1))
    | r2_hidden(sK1(sK4,X0,X1),k1_yellow19(sK4,X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3768,c_35,c_700,c_1390])).

cnf(c_4426,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | r2_waybel_7(sK4,sK6,sK5)
    | r2_hidden(sK1(sK4,X0,X1),sK6)
    | ~ r2_hidden(sK5,sK1(sK4,X0,X1)) ),
    inference(resolution,[status(thm)],[c_4204,c_3773])).

cnf(c_18,plain,
    ( r2_waybel_7(X0,X1,X2)
    | ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_753,plain,
    ( r2_waybel_7(X0,X1,X2)
    | ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_36])).

cnf(c_754,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | ~ r2_hidden(sK1(sK4,X0,X1),X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_753])).

cnf(c_758,plain,
    ( ~ r2_hidden(sK1(sK4,X0,X1),X0)
    | r2_waybel_7(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_754,c_35])).

cnf(c_759,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | ~ r2_hidden(sK1(sK4,X0,X1),X0) ),
    inference(renaming,[status(thm)],[c_758])).

cnf(c_4814,plain,
    ( r2_waybel_7(sK4,sK6,X0)
    | r2_waybel_7(sK4,sK6,sK5)
    | ~ r2_hidden(sK5,sK1(sK4,sK6,X0)) ),
    inference(resolution,[status(thm)],[c_4426,c_759])).

cnf(c_19,plain,
    ( r2_waybel_7(X0,X1,X2)
    | r2_hidden(X2,sK1(X0,X1,X2))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_735,plain,
    ( r2_waybel_7(X0,X1,X2)
    | r2_hidden(X2,sK1(X0,X1,X2))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_36])).

cnf(c_736,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | r2_hidden(X1,sK1(sK4,X0,X1))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_735])).

cnf(c_740,plain,
    ( r2_hidden(X1,sK1(sK4,X0,X1))
    | r2_waybel_7(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_736,c_35])).

cnf(c_741,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | r2_hidden(X1,sK1(sK4,X0,X1)) ),
    inference(renaming,[status(thm)],[c_740])).

cnf(c_4826,plain,
    ( r2_waybel_7(sK4,sK6,sK5) ),
    inference(resolution,[status(thm)],[c_4814,c_741])).

cnf(c_3054,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3167,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_3054])).

cnf(c_3033,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(k1_tops_1(sK4,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_834])).

cnf(c_4705,plain,
    ( r1_tarski(k1_tops_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3167,c_3033])).

cnf(c_4709,plain,
    ( r1_tarski(k1_tops_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4705])).

cnf(c_29,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k1_yellow19(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_534,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k1_yellow19(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_37])).

cnf(c_535,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,k1_yellow19(sK4,X1))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_539,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,k1_yellow19(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_36,c_35])).

cnf(c_15,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_16,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_16])).

cnf(c_224,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_223])).

cnf(c_513,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_224,c_37])).

cnf(c_514,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k1_tops_1(sK4,X0))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_518,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k1_tops_1(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_36,c_35])).

cnf(c_1331,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k1_yellow19(sK4,X0))
    | r2_hidden(X0,k1_tops_1(sK4,X1)) ),
    inference(resolution,[status(thm)],[c_539,c_518])).

cnf(c_4461,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),k1_yellow19(sK4,sK5))
    | r2_hidden(sK5,k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6))) ),
    inference(instantiation,[status(thm)],[c_1331])).

cnf(c_605,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_37])).

cnf(c_606,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_610,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_606,c_36,c_35])).

cnf(c_1316,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,k1_yellow19(sK4,X0)) ),
    inference(resolution,[status(thm)],[c_539,c_610])).

cnf(c_4462,plain,
    ( m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),k1_yellow19(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1316])).

cnf(c_3218,plain,
    ( r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),k1_yellow19(sK4,sK5))
    | r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2255,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2224])).

cnf(c_30,negated_conjecture,
    ( ~ r2_waybel_7(sK4,sK6,sK5)
    | ~ r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_33,negated_conjecture,
    ( v13_waybel_0(sK6,k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f102])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_113726,c_57627,c_29534,c_27231,c_23654,c_12880,c_12570,c_11022,c_7762,c_7195,c_6989,c_6375,c_6066,c_4826,c_4709,c_4461,c_4462,c_3218,c_2255,c_30,c_32,c_33,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 27.63/3.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.63/3.99  
% 27.63/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.63/3.99  
% 27.63/3.99  ------  iProver source info
% 27.63/3.99  
% 27.63/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.63/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.63/3.99  git: non_committed_changes: false
% 27.63/3.99  git: last_make_outside_of_git: false
% 27.63/3.99  
% 27.63/3.99  ------ 
% 27.63/3.99  ------ Parsing...
% 27.63/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.63/3.99  
% 27.63/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 27.63/3.99  
% 27.63/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.63/3.99  
% 27.63/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.63/3.99  ------ Proving...
% 27.63/3.99  ------ Problem Properties 
% 27.63/3.99  
% 27.63/3.99  
% 27.63/3.99  clauses                                 33
% 27.63/3.99  conjectures                             5
% 27.63/3.99  EPR                                     2
% 27.63/3.99  Horn                                    25
% 27.63/3.99  unary                                   6
% 27.63/3.99  binary                                  12
% 27.63/3.99  lits                                    84
% 27.63/3.99  lits eq                                 2
% 27.63/3.99  fd_pure                                 0
% 27.63/3.99  fd_pseudo                               0
% 27.63/3.99  fd_cond                                 0
% 27.63/3.99  fd_pseudo_cond                          0
% 27.63/3.99  AC symbols                              0
% 27.63/3.99  
% 27.63/3.99  ------ Input Options Time Limit: Unbounded
% 27.63/3.99  
% 27.63/3.99  
% 27.63/3.99  ------ 
% 27.63/3.99  Current options:
% 27.63/3.99  ------ 
% 27.63/3.99  
% 27.63/3.99  
% 27.63/3.99  
% 27.63/3.99  
% 27.63/3.99  ------ Proving...
% 27.63/3.99  
% 27.63/3.99  
% 27.63/3.99  % SZS status Theorem for theBenchmark.p
% 27.63/3.99  
% 27.63/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.63/3.99  
% 27.63/3.99  fof(f17,axiom,(
% 27.63/3.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) => (v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : ((r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => r2_hidden(X3,X1))))),
% 27.63/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/3.99  
% 27.63/3.99  fof(f41,plain,(
% 27.63/3.99    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | (~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 27.63/3.99    inference(ennf_transformation,[],[f17])).
% 27.63/3.99  
% 27.63/3.99  fof(f42,plain,(
% 27.63/3.99    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 27.63/3.99    inference(flattening,[],[f41])).
% 27.63/3.99  
% 27.63/3.99  fof(f57,plain,(
% 27.63/3.99    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 27.63/3.99    inference(nnf_transformation,[],[f42])).
% 27.63/3.99  
% 27.63/3.99  fof(f58,plain,(
% 27.63/3.99    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 27.63/3.99    inference(rectify,[],[f57])).
% 27.63/3.99  
% 27.63/3.99  fof(f59,plain,(
% 27.63/3.99    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK2(X0,X1),X1) & r1_tarski(sK3(X0,X1),X0) & r1_tarski(sK2(X0,X1),sK3(X0,X1))))),
% 27.63/3.99    introduced(choice_axiom,[])).
% 27.63/3.99  
% 27.63/3.99  fof(f60,plain,(
% 27.63/3.99    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK2(X0,X1),X1) & r1_tarski(sK3(X0,X1),X0) & r1_tarski(sK2(X0,X1),sK3(X0,X1)))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 27.63/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f58,f59])).
% 27.63/3.99  
% 27.63/3.99  fof(f92,plain,(
% 27.63/3.99    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))) )),
% 27.63/3.99    inference(cnf_transformation,[],[f60])).
% 27.63/3.99  
% 27.63/3.99  fof(f15,axiom,(
% 27.63/3.99    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 27.63/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/3.99  
% 27.63/3.99  fof(f86,plain,(
% 27.63/3.99    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 27.63/3.99    inference(cnf_transformation,[],[f15])).
% 27.63/3.99  
% 27.63/3.99  fof(f111,plain,(
% 27.63/3.99    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))) )),
% 27.63/3.99    inference(definition_unfolding,[],[f92,f86,f86])).
% 27.63/3.99  
% 27.63/3.99  fof(f16,axiom,(
% 27.63/3.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,X3) & v3_pre_topc(X3,X0)) => r2_hidden(X3,X1)))))),
% 27.63/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/3.99  
% 27.63/3.99  fof(f39,plain,(
% 27.63/3.99    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : ((r2_hidden(X3,X1) | (~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.63/3.99    inference(ennf_transformation,[],[f16])).
% 27.63/3.99  
% 27.63/3.99  fof(f40,plain,(
% 27.63/3.99    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.63/3.99    inference(flattening,[],[f39])).
% 27.63/3.99  
% 27.63/3.99  fof(f53,plain,(
% 27.63/3.99    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | ? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.63/3.99    inference(nnf_transformation,[],[f40])).
% 27.63/3.99  
% 27.63/3.99  fof(f54,plain,(
% 27.63/3.99    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | ? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.63/3.99    inference(rectify,[],[f53])).
% 27.63/3.99  
% 27.63/3.99  fof(f55,plain,(
% 27.63/3.99    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(X2,sK1(X0,X1,X2)) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 27.63/3.99    introduced(choice_axiom,[])).
% 27.63/3.99  
% 27.63/3.99  fof(f56,plain,(
% 27.63/3.99    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | (~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(X2,sK1(X0,X1,X2)) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.63/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f54,f55])).
% 27.63/3.99  
% 27.63/3.99  fof(f87,plain,(
% 27.63/3.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_waybel_7(X0,X1,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f56])).
% 27.63/3.99  
% 27.63/3.99  fof(f19,conjecture,(
% 27.63/3.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => (r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)))))),
% 27.63/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/3.99  
% 27.63/3.99  fof(f20,negated_conjecture,(
% 27.63/3.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => (r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)))))),
% 27.63/3.99    inference(negated_conjecture,[],[f19])).
% 27.63/3.99  
% 27.63/3.99  fof(f45,plain,(
% 27.63/3.99    ? [X0] : (? [X1] : (? [X2] : ((r2_waybel_7(X0,X2,X1) <~> r1_tarski(k1_yellow19(X0,X1),X2)) & (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 27.63/3.99    inference(ennf_transformation,[],[f20])).
% 27.63/3.99  
% 27.63/3.99  fof(f46,plain,(
% 27.63/3.99    ? [X0] : (? [X1] : (? [X2] : ((r2_waybel_7(X0,X2,X1) <~> r1_tarski(k1_yellow19(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 27.63/3.99    inference(flattening,[],[f45])).
% 27.63/3.99  
% 27.63/3.99  fof(f62,plain,(
% 27.63/3.99    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 27.63/3.99    inference(nnf_transformation,[],[f46])).
% 27.63/3.99  
% 27.63/3.99  fof(f63,plain,(
% 27.63/3.99    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 27.63/3.99    inference(flattening,[],[f62])).
% 27.63/3.99  
% 27.63/3.99  fof(f66,plain,(
% 27.63/3.99    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => ((~r1_tarski(k1_yellow19(X0,X1),sK6) | ~r2_waybel_7(X0,sK6,X1)) & (r1_tarski(k1_yellow19(X0,X1),sK6) | r2_waybel_7(X0,sK6,X1)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK6,k3_yellow_1(k2_struct_0(X0))))) )),
% 27.63/3.99    introduced(choice_axiom,[])).
% 27.63/3.99  
% 27.63/3.99  fof(f65,plain,(
% 27.63/3.99    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~r1_tarski(k1_yellow19(X0,sK5),X2) | ~r2_waybel_7(X0,X2,sK5)) & (r1_tarski(k1_yellow19(X0,sK5),X2) | r2_waybel_7(X0,X2,sK5)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 27.63/3.99    introduced(choice_axiom,[])).
% 27.63/3.99  
% 27.63/3.99  fof(f64,plain,(
% 27.63/3.99    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(sK4,X1),X2) | ~r2_waybel_7(sK4,X2,X1)) & (r1_tarski(k1_yellow19(sK4,X1),X2) | r2_waybel_7(sK4,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK4)))) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 27.63/3.99    introduced(choice_axiom,[])).
% 27.63/3.99  
% 27.63/3.99  fof(f67,plain,(
% 27.63/3.99    (((~r1_tarski(k1_yellow19(sK4,sK5),sK6) | ~r2_waybel_7(sK4,sK6,sK5)) & (r1_tarski(k1_yellow19(sK4,sK5),sK6) | r2_waybel_7(sK4,sK6,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) & v13_waybel_0(sK6,k3_yellow_1(k2_struct_0(sK4)))) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 27.63/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f63,f66,f65,f64])).
% 27.63/3.99  
% 27.63/3.99  fof(f100,plain,(
% 27.63/3.99    v2_pre_topc(sK4)),
% 27.63/3.99    inference(cnf_transformation,[],[f67])).
% 27.63/3.99  
% 27.63/3.99  fof(f101,plain,(
% 27.63/3.99    l1_pre_topc(sK4)),
% 27.63/3.99    inference(cnf_transformation,[],[f67])).
% 27.63/3.99  
% 27.63/3.99  fof(f2,axiom,(
% 27.63/3.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 27.63/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/3.99  
% 27.63/3.99  fof(f22,plain,(
% 27.63/3.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 27.63/3.99    inference(ennf_transformation,[],[f2])).
% 27.63/3.99  
% 27.63/3.99  fof(f23,plain,(
% 27.63/3.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 27.63/3.99    inference(flattening,[],[f22])).
% 27.63/3.99  
% 27.63/3.99  fof(f71,plain,(
% 27.63/3.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f23])).
% 27.63/3.99  
% 27.63/3.99  fof(f8,axiom,(
% 27.63/3.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 27.63/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/3.99  
% 27.63/3.99  fof(f27,plain,(
% 27.63/3.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 27.63/3.99    inference(ennf_transformation,[],[f8])).
% 27.63/3.99  
% 27.63/3.99  fof(f78,plain,(
% 27.63/3.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f27])).
% 27.63/3.99  
% 27.63/3.99  fof(f7,axiom,(
% 27.63/3.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 27.63/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/3.99  
% 27.63/3.99  fof(f26,plain,(
% 27.63/3.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 27.63/3.99    inference(ennf_transformation,[],[f7])).
% 27.63/3.99  
% 27.63/3.99  fof(f77,plain,(
% 27.63/3.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f26])).
% 27.63/3.99  
% 27.63/3.99  fof(f4,axiom,(
% 27.63/3.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 27.63/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/3.99  
% 27.63/3.99  fof(f73,plain,(
% 27.63/3.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 27.63/3.99    inference(cnf_transformation,[],[f4])).
% 27.63/3.99  
% 27.63/3.99  fof(f3,axiom,(
% 27.63/3.99    ! [X0] : k2_subset_1(X0) = X0),
% 27.63/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/3.99  
% 27.63/3.99  fof(f72,plain,(
% 27.63/3.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 27.63/3.99    inference(cnf_transformation,[],[f3])).
% 27.63/3.99  
% 27.63/3.99  fof(f11,axiom,(
% 27.63/3.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 27.63/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/3.99  
% 27.63/3.99  fof(f31,plain,(
% 27.63/3.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.63/3.99    inference(ennf_transformation,[],[f11])).
% 27.63/3.99  
% 27.63/3.99  fof(f32,plain,(
% 27.63/3.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.63/3.99    inference(flattening,[],[f31])).
% 27.63/3.99  
% 27.63/3.99  fof(f81,plain,(
% 27.63/3.99    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f32])).
% 27.63/3.99  
% 27.63/3.99  fof(f5,axiom,(
% 27.63/3.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 27.63/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/3.99  
% 27.63/3.99  fof(f51,plain,(
% 27.63/3.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 27.63/3.99    inference(nnf_transformation,[],[f5])).
% 27.63/3.99  
% 27.63/3.99  fof(f75,plain,(
% 27.63/3.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f51])).
% 27.63/3.99  
% 27.63/3.99  fof(f1,axiom,(
% 27.63/3.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 27.63/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/3.99  
% 27.63/3.99  fof(f21,plain,(
% 27.63/3.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 27.63/3.99    inference(ennf_transformation,[],[f1])).
% 27.63/3.99  
% 27.63/3.99  fof(f47,plain,(
% 27.63/3.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 27.63/3.99    inference(nnf_transformation,[],[f21])).
% 27.63/3.99  
% 27.63/3.99  fof(f48,plain,(
% 27.63/3.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 27.63/3.99    inference(rectify,[],[f47])).
% 27.63/3.99  
% 27.63/3.99  fof(f49,plain,(
% 27.63/3.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 27.63/3.99    introduced(choice_axiom,[])).
% 27.63/3.99  
% 27.63/3.99  fof(f50,plain,(
% 27.63/3.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 27.63/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).
% 27.63/3.99  
% 27.63/3.99  fof(f69,plain,(
% 27.63/3.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f50])).
% 27.63/3.99  
% 27.63/3.99  fof(f70,plain,(
% 27.63/3.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f50])).
% 27.63/3.99  
% 27.63/3.99  fof(f10,axiom,(
% 27.63/3.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 27.63/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/3.99  
% 27.63/3.99  fof(f30,plain,(
% 27.63/3.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.63/3.99    inference(ennf_transformation,[],[f10])).
% 27.63/3.99  
% 27.63/3.99  fof(f80,plain,(
% 27.63/3.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f30])).
% 27.63/3.99  
% 27.63/3.99  fof(f74,plain,(
% 27.63/3.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 27.63/3.99    inference(cnf_transformation,[],[f51])).
% 27.63/3.99  
% 27.63/3.99  fof(f9,axiom,(
% 27.63/3.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 27.63/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/3.99  
% 27.63/3.99  fof(f28,plain,(
% 27.63/3.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.63/3.99    inference(ennf_transformation,[],[f9])).
% 27.63/3.99  
% 27.63/3.99  fof(f29,plain,(
% 27.63/3.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.63/3.99    inference(flattening,[],[f28])).
% 27.63/3.99  
% 27.63/3.99  fof(f79,plain,(
% 27.63/3.99    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f29])).
% 27.63/3.99  
% 27.63/3.99  fof(f68,plain,(
% 27.63/3.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f50])).
% 27.63/3.99  
% 27.63/3.99  fof(f105,plain,(
% 27.63/3.99    r1_tarski(k1_yellow19(sK4,sK5),sK6) | r2_waybel_7(sK4,sK6,sK5)),
% 27.63/3.99    inference(cnf_transformation,[],[f67])).
% 27.63/3.99  
% 27.63/3.99  fof(f14,axiom,(
% 27.63/3.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 27.63/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/3.99  
% 27.63/3.99  fof(f37,plain,(
% 27.63/3.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 27.63/3.99    inference(ennf_transformation,[],[f14])).
% 27.63/3.99  
% 27.63/3.99  fof(f38,plain,(
% 27.63/3.99    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.63/3.99    inference(flattening,[],[f37])).
% 27.63/3.99  
% 27.63/3.99  fof(f85,plain,(
% 27.63/3.99    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f38])).
% 27.63/3.99  
% 27.63/3.99  fof(f99,plain,(
% 27.63/3.99    ~v2_struct_0(sK4)),
% 27.63/3.99    inference(cnf_transformation,[],[f67])).
% 27.63/3.99  
% 27.63/3.99  fof(f6,axiom,(
% 27.63/3.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 27.63/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/3.99  
% 27.63/3.99  fof(f24,plain,(
% 27.63/3.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 27.63/3.99    inference(ennf_transformation,[],[f6])).
% 27.63/3.99  
% 27.63/3.99  fof(f25,plain,(
% 27.63/3.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 27.63/3.99    inference(flattening,[],[f24])).
% 27.63/3.99  
% 27.63/3.99  fof(f76,plain,(
% 27.63/3.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f25])).
% 27.63/3.99  
% 27.63/3.99  fof(f18,axiom,(
% 27.63/3.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1))))),
% 27.63/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/3.99  
% 27.63/3.99  fof(f43,plain,(
% 27.63/3.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 27.63/3.99    inference(ennf_transformation,[],[f18])).
% 27.63/3.99  
% 27.63/3.99  fof(f44,plain,(
% 27.63/3.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.63/3.99    inference(flattening,[],[f43])).
% 27.63/3.99  
% 27.63/3.99  fof(f61,plain,(
% 27.63/3.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_connsp_2(X2,X0,X1)) & (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X2,k1_yellow19(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.63/3.99    inference(nnf_transformation,[],[f44])).
% 27.63/3.99  
% 27.63/3.99  fof(f98,plain,(
% 27.63/3.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f61])).
% 27.63/3.99  
% 27.63/3.99  fof(f88,plain,(
% 27.63/3.99    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f56])).
% 27.63/3.99  
% 27.63/3.99  fof(f89,plain,(
% 27.63/3.99    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | v3_pre_topc(sK1(X0,X1,X2),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f56])).
% 27.63/3.99  
% 27.63/3.99  fof(f91,plain,(
% 27.63/3.99    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | ~r2_hidden(sK1(X0,X1,X2),X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f56])).
% 27.63/3.99  
% 27.63/3.99  fof(f90,plain,(
% 27.63/3.99    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,sK1(X0,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f56])).
% 27.63/3.99  
% 27.63/3.99  fof(f97,plain,(
% 27.63/3.99    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.63/3.99    inference(cnf_transformation,[],[f61])).
% 27.63/3.99  
% 27.63/3.99  fof(f12,axiom,(
% 27.63/3.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 27.63/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/4.00  
% 27.63/4.00  fof(f33,plain,(
% 27.63/4.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 27.63/4.00    inference(ennf_transformation,[],[f12])).
% 27.63/4.00  
% 27.63/4.00  fof(f34,plain,(
% 27.63/4.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.63/4.00    inference(flattening,[],[f33])).
% 27.63/4.00  
% 27.63/4.00  fof(f52,plain,(
% 27.63/4.00    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.63/4.00    inference(nnf_transformation,[],[f34])).
% 27.63/4.00  
% 27.63/4.00  fof(f82,plain,(
% 27.63/4.00    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.63/4.00    inference(cnf_transformation,[],[f52])).
% 27.63/4.00  
% 27.63/4.00  fof(f13,axiom,(
% 27.63/4.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 27.63/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.63/4.00  
% 27.63/4.00  fof(f35,plain,(
% 27.63/4.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 27.63/4.00    inference(ennf_transformation,[],[f13])).
% 27.63/4.00  
% 27.63/4.00  fof(f36,plain,(
% 27.63/4.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.63/4.00    inference(flattening,[],[f35])).
% 27.63/4.00  
% 27.63/4.00  fof(f84,plain,(
% 27.63/4.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.63/4.00    inference(cnf_transformation,[],[f36])).
% 27.63/4.00  
% 27.63/4.00  fof(f106,plain,(
% 27.63/4.00    ~r1_tarski(k1_yellow19(sK4,sK5),sK6) | ~r2_waybel_7(sK4,sK6,sK5)),
% 27.63/4.00    inference(cnf_transformation,[],[f67])).
% 27.63/4.00  
% 27.63/4.00  fof(f104,plain,(
% 27.63/4.00    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))),
% 27.63/4.00    inference(cnf_transformation,[],[f67])).
% 27.63/4.00  
% 27.63/4.00  fof(f112,plain,(
% 27.63/4.00    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))))),
% 27.63/4.00    inference(definition_unfolding,[],[f104,f86])).
% 27.63/4.00  
% 27.63/4.00  fof(f103,plain,(
% 27.63/4.00    v13_waybel_0(sK6,k3_yellow_1(k2_struct_0(sK4)))),
% 27.63/4.00    inference(cnf_transformation,[],[f67])).
% 27.63/4.00  
% 27.63/4.00  fof(f113,plain,(
% 27.63/4.00    v13_waybel_0(sK6,k3_lattice3(k1_lattice3(k2_struct_0(sK4))))),
% 27.63/4.00    inference(definition_unfolding,[],[f103,f86])).
% 27.63/4.00  
% 27.63/4.00  fof(f102,plain,(
% 27.63/4.00    m1_subset_1(sK5,u1_struct_0(sK4))),
% 27.63/4.00    inference(cnf_transformation,[],[f67])).
% 27.63/4.00  
% 27.63/4.00  cnf(c_27,plain,
% 27.63/4.00      ( ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 27.63/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 27.63/4.00      | ~ r2_hidden(X2,X0)
% 27.63/4.00      | r2_hidden(X3,X0)
% 27.63/4.00      | ~ r1_tarski(X3,X1)
% 27.63/4.00      | ~ r1_tarski(X2,X3) ),
% 27.63/4.00      inference(cnf_transformation,[],[f111]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_106170,plain,
% 27.63/4.00      ( ~ v13_waybel_0(sK6,k3_lattice3(k1_lattice3(k2_struct_0(sK4))))
% 27.63/4.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))))
% 27.63/4.00      | ~ r2_hidden(X0,sK6)
% 27.63/4.00      | r2_hidden(X1,sK6)
% 27.63/4.00      | ~ r1_tarski(X0,X1)
% 27.63/4.00      | ~ r1_tarski(X1,k2_struct_0(sK4)) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_27]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_108822,plain,
% 27.63/4.00      ( ~ v13_waybel_0(sK6,k3_lattice3(k1_lattice3(k2_struct_0(sK4))))
% 27.63/4.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))))
% 27.63/4.00      | r2_hidden(X0,sK6)
% 27.63/4.00      | ~ r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK6)
% 27.63/4.00      | ~ r1_tarski(X0,k2_struct_0(sK4))
% 27.63/4.00      | ~ r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),X0) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_106170]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_113726,plain,
% 27.63/4.00      ( ~ v13_waybel_0(sK6,k3_lattice3(k1_lattice3(k2_struct_0(sK4))))
% 27.63/4.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))))
% 27.63/4.00      | ~ r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK6)
% 27.63/4.00      | r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),sK6)
% 27.63/4.00      | ~ r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK0(k1_yellow19(sK4,sK5),sK6))
% 27.63/4.00      | ~ r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),k2_struct_0(sK4)) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_108822]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_22,plain,
% 27.63/4.00      ( ~ r2_waybel_7(X0,X1,X2)
% 27.63/4.00      | ~ v3_pre_topc(X3,X0)
% 27.63/4.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 27.63/4.00      | ~ r2_hidden(X2,X3)
% 27.63/4.00      | r2_hidden(X3,X1)
% 27.63/4.00      | ~ v2_pre_topc(X0)
% 27.63/4.00      | ~ l1_pre_topc(X0) ),
% 27.63/4.00      inference(cnf_transformation,[],[f87]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_36,negated_conjecture,
% 27.63/4.00      ( v2_pre_topc(sK4) ),
% 27.63/4.00      inference(cnf_transformation,[],[f100]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_676,plain,
% 27.63/4.00      ( ~ r2_waybel_7(X0,X1,X2)
% 27.63/4.00      | ~ v3_pre_topc(X3,X0)
% 27.63/4.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 27.63/4.00      | ~ r2_hidden(X2,X3)
% 27.63/4.00      | r2_hidden(X3,X1)
% 27.63/4.00      | ~ l1_pre_topc(X0)
% 27.63/4.00      | sK4 != X0 ),
% 27.63/4.00      inference(resolution_lifted,[status(thm)],[c_22,c_36]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_677,plain,
% 27.63/4.00      ( ~ r2_waybel_7(sK4,X0,X1)
% 27.63/4.00      | ~ v3_pre_topc(X2,sK4)
% 27.63/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ r2_hidden(X1,X2)
% 27.63/4.00      | r2_hidden(X2,X0)
% 27.63/4.00      | ~ l1_pre_topc(sK4) ),
% 27.63/4.00      inference(unflattening,[status(thm)],[c_676]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_35,negated_conjecture,
% 27.63/4.00      ( l1_pre_topc(sK4) ),
% 27.63/4.00      inference(cnf_transformation,[],[f101]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_679,plain,
% 27.63/4.00      ( r2_hidden(X2,X0)
% 27.63/4.00      | ~ r2_hidden(X1,X2)
% 27.63/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ v3_pre_topc(X2,sK4)
% 27.63/4.00      | ~ r2_waybel_7(sK4,X0,X1) ),
% 27.63/4.00      inference(global_propositional_subsumption,
% 27.63/4.00                [status(thm)],
% 27.63/4.00                [c_677,c_35]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_680,plain,
% 27.63/4.00      ( ~ r2_waybel_7(sK4,X0,X1)
% 27.63/4.00      | ~ v3_pre_topc(X2,sK4)
% 27.63/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ r2_hidden(X1,X2)
% 27.63/4.00      | r2_hidden(X2,X0) ),
% 27.63/4.00      inference(renaming,[status(thm)],[c_679]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_5828,plain,
% 27.63/4.00      ( ~ r2_waybel_7(sK4,X0,sK5)
% 27.63/4.00      | ~ v3_pre_topc(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK4)
% 27.63/4.00      | ~ m1_subset_1(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),X0)
% 27.63/4.00      | ~ r2_hidden(sK5,k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6))) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_680]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_57627,plain,
% 27.63/4.00      ( ~ r2_waybel_7(sK4,sK6,sK5)
% 27.63/4.00      | ~ v3_pre_topc(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK4)
% 27.63/4.00      | ~ m1_subset_1(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK6)
% 27.63/4.00      | ~ r2_hidden(sK5,k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6))) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_5828]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_3,plain,
% 27.63/4.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 27.63/4.00      inference(cnf_transformation,[],[f71]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_6475,plain,
% 27.63/4.00      ( ~ r1_tarski(X0,X1)
% 27.63/4.00      | ~ r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),X0)
% 27.63/4.00      | r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),X1) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_3]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_16129,plain,
% 27.63/4.00      ( r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),X0)
% 27.63/4.00      | ~ r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),u1_struct_0(sK4))
% 27.63/4.00      | ~ r1_tarski(u1_struct_0(sK4),X0) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_6475]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_29534,plain,
% 27.63/4.00      ( ~ r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),u1_struct_0(sK4))
% 27.63/4.00      | r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),k2_struct_0(sK4))
% 27.63/4.00      | ~ r1_tarski(u1_struct_0(sK4),k2_struct_0(sK4)) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_16129]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_3444,plain,
% 27.63/4.00      ( ~ r1_tarski(X0,X1)
% 27.63/4.00      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 27.63/4.00      | r1_tarski(X0,u1_struct_0(sK4)) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_3]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_7686,plain,
% 27.63/4.00      ( ~ r1_tarski(X0,k1_tops_1(sK4,u1_struct_0(sK4)))
% 27.63/4.00      | r1_tarski(X0,u1_struct_0(sK4))
% 27.63/4.00      | ~ r1_tarski(k1_tops_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_3444]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_14433,plain,
% 27.63/4.00      ( ~ r1_tarski(k1_tops_1(sK4,X0),k1_tops_1(sK4,u1_struct_0(sK4)))
% 27.63/4.00      | r1_tarski(k1_tops_1(sK4,X0),u1_struct_0(sK4))
% 27.63/4.00      | ~ r1_tarski(k1_tops_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_7686]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_27231,plain,
% 27.63/4.00      ( ~ r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_tops_1(sK4,u1_struct_0(sK4)))
% 27.63/4.00      | r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),u1_struct_0(sK4))
% 27.63/4.00      | ~ r1_tarski(k1_tops_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_14433]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_2229,plain,
% 27.63/4.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.63/4.00      theory(equality) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_2228,plain,
% 27.63/4.00      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 27.63/4.00      theory(equality) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_7112,plain,
% 27.63/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.63/4.00      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 27.63/4.00      | X2 != X0
% 27.63/4.00      | X3 != X1 ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_2229,c_2228]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_10,plain,
% 27.63/4.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 27.63/4.00      inference(cnf_transformation,[],[f78]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_9,plain,
% 27.63/4.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 27.63/4.00      inference(cnf_transformation,[],[f77]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_499,plain,
% 27.63/4.00      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_10,c_9]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_810,plain,
% 27.63/4.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK4 != X0 ),
% 27.63/4.00      inference(resolution_lifted,[status(thm)],[c_499,c_35]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_811,plain,
% 27.63/4.00      ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
% 27.63/4.00      inference(unflattening,[status(thm)],[c_810]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_22942,plain,
% 27.63/4.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK4)))
% 27.63/4.00      | X0 != X1 ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_7112,c_811]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_5,plain,
% 27.63/4.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 27.63/4.00      inference(cnf_transformation,[],[f73]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_23305,plain,
% 27.63/4.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | X0 != k2_subset_1(k2_struct_0(sK4)) ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_22942,c_5]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_2225,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_6022,plain,
% 27.63/4.00      ( X0 != k2_struct_0(sK4) | u1_struct_0(sK4) = X0 ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_2225,c_811]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_4,plain,
% 27.63/4.00      ( k2_subset_1(X0) = X0 ),
% 27.63/4.00      inference(cnf_transformation,[],[f72]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_6307,plain,
% 27.63/4.00      ( u1_struct_0(sK4) = k2_subset_1(k2_struct_0(sK4)) ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_6022,c_4]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_23654,plain,
% 27.63/4.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_23305,c_6307]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_13,plain,
% 27.63/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.63/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.63/4.00      | ~ r1_tarski(X0,X2)
% 27.63/4.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 27.63/4.00      | ~ l1_pre_topc(X1) ),
% 27.63/4.00      inference(cnf_transformation,[],[f81]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_815,plain,
% 27.63/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.63/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.63/4.00      | ~ r1_tarski(X0,X2)
% 27.63/4.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 27.63/4.00      | sK4 != X1 ),
% 27.63/4.00      inference(resolution_lifted,[status(thm)],[c_13,c_35]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_816,plain,
% 27.63/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ r1_tarski(X0,X1)
% 27.63/4.00      | r1_tarski(k1_tops_1(sK4,X0),k1_tops_1(sK4,X1)) ),
% 27.63/4.00      inference(unflattening,[status(thm)],[c_815]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_7185,plain,
% 27.63/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_tops_1(sK4,X0))
% 27.63/4.00      | ~ r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),X0) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_816]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_12880,plain,
% 27.63/4.00      ( ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_tops_1(sK4,u1_struct_0(sK4)))
% 27.63/4.00      | ~ r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),u1_struct_0(sK4)) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_7185]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_6,plain,
% 27.63/4.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.63/4.00      inference(cnf_transformation,[],[f75]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_3189,plain,
% 27.63/4.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ r1_tarski(X0,u1_struct_0(sK4)) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_6]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_12570,plain,
% 27.63/4.00      ( m1_subset_1(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),u1_struct_0(sK4)) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_3189]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_2224,plain,( X0 = X0 ),theory(equality) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_6024,plain,
% 27.63/4.00      ( X0 != X1 | X1 = X0 ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_2225,c_2224]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_10011,plain,
% 27.63/4.00      ( k2_struct_0(sK4) = u1_struct_0(sK4) ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_6024,c_811]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_2226,plain,
% 27.63/4.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.63/4.00      theory(equality) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_10032,plain,
% 27.63/4.00      ( ~ r1_tarski(X0,u1_struct_0(sK4))
% 27.63/4.00      | r1_tarski(X1,k2_struct_0(sK4))
% 27.63/4.00      | X1 != X0 ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_10011,c_2226]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_2231,plain,
% 27.63/4.00      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 27.63/4.00      theory(equality) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_11020,plain,
% 27.63/4.00      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK4))
% 27.63/4.00      | r1_tarski(u1_struct_0(X1),k2_struct_0(sK4))
% 27.63/4.00      | X1 != X0 ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_10032,c_2231]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_11022,plain,
% 27.63/4.00      ( ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
% 27.63/4.00      | r1_tarski(u1_struct_0(sK4),k2_struct_0(sK4))
% 27.63/4.00      | sK4 != sK4 ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_11020]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_6249,plain,
% 27.63/4.00      ( r1_tarski(X0,u1_struct_0(sK4))
% 27.63/4.00      | ~ r1_tarski(X1,k2_struct_0(sK4))
% 27.63/4.00      | X0 != X1 ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_2226,c_811]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_6772,plain,
% 27.63/4.00      ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4))
% 27.63/4.00      | ~ r1_tarski(k2_subset_1(k2_struct_0(sK4)),k2_struct_0(sK4)) ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_6307,c_6249]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_1,plain,
% 27.63/4.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 27.63/4.00      inference(cnf_transformation,[],[f69]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_3434,plain,
% 27.63/4.00      ( r2_hidden(sK0(X0,u1_struct_0(sK4)),X0)
% 27.63/4.00      | r1_tarski(X0,u1_struct_0(sK4)) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_1]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_7515,plain,
% 27.63/4.00      ( r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
% 27.63/4.00      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_3434]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_0,plain,
% 27.63/4.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 27.63/4.00      inference(cnf_transformation,[],[f70]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_7516,plain,
% 27.63/4.00      ( ~ r2_hidden(sK0(u1_struct_0(sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
% 27.63/4.00      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_0]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_7762,plain,
% 27.63/4.00      ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
% 27.63/4.00      inference(global_propositional_subsumption,
% 27.63/4.00                [status(thm)],
% 27.63/4.00                [c_6772,c_7515,c_7516]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_12,plain,
% 27.63/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.63/4.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 27.63/4.00      | ~ l1_pre_topc(X1) ),
% 27.63/4.00      inference(cnf_transformation,[],[f80]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_833,plain,
% 27.63/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.63/4.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 27.63/4.00      | sK4 != X1 ),
% 27.63/4.00      inference(resolution_lifted,[status(thm)],[c_12,c_35]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_834,plain,
% 27.63/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | r1_tarski(k1_tops_1(sK4,X0),X0) ),
% 27.63/4.00      inference(unflattening,[status(thm)],[c_833]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_7195,plain,
% 27.63/4.00      ( ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK0(k1_yellow19(sK4,sK5),sK6)) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_834]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_7,plain,
% 27.63/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 27.63/4.00      inference(cnf_transformation,[],[f74]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_3435,plain,
% 27.63/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | r1_tarski(X0,u1_struct_0(sK4)) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_7]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_6989,plain,
% 27.63/4.00      ( ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),u1_struct_0(sK4)) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_3435]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_11,plain,
% 27.63/4.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 27.63/4.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 27.63/4.00      | ~ v2_pre_topc(X0)
% 27.63/4.00      | ~ l1_pre_topc(X0) ),
% 27.63/4.00      inference(cnf_transformation,[],[f79]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_771,plain,
% 27.63/4.00      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 27.63/4.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 27.63/4.00      | ~ l1_pre_topc(X0)
% 27.63/4.00      | sK4 != X0 ),
% 27.63/4.00      inference(resolution_lifted,[status(thm)],[c_11,c_36]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_772,plain,
% 27.63/4.00      ( v3_pre_topc(k1_tops_1(sK4,X0),sK4)
% 27.63/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ l1_pre_topc(sK4) ),
% 27.63/4.00      inference(unflattening,[status(thm)],[c_771]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_776,plain,
% 27.63/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | v3_pre_topc(k1_tops_1(sK4,X0),sK4) ),
% 27.63/4.00      inference(global_propositional_subsumption,
% 27.63/4.00                [status(thm)],
% 27.63/4.00                [c_772,c_35]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_777,plain,
% 27.63/4.00      ( v3_pre_topc(k1_tops_1(sK4,X0),sK4)
% 27.63/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 27.63/4.00      inference(renaming,[status(thm)],[c_776]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_6375,plain,
% 27.63/4.00      ( v3_pre_topc(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK4)
% 27.63/4.00      | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_777]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_6066,plain,
% 27.63/4.00      ( ~ r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),sK6)
% 27.63/4.00      | r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_0]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_2,plain,
% 27.63/4.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 27.63/4.00      inference(cnf_transformation,[],[f68]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_31,negated_conjecture,
% 27.63/4.00      ( r2_waybel_7(sK4,sK6,sK5) | r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
% 27.63/4.00      inference(cnf_transformation,[],[f105]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_4204,plain,
% 27.63/4.00      ( r2_waybel_7(sK4,sK6,sK5)
% 27.63/4.00      | ~ r2_hidden(X0,k1_yellow19(sK4,sK5))
% 27.63/4.00      | r2_hidden(X0,sK6) ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_2,c_31]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_17,plain,
% 27.63/4.00      ( m1_connsp_2(X0,X1,X2)
% 27.63/4.00      | ~ v3_pre_topc(X0,X1)
% 27.63/4.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.63/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.63/4.00      | ~ r2_hidden(X2,X0)
% 27.63/4.00      | v2_struct_0(X1)
% 27.63/4.00      | ~ v2_pre_topc(X1)
% 27.63/4.00      | ~ l1_pre_topc(X1) ),
% 27.63/4.00      inference(cnf_transformation,[],[f85]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_37,negated_conjecture,
% 27.63/4.00      ( ~ v2_struct_0(sK4) ),
% 27.63/4.00      inference(cnf_transformation,[],[f99]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_576,plain,
% 27.63/4.00      ( m1_connsp_2(X0,X1,X2)
% 27.63/4.00      | ~ v3_pre_topc(X0,X1)
% 27.63/4.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.63/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.63/4.00      | ~ r2_hidden(X2,X0)
% 27.63/4.00      | ~ v2_pre_topc(X1)
% 27.63/4.00      | ~ l1_pre_topc(X1)
% 27.63/4.00      | sK4 != X1 ),
% 27.63/4.00      inference(resolution_lifted,[status(thm)],[c_17,c_37]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_577,plain,
% 27.63/4.00      ( m1_connsp_2(X0,sK4,X1)
% 27.63/4.00      | ~ v3_pre_topc(X0,sK4)
% 27.63/4.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 27.63/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ r2_hidden(X1,X0)
% 27.63/4.00      | ~ v2_pre_topc(sK4)
% 27.63/4.00      | ~ l1_pre_topc(sK4) ),
% 27.63/4.00      inference(unflattening,[status(thm)],[c_576]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_581,plain,
% 27.63/4.00      ( m1_connsp_2(X0,sK4,X1)
% 27.63/4.00      | ~ v3_pre_topc(X0,sK4)
% 27.63/4.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 27.63/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ r2_hidden(X1,X0) ),
% 27.63/4.00      inference(global_propositional_subsumption,
% 27.63/4.00                [status(thm)],
% 27.63/4.00                [c_577,c_36,c_35]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_8,plain,
% 27.63/4.00      ( m1_subset_1(X0,X1)
% 27.63/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 27.63/4.00      | ~ r2_hidden(X0,X2) ),
% 27.63/4.00      inference(cnf_transformation,[],[f76]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_597,plain,
% 27.63/4.00      ( m1_connsp_2(X0,sK4,X1)
% 27.63/4.00      | ~ v3_pre_topc(X0,sK4)
% 27.63/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ r2_hidden(X1,X0) ),
% 27.63/4.00      inference(forward_subsumption_resolution,[status(thm)],[c_581,c_8]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_28,plain,
% 27.63/4.00      ( ~ m1_connsp_2(X0,X1,X2)
% 27.63/4.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.63/4.00      | r2_hidden(X0,k1_yellow19(X1,X2))
% 27.63/4.00      | v2_struct_0(X1)
% 27.63/4.00      | ~ v2_pre_topc(X1)
% 27.63/4.00      | ~ l1_pre_topc(X1) ),
% 27.63/4.00      inference(cnf_transformation,[],[f98]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_555,plain,
% 27.63/4.00      ( ~ m1_connsp_2(X0,X1,X2)
% 27.63/4.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.63/4.00      | r2_hidden(X0,k1_yellow19(X1,X2))
% 27.63/4.00      | ~ v2_pre_topc(X1)
% 27.63/4.00      | ~ l1_pre_topc(X1)
% 27.63/4.00      | sK4 != X1 ),
% 27.63/4.00      inference(resolution_lifted,[status(thm)],[c_28,c_37]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_556,plain,
% 27.63/4.00      ( ~ m1_connsp_2(X0,sK4,X1)
% 27.63/4.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 27.63/4.00      | r2_hidden(X0,k1_yellow19(sK4,X1))
% 27.63/4.00      | ~ v2_pre_topc(sK4)
% 27.63/4.00      | ~ l1_pre_topc(sK4) ),
% 27.63/4.00      inference(unflattening,[status(thm)],[c_555]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_560,plain,
% 27.63/4.00      ( ~ m1_connsp_2(X0,sK4,X1)
% 27.63/4.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 27.63/4.00      | r2_hidden(X0,k1_yellow19(sK4,X1)) ),
% 27.63/4.00      inference(global_propositional_subsumption,
% 27.63/4.00                [status(thm)],
% 27.63/4.00                [c_556,c_36,c_35]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_1272,plain,
% 27.63/4.00      ( ~ v3_pre_topc(X0,sK4)
% 27.63/4.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 27.63/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ r2_hidden(X1,X0)
% 27.63/4.00      | r2_hidden(X0,k1_yellow19(sK4,X1)) ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_597,c_560]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_1286,plain,
% 27.63/4.00      ( ~ v3_pre_topc(X0,sK4)
% 27.63/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ r2_hidden(X1,X0)
% 27.63/4.00      | r2_hidden(X0,k1_yellow19(sK4,X1)) ),
% 27.63/4.00      inference(forward_subsumption_resolution,
% 27.63/4.00                [status(thm)],
% 27.63/4.00                [c_1272,c_8]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_21,plain,
% 27.63/4.00      ( r2_waybel_7(X0,X1,X2)
% 27.63/4.00      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 27.63/4.00      | ~ v2_pre_topc(X0)
% 27.63/4.00      | ~ l1_pre_topc(X0) ),
% 27.63/4.00      inference(cnf_transformation,[],[f88]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_699,plain,
% 27.63/4.00      ( r2_waybel_7(X0,X1,X2)
% 27.63/4.00      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 27.63/4.00      | ~ l1_pre_topc(X0)
% 27.63/4.00      | sK4 != X0 ),
% 27.63/4.00      inference(resolution_lifted,[status(thm)],[c_21,c_36]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_700,plain,
% 27.63/4.00      ( r2_waybel_7(sK4,X0,X1)
% 27.63/4.00      | m1_subset_1(sK1(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ l1_pre_topc(sK4) ),
% 27.63/4.00      inference(unflattening,[status(thm)],[c_699]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_704,plain,
% 27.63/4.00      ( m1_subset_1(sK1(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | r2_waybel_7(sK4,X0,X1) ),
% 27.63/4.00      inference(global_propositional_subsumption,
% 27.63/4.00                [status(thm)],
% 27.63/4.00                [c_700,c_35]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_705,plain,
% 27.63/4.00      ( r2_waybel_7(sK4,X0,X1)
% 27.63/4.00      | m1_subset_1(sK1(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 27.63/4.00      inference(renaming,[status(thm)],[c_704]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_3768,plain,
% 27.63/4.00      ( r2_waybel_7(sK4,X0,X1)
% 27.63/4.00      | ~ v3_pre_topc(sK1(sK4,X0,X1),sK4)
% 27.63/4.00      | ~ r2_hidden(X2,sK1(sK4,X0,X1))
% 27.63/4.00      | r2_hidden(sK1(sK4,X0,X1),k1_yellow19(sK4,X2)) ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_1286,c_705]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_20,plain,
% 27.63/4.00      ( r2_waybel_7(X0,X1,X2)
% 27.63/4.00      | v3_pre_topc(sK1(X0,X1,X2),X0)
% 27.63/4.00      | ~ v2_pre_topc(X0)
% 27.63/4.00      | ~ l1_pre_topc(X0) ),
% 27.63/4.00      inference(cnf_transformation,[],[f89]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_717,plain,
% 27.63/4.00      ( r2_waybel_7(X0,X1,X2)
% 27.63/4.00      | v3_pre_topc(sK1(X0,X1,X2),X0)
% 27.63/4.00      | ~ l1_pre_topc(X0)
% 27.63/4.00      | sK4 != X0 ),
% 27.63/4.00      inference(resolution_lifted,[status(thm)],[c_20,c_36]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_718,plain,
% 27.63/4.00      ( r2_waybel_7(sK4,X0,X1)
% 27.63/4.00      | v3_pre_topc(sK1(sK4,X0,X1),sK4)
% 27.63/4.00      | ~ l1_pre_topc(sK4) ),
% 27.63/4.00      inference(unflattening,[status(thm)],[c_717]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_722,plain,
% 27.63/4.00      ( v3_pre_topc(sK1(sK4,X0,X1),sK4) | r2_waybel_7(sK4,X0,X1) ),
% 27.63/4.00      inference(global_propositional_subsumption,
% 27.63/4.00                [status(thm)],
% 27.63/4.00                [c_718,c_35]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_723,plain,
% 27.63/4.00      ( r2_waybel_7(sK4,X0,X1) | v3_pre_topc(sK1(sK4,X0,X1),sK4) ),
% 27.63/4.00      inference(renaming,[status(thm)],[c_722]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_1389,plain,
% 27.63/4.00      ( r2_waybel_7(sK4,X0,X1)
% 27.63/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ r2_hidden(X3,X2)
% 27.63/4.00      | r2_hidden(X2,k1_yellow19(sK4,X3))
% 27.63/4.00      | sK1(sK4,X0,X1) != X2
% 27.63/4.00      | sK4 != sK4 ),
% 27.63/4.00      inference(resolution_lifted,[status(thm)],[c_1286,c_723]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_1390,plain,
% 27.63/4.00      ( r2_waybel_7(sK4,X0,X1)
% 27.63/4.00      | ~ m1_subset_1(sK1(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ r2_hidden(X2,sK1(sK4,X0,X1))
% 27.63/4.00      | r2_hidden(sK1(sK4,X0,X1),k1_yellow19(sK4,X2)) ),
% 27.63/4.00      inference(unflattening,[status(thm)],[c_1389]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_1394,plain,
% 27.63/4.00      ( r2_waybel_7(sK4,X0,X1)
% 27.63/4.00      | ~ r2_hidden(X2,sK1(sK4,X0,X1))
% 27.63/4.00      | r2_hidden(sK1(sK4,X0,X1),k1_yellow19(sK4,X2)) ),
% 27.63/4.00      inference(global_propositional_subsumption,
% 27.63/4.00                [status(thm)],
% 27.63/4.00                [c_1390,c_35,c_700]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_3773,plain,
% 27.63/4.00      ( r2_waybel_7(sK4,X0,X1)
% 27.63/4.00      | ~ r2_hidden(X2,sK1(sK4,X0,X1))
% 27.63/4.00      | r2_hidden(sK1(sK4,X0,X1),k1_yellow19(sK4,X2)) ),
% 27.63/4.00      inference(global_propositional_subsumption,
% 27.63/4.00                [status(thm)],
% 27.63/4.00                [c_3768,c_35,c_700,c_1390]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_4426,plain,
% 27.63/4.00      ( r2_waybel_7(sK4,X0,X1)
% 27.63/4.00      | r2_waybel_7(sK4,sK6,sK5)
% 27.63/4.00      | r2_hidden(sK1(sK4,X0,X1),sK6)
% 27.63/4.00      | ~ r2_hidden(sK5,sK1(sK4,X0,X1)) ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_4204,c_3773]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_18,plain,
% 27.63/4.00      ( r2_waybel_7(X0,X1,X2)
% 27.63/4.00      | ~ r2_hidden(sK1(X0,X1,X2),X1)
% 27.63/4.00      | ~ v2_pre_topc(X0)
% 27.63/4.00      | ~ l1_pre_topc(X0) ),
% 27.63/4.00      inference(cnf_transformation,[],[f91]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_753,plain,
% 27.63/4.00      ( r2_waybel_7(X0,X1,X2)
% 27.63/4.00      | ~ r2_hidden(sK1(X0,X1,X2),X1)
% 27.63/4.00      | ~ l1_pre_topc(X0)
% 27.63/4.00      | sK4 != X0 ),
% 27.63/4.00      inference(resolution_lifted,[status(thm)],[c_18,c_36]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_754,plain,
% 27.63/4.00      ( r2_waybel_7(sK4,X0,X1)
% 27.63/4.00      | ~ r2_hidden(sK1(sK4,X0,X1),X0)
% 27.63/4.00      | ~ l1_pre_topc(sK4) ),
% 27.63/4.00      inference(unflattening,[status(thm)],[c_753]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_758,plain,
% 27.63/4.00      ( ~ r2_hidden(sK1(sK4,X0,X1),X0) | r2_waybel_7(sK4,X0,X1) ),
% 27.63/4.00      inference(global_propositional_subsumption,
% 27.63/4.00                [status(thm)],
% 27.63/4.00                [c_754,c_35]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_759,plain,
% 27.63/4.00      ( r2_waybel_7(sK4,X0,X1) | ~ r2_hidden(sK1(sK4,X0,X1),X0) ),
% 27.63/4.00      inference(renaming,[status(thm)],[c_758]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_4814,plain,
% 27.63/4.00      ( r2_waybel_7(sK4,sK6,X0)
% 27.63/4.00      | r2_waybel_7(sK4,sK6,sK5)
% 27.63/4.00      | ~ r2_hidden(sK5,sK1(sK4,sK6,X0)) ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_4426,c_759]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_19,plain,
% 27.63/4.00      ( r2_waybel_7(X0,X1,X2)
% 27.63/4.00      | r2_hidden(X2,sK1(X0,X1,X2))
% 27.63/4.00      | ~ v2_pre_topc(X0)
% 27.63/4.00      | ~ l1_pre_topc(X0) ),
% 27.63/4.00      inference(cnf_transformation,[],[f90]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_735,plain,
% 27.63/4.00      ( r2_waybel_7(X0,X1,X2)
% 27.63/4.00      | r2_hidden(X2,sK1(X0,X1,X2))
% 27.63/4.00      | ~ l1_pre_topc(X0)
% 27.63/4.00      | sK4 != X0 ),
% 27.63/4.00      inference(resolution_lifted,[status(thm)],[c_19,c_36]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_736,plain,
% 27.63/4.00      ( r2_waybel_7(sK4,X0,X1)
% 27.63/4.00      | r2_hidden(X1,sK1(sK4,X0,X1))
% 27.63/4.00      | ~ l1_pre_topc(sK4) ),
% 27.63/4.00      inference(unflattening,[status(thm)],[c_735]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_740,plain,
% 27.63/4.00      ( r2_hidden(X1,sK1(sK4,X0,X1)) | r2_waybel_7(sK4,X0,X1) ),
% 27.63/4.00      inference(global_propositional_subsumption,
% 27.63/4.00                [status(thm)],
% 27.63/4.00                [c_736,c_35]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_741,plain,
% 27.63/4.00      ( r2_waybel_7(sK4,X0,X1) | r2_hidden(X1,sK1(sK4,X0,X1)) ),
% 27.63/4.00      inference(renaming,[status(thm)],[c_740]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_4826,plain,
% 27.63/4.00      ( r2_waybel_7(sK4,sK6,sK5) ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_4814,c_741]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_3054,plain,
% 27.63/4.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 27.63/4.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_3167,plain,
% 27.63/4.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 27.63/4.00      inference(superposition,[status(thm)],[c_4,c_3054]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_3033,plain,
% 27.63/4.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 27.63/4.00      | r1_tarski(k1_tops_1(sK4,X0),X0) = iProver_top ),
% 27.63/4.00      inference(predicate_to_equality,[status(thm)],[c_834]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_4705,plain,
% 27.63/4.00      ( r1_tarski(k1_tops_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top ),
% 27.63/4.00      inference(superposition,[status(thm)],[c_3167,c_3033]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_4709,plain,
% 27.63/4.00      ( r1_tarski(k1_tops_1(sK4,u1_struct_0(sK4)),u1_struct_0(sK4)) ),
% 27.63/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_4705]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_29,plain,
% 27.63/4.00      ( m1_connsp_2(X0,X1,X2)
% 27.63/4.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.63/4.00      | ~ r2_hidden(X0,k1_yellow19(X1,X2))
% 27.63/4.00      | v2_struct_0(X1)
% 27.63/4.00      | ~ v2_pre_topc(X1)
% 27.63/4.00      | ~ l1_pre_topc(X1) ),
% 27.63/4.00      inference(cnf_transformation,[],[f97]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_534,plain,
% 27.63/4.00      ( m1_connsp_2(X0,X1,X2)
% 27.63/4.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.63/4.00      | ~ r2_hidden(X0,k1_yellow19(X1,X2))
% 27.63/4.00      | ~ v2_pre_topc(X1)
% 27.63/4.00      | ~ l1_pre_topc(X1)
% 27.63/4.00      | sK4 != X1 ),
% 27.63/4.00      inference(resolution_lifted,[status(thm)],[c_29,c_37]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_535,plain,
% 27.63/4.00      ( m1_connsp_2(X0,sK4,X1)
% 27.63/4.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 27.63/4.00      | ~ r2_hidden(X0,k1_yellow19(sK4,X1))
% 27.63/4.00      | ~ v2_pre_topc(sK4)
% 27.63/4.00      | ~ l1_pre_topc(sK4) ),
% 27.63/4.00      inference(unflattening,[status(thm)],[c_534]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_539,plain,
% 27.63/4.00      ( m1_connsp_2(X0,sK4,X1)
% 27.63/4.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 27.63/4.00      | ~ r2_hidden(X0,k1_yellow19(sK4,X1)) ),
% 27.63/4.00      inference(global_propositional_subsumption,
% 27.63/4.00                [status(thm)],
% 27.63/4.00                [c_535,c_36,c_35]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_15,plain,
% 27.63/4.00      ( ~ m1_connsp_2(X0,X1,X2)
% 27.63/4.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.63/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.63/4.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 27.63/4.00      | v2_struct_0(X1)
% 27.63/4.00      | ~ v2_pre_topc(X1)
% 27.63/4.00      | ~ l1_pre_topc(X1) ),
% 27.63/4.00      inference(cnf_transformation,[],[f82]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_16,plain,
% 27.63/4.00      ( ~ m1_connsp_2(X0,X1,X2)
% 27.63/4.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.63/4.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.63/4.00      | v2_struct_0(X1)
% 27.63/4.00      | ~ v2_pre_topc(X1)
% 27.63/4.00      | ~ l1_pre_topc(X1) ),
% 27.63/4.00      inference(cnf_transformation,[],[f84]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_223,plain,
% 27.63/4.00      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.63/4.00      | ~ m1_connsp_2(X0,X1,X2)
% 27.63/4.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 27.63/4.00      | v2_struct_0(X1)
% 27.63/4.00      | ~ v2_pre_topc(X1)
% 27.63/4.00      | ~ l1_pre_topc(X1) ),
% 27.63/4.00      inference(global_propositional_subsumption,
% 27.63/4.00                [status(thm)],
% 27.63/4.00                [c_15,c_16]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_224,plain,
% 27.63/4.00      ( ~ m1_connsp_2(X0,X1,X2)
% 27.63/4.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.63/4.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 27.63/4.00      | v2_struct_0(X1)
% 27.63/4.00      | ~ v2_pre_topc(X1)
% 27.63/4.00      | ~ l1_pre_topc(X1) ),
% 27.63/4.00      inference(renaming,[status(thm)],[c_223]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_513,plain,
% 27.63/4.00      ( ~ m1_connsp_2(X0,X1,X2)
% 27.63/4.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.63/4.00      | r2_hidden(X2,k1_tops_1(X1,X0))
% 27.63/4.00      | ~ v2_pre_topc(X1)
% 27.63/4.00      | ~ l1_pre_topc(X1)
% 27.63/4.00      | sK4 != X1 ),
% 27.63/4.00      inference(resolution_lifted,[status(thm)],[c_224,c_37]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_514,plain,
% 27.63/4.00      ( ~ m1_connsp_2(X0,sK4,X1)
% 27.63/4.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 27.63/4.00      | r2_hidden(X1,k1_tops_1(sK4,X0))
% 27.63/4.00      | ~ v2_pre_topc(sK4)
% 27.63/4.00      | ~ l1_pre_topc(sK4) ),
% 27.63/4.00      inference(unflattening,[status(thm)],[c_513]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_518,plain,
% 27.63/4.00      ( ~ m1_connsp_2(X0,sK4,X1)
% 27.63/4.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 27.63/4.00      | r2_hidden(X1,k1_tops_1(sK4,X0)) ),
% 27.63/4.00      inference(global_propositional_subsumption,
% 27.63/4.00                [status(thm)],
% 27.63/4.00                [c_514,c_36,c_35]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_1331,plain,
% 27.63/4.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.63/4.00      | ~ r2_hidden(X1,k1_yellow19(sK4,X0))
% 27.63/4.00      | r2_hidden(X0,k1_tops_1(sK4,X1)) ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_539,c_518]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_4461,plain,
% 27.63/4.00      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 27.63/4.00      | ~ r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),k1_yellow19(sK4,sK5))
% 27.63/4.00      | r2_hidden(sK5,k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6))) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_1331]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_605,plain,
% 27.63/4.00      ( ~ m1_connsp_2(X0,X1,X2)
% 27.63/4.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.63/4.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.63/4.00      | ~ v2_pre_topc(X1)
% 27.63/4.00      | ~ l1_pre_topc(X1)
% 27.63/4.00      | sK4 != X1 ),
% 27.63/4.00      inference(resolution_lifted,[status(thm)],[c_16,c_37]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_606,plain,
% 27.63/4.00      ( ~ m1_connsp_2(X0,sK4,X1)
% 27.63/4.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 27.63/4.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ v2_pre_topc(sK4)
% 27.63/4.00      | ~ l1_pre_topc(sK4) ),
% 27.63/4.00      inference(unflattening,[status(thm)],[c_605]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_610,plain,
% 27.63/4.00      ( ~ m1_connsp_2(X0,sK4,X1)
% 27.63/4.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 27.63/4.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 27.63/4.00      inference(global_propositional_subsumption,
% 27.63/4.00                [status(thm)],
% 27.63/4.00                [c_606,c_36,c_35]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_1316,plain,
% 27.63/4.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 27.63/4.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ r2_hidden(X1,k1_yellow19(sK4,X0)) ),
% 27.63/4.00      inference(resolution,[status(thm)],[c_539,c_610]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_4462,plain,
% 27.63/4.00      ( m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 27.63/4.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 27.63/4.00      | ~ r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),k1_yellow19(sK4,sK5)) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_1316]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_3218,plain,
% 27.63/4.00      ( r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),k1_yellow19(sK4,sK5))
% 27.63/4.00      | r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_1]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_2255,plain,
% 27.63/4.00      ( sK4 = sK4 ),
% 27.63/4.00      inference(instantiation,[status(thm)],[c_2224]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_30,negated_conjecture,
% 27.63/4.00      ( ~ r2_waybel_7(sK4,sK6,sK5)
% 27.63/4.00      | ~ r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
% 27.63/4.00      inference(cnf_transformation,[],[f106]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_32,negated_conjecture,
% 27.63/4.00      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) ),
% 27.63/4.00      inference(cnf_transformation,[],[f112]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_33,negated_conjecture,
% 27.63/4.00      ( v13_waybel_0(sK6,k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
% 27.63/4.00      inference(cnf_transformation,[],[f113]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(c_34,negated_conjecture,
% 27.63/4.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 27.63/4.00      inference(cnf_transformation,[],[f102]) ).
% 27.63/4.00  
% 27.63/4.00  cnf(contradiction,plain,
% 27.63/4.00      ( $false ),
% 27.63/4.00      inference(minisat,
% 27.63/4.00                [status(thm)],
% 27.63/4.00                [c_113726,c_57627,c_29534,c_27231,c_23654,c_12880,
% 27.63/4.00                 c_12570,c_11022,c_7762,c_7195,c_6989,c_6375,c_6066,
% 27.63/4.00                 c_4826,c_4709,c_4461,c_4462,c_3218,c_2255,c_30,c_32,
% 27.63/4.00                 c_33,c_34]) ).
% 27.63/4.00  
% 27.63/4.00  
% 27.63/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.63/4.00  
% 27.63/4.00  ------                               Statistics
% 27.63/4.00  
% 27.63/4.00  ------ Selected
% 27.63/4.00  
% 27.63/4.00  total_time:                             3.157
% 27.63/4.00  
%------------------------------------------------------------------------------
