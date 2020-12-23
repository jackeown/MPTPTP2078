%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2045+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:04 EST 2020

% Result     : Theorem 7.52s
% Output     : CNFRefutation 7.52s
% Verified   : 
% Statistics : Number of formulae       :  239 ( 980 expanded)
%              Number of clauses        :  153 ( 239 expanded)
%              Number of leaves         :   20 ( 251 expanded)
%              Depth                    :   21
%              Number of atoms          :  984 (7363 expanded)
%              Number of equality atoms :   94 ( 114 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
     => ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) )
           => r2_hidden(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(flattening,[],[f29])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f49,plain,(
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

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f48,f49])).

fof(f74,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f57,plain,(
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

fof(f56,plain,(
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

fof(f55,plain,
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

fof(f58,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f54,f57,f56,f55])).

fof(f86,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f87,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f91,plain,
    ( r1_tarski(k1_yellow19(sK4,sK5),sK6)
    | r2_waybel_7(sK4,sK6,sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f58])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | v3_pre_topc(sK1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f58])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | r2_hidden(X2,sK1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) ),
    inference(cnf_transformation,[],[f58])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,(
    v13_waybel_0(sK6,k3_yellow_1(k2_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f58])).

fof(f92,plain,
    ( ~ r1_tarski(k1_yellow19(sK4,sK5),sK6)
    | ~ r2_waybel_7(sK4,sK6,sK5) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_19,plain,
    ( ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2211,plain,
    ( ~ v13_waybel_0(X0_52,k3_yellow_1(X1_52))
    | ~ r1_tarski(X2_52,X1_52)
    | ~ r1_tarski(X3_52,X2_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1_52))))
    | ~ r2_hidden(X3_52,X0_52)
    | r2_hidden(X2_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_5458,plain,
    ( ~ v13_waybel_0(sK6,k3_yellow_1(X0_52))
    | ~ r1_tarski(X1_52,sK0(k1_yellow19(sK4,sK5),sK6))
    | ~ r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),X0_52)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0_52))))
    | ~ r2_hidden(X1_52,sK6)
    | r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_2211])).

cnf(c_7046,plain,
    ( ~ v13_waybel_0(sK6,k3_yellow_1(X0_52))
    | ~ r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),X0_52)
    | ~ r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK0(k1_yellow19(sK4,sK5),sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0_52))))
    | r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),sK6)
    | ~ r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK6) ),
    inference(instantiation,[status(thm)],[c_5458])).

cnf(c_26180,plain,
    ( ~ v13_waybel_0(sK6,k3_yellow_1(u1_struct_0(sK4)))
    | ~ r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),u1_struct_0(sK4))
    | ~ r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK0(k1_yellow19(sK4,sK5),sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK4)))))
    | r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),sK6)
    | ~ r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK6) ),
    inference(instantiation,[status(thm)],[c_7046])).

cnf(c_14,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_632,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_32])).

cnf(c_633,plain,
    ( v3_pre_topc(k1_tops_1(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_637,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v3_pre_topc(k1_tops_1(sK4,X0),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_633,c_31])).

cnf(c_638,plain,
    ( v3_pre_topc(k1_tops_1(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_637])).

cnf(c_2203,plain,
    ( v3_pre_topc(k1_tops_1(sK4,X0_52),sK4)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_638])).

cnf(c_10475,plain,
    ( v3_pre_topc(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK4)
    | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_2203])).

cnf(c_27,negated_conjecture,
    ( r2_waybel_7(sK4,sK6,sK5)
    | r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2207,negated_conjecture,
    ( r2_waybel_7(sK4,sK6,sK5)
    | r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_2982,plain,
    ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
    | r1_tarski(k1_yellow19(sK4,sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2207])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2217,plain,
    ( r1_tarski(X0_52,X1_52)
    | r2_hidden(sK0(X0_52,X1_52),X0_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2972,plain,
    ( r1_tarski(X0_52,X1_52) = iProver_top
    | r2_hidden(sK0(X0_52,X1_52),X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2217])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2216,plain,
    ( ~ r1_tarski(X0_52,X1_52)
    | ~ r2_hidden(X2_52,X0_52)
    | r2_hidden(X2_52,X1_52) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2973,plain,
    ( r1_tarski(X0_52,X1_52) != iProver_top
    | r2_hidden(X2_52,X0_52) != iProver_top
    | r2_hidden(X2_52,X1_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2216])).

cnf(c_3418,plain,
    ( r1_tarski(X0_52,X1_52) != iProver_top
    | r1_tarski(X0_52,X2_52) = iProver_top
    | r2_hidden(sK0(X0_52,X2_52),X1_52) = iProver_top ),
    inference(superposition,[status(thm)],[c_2972,c_2973])).

cnf(c_4434,plain,
    ( r1_tarski(X0_52,X1_52) != iProver_top
    | r1_tarski(X1_52,X2_52) != iProver_top
    | r1_tarski(X0_52,X3_52) = iProver_top
    | r2_hidden(sK0(X0_52,X3_52),X2_52) = iProver_top ),
    inference(superposition,[status(thm)],[c_3418,c_2973])).

cnf(c_6211,plain,
    ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
    | r1_tarski(k1_yellow19(sK4,sK5),X0_52) = iProver_top
    | r1_tarski(sK6,X1_52) != iProver_top
    | r2_hidden(sK0(k1_yellow19(sK4,sK5),X0_52),X1_52) = iProver_top ),
    inference(superposition,[status(thm)],[c_2982,c_4434])).

cnf(c_9,plain,
    ( r2_waybel_7(X0,X1,X2)
    | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_673,plain,
    ( r2_waybel_7(X0,X1,X2)
    | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_32])).

cnf(c_674,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | m1_subset_1(sK1(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_673])).

cnf(c_678,plain,
    ( m1_subset_1(sK1(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_waybel_7(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_674,c_31])).

cnf(c_679,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | m1_subset_1(sK1(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_678])).

cnf(c_2201,plain,
    ( r2_waybel_7(sK4,X0_52,X1_52)
    | m1_subset_1(sK1(sK4,X0_52,X1_52),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_679])).

cnf(c_2988,plain,
    ( r2_waybel_7(sK4,X0_52,X1_52) = iProver_top
    | m1_subset_1(sK1(sK4,X0_52,X1_52),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2201])).

cnf(c_25,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_491,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_492,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_496,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_492,c_32,c_31])).

cnf(c_22,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X0,k1_yellow19(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_539,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X0,k1_yellow19(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_540,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X0,k1_yellow19(sK4,X1))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_539])).

cnf(c_544,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X0,k1_yellow19(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_540,c_32,c_31])).

cnf(c_1260,plain,
    ( ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,k1_yellow19(sK4,X1)) ),
    inference(resolution,[status(thm)],[c_496,c_544])).

cnf(c_2191,plain,
    ( ~ v3_pre_topc(X0_52,sK4)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK4))
    | ~ r2_hidden(X1_52,X0_52)
    | r2_hidden(X0_52,k1_yellow19(sK4,X1_52)) ),
    inference(subtyping,[status(esa)],[c_1260])).

cnf(c_2997,plain,
    ( v3_pre_topc(X0_52,sK4) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1_52,X0_52) != iProver_top
    | r2_hidden(X0_52,k1_yellow19(sK4,X1_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2191])).

cnf(c_4290,plain,
    ( r2_waybel_7(sK4,X0_52,X1_52) = iProver_top
    | v3_pre_topc(sK1(sK4,X0_52,X1_52),sK4) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X2_52,sK1(sK4,X0_52,X1_52)) != iProver_top
    | r2_hidden(sK1(sK4,X0_52,X1_52),k1_yellow19(sK4,X2_52)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2988,c_2997])).

cnf(c_8,plain,
    ( r2_waybel_7(X0,X1,X2)
    | v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_691,plain,
    ( r2_waybel_7(X0,X1,X2)
    | v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_32])).

cnf(c_692,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | v3_pre_topc(sK1(sK4,X0,X1),sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_696,plain,
    ( v3_pre_topc(sK1(sK4,X0,X1),sK4)
    | r2_waybel_7(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_692,c_31])).

cnf(c_697,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | v3_pre_topc(sK1(sK4,X0,X1),sK4) ),
    inference(renaming,[status(thm)],[c_696])).

cnf(c_2200,plain,
    ( r2_waybel_7(sK4,X0_52,X1_52)
    | v3_pre_topc(sK1(sK4,X0_52,X1_52),sK4) ),
    inference(subtyping,[status(esa)],[c_697])).

cnf(c_2290,plain,
    ( r2_waybel_7(sK4,X0_52,X1_52) = iProver_top
    | v3_pre_topc(sK1(sK4,X0_52,X1_52),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2200])).

cnf(c_5657,plain,
    ( r2_waybel_7(sK4,X0_52,X1_52) = iProver_top
    | m1_subset_1(X2_52,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X2_52,sK1(sK4,X0_52,X1_52)) != iProver_top
    | r2_hidden(sK1(sK4,X0_52,X1_52),k1_yellow19(sK4,X2_52)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4290,c_2290])).

cnf(c_5670,plain,
    ( r2_waybel_7(sK4,X0_52,X1_52) = iProver_top
    | r1_tarski(k1_yellow19(sK4,X2_52),X3_52) != iProver_top
    | m1_subset_1(X2_52,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X2_52,sK1(sK4,X0_52,X1_52)) != iProver_top
    | r2_hidden(sK1(sK4,X0_52,X1_52),X3_52) = iProver_top ),
    inference(superposition,[status(thm)],[c_5657,c_2973])).

cnf(c_9840,plain,
    ( r2_waybel_7(sK4,X0_52,X1_52) = iProver_top
    | r2_waybel_7(sK4,sK6,sK5) = iProver_top
    | r1_tarski(k1_yellow19(sK4,sK0(k1_yellow19(sK4,sK5),X2_52)),X3_52) != iProver_top
    | r1_tarski(k1_yellow19(sK4,sK5),X2_52) = iProver_top
    | r1_tarski(sK6,sK1(sK4,X0_52,X1_52)) != iProver_top
    | m1_subset_1(sK0(k1_yellow19(sK4,sK5),X2_52),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK1(sK4,X0_52,X1_52),X3_52) = iProver_top ),
    inference(superposition,[status(thm)],[c_6211,c_5670])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_40,plain,
    ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
    | r1_tarski(k1_yellow19(sK4,sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3305,plain,
    ( r2_waybel_7(sK4,sK6,sK5)
    | v3_pre_topc(sK1(sK4,sK6,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_2200])).

cnf(c_3306,plain,
    ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
    | v3_pre_topc(sK1(sK4,sK6,sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3305])).

cnf(c_3304,plain,
    ( r2_waybel_7(sK4,sK6,sK5)
    | m1_subset_1(sK1(sK4,sK6,sK5),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_2201])).

cnf(c_3308,plain,
    ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
    | m1_subset_1(sK1(sK4,sK6,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3304])).

cnf(c_6,plain,
    ( r2_waybel_7(X0,X1,X2)
    | ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_727,plain,
    ( r2_waybel_7(X0,X1,X2)
    | ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_32])).

cnf(c_728,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | ~ r2_hidden(sK1(sK4,X0,X1),X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_727])).

cnf(c_732,plain,
    ( ~ r2_hidden(sK1(sK4,X0,X1),X0)
    | r2_waybel_7(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_728,c_31])).

cnf(c_733,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | ~ r2_hidden(sK1(sK4,X0,X1),X0) ),
    inference(renaming,[status(thm)],[c_732])).

cnf(c_2198,plain,
    ( r2_waybel_7(sK4,X0_52,X1_52)
    | ~ r2_hidden(sK1(sK4,X0_52,X1_52),X0_52) ),
    inference(subtyping,[status(esa)],[c_733])).

cnf(c_3303,plain,
    ( r2_waybel_7(sK4,sK6,sK5)
    | ~ r2_hidden(sK1(sK4,sK6,sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_2198])).

cnf(c_3310,plain,
    ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
    | r2_hidden(sK1(sK4,sK6,sK5),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3303])).

cnf(c_7,plain,
    ( r2_waybel_7(X0,X1,X2)
    | r2_hidden(X2,sK1(X0,X1,X2))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_709,plain,
    ( r2_waybel_7(X0,X1,X2)
    | r2_hidden(X2,sK1(X0,X1,X2))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_32])).

cnf(c_710,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | r2_hidden(X1,sK1(sK4,X0,X1))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_714,plain,
    ( r2_hidden(X1,sK1(sK4,X0,X1))
    | r2_waybel_7(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_710,c_31])).

cnf(c_715,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | r2_hidden(X1,sK1(sK4,X0,X1)) ),
    inference(renaming,[status(thm)],[c_714])).

cnf(c_2199,plain,
    ( r2_waybel_7(sK4,X0_52,X1_52)
    | r2_hidden(X1_52,sK1(sK4,X0_52,X1_52)) ),
    inference(subtyping,[status(esa)],[c_715])).

cnf(c_3302,plain,
    ( r2_waybel_7(sK4,sK6,sK5)
    | r2_hidden(sK5,sK1(sK4,sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_2199])).

cnf(c_3312,plain,
    ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
    | r2_hidden(sK5,sK1(sK4,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3302])).

cnf(c_4047,plain,
    ( ~ v3_pre_topc(sK1(sK4,sK6,sK5),sK4)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK4,sK6,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0_52,sK1(sK4,sK6,sK5))
    | r2_hidden(sK1(sK4,sK6,sK5),k1_yellow19(sK4,X0_52)) ),
    inference(instantiation,[status(thm)],[c_2191])).

cnf(c_4270,plain,
    ( ~ v3_pre_topc(sK1(sK4,sK6,sK5),sK4)
    | ~ m1_subset_1(sK1(sK4,sK6,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,sK6,sK5),k1_yellow19(sK4,sK5))
    | ~ r2_hidden(sK5,sK1(sK4,sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_4047])).

cnf(c_4271,plain,
    ( v3_pre_topc(sK1(sK4,sK6,sK5),sK4) != iProver_top
    | m1_subset_1(sK1(sK4,sK6,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK1(sK4,sK6,sK5),k1_yellow19(sK4,sK5)) = iProver_top
    | r2_hidden(sK5,sK1(sK4,sK6,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4270])).

cnf(c_5116,plain,
    ( ~ r1_tarski(X0_52,sK6)
    | ~ r2_hidden(sK1(sK4,sK6,sK5),X0_52)
    | r2_hidden(sK1(sK4,sK6,sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_2216])).

cnf(c_10154,plain,
    ( ~ r1_tarski(k1_yellow19(sK4,sK5),sK6)
    | ~ r2_hidden(sK1(sK4,sK6,sK5),k1_yellow19(sK4,sK5))
    | r2_hidden(sK1(sK4,sK6,sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_5116])).

cnf(c_10155,plain,
    ( r1_tarski(k1_yellow19(sK4,sK5),sK6) != iProver_top
    | r2_hidden(sK1(sK4,sK6,sK5),k1_yellow19(sK4,sK5)) != iProver_top
    | r2_hidden(sK1(sK4,sK6,sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10154])).

cnf(c_10200,plain,
    ( r2_waybel_7(sK4,sK6,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9840,c_37,c_40,c_3306,c_3308,c_3310,c_3312,c_4271,c_10155])).

cnf(c_10202,plain,
    ( r2_waybel_7(sK4,sK6,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10200])).

cnf(c_10,plain,
    ( ~ r2_waybel_7(X0,X1,X2)
    | ~ v3_pre_topc(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_650,plain,
    ( ~ r2_waybel_7(X0,X1,X2)
    | ~ v3_pre_topc(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_32])).

cnf(c_651,plain,
    ( ~ r2_waybel_7(sK4,X0,X1)
    | ~ v3_pre_topc(X2,sK4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X2,X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_653,plain,
    ( r2_hidden(X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_pre_topc(X2,sK4)
    | ~ r2_waybel_7(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_651,c_31])).

cnf(c_654,plain,
    ( ~ r2_waybel_7(sK4,X0,X1)
    | ~ v3_pre_topc(X2,sK4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X2,X0) ),
    inference(renaming,[status(thm)],[c_653])).

cnf(c_2202,plain,
    ( ~ r2_waybel_7(sK4,X0_52,X1_52)
    | ~ v3_pre_topc(X2_52,sK4)
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1_52,X2_52)
    | r2_hidden(X2_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_654])).

cnf(c_5882,plain,
    ( ~ r2_waybel_7(sK4,X0_52,X1_52)
    | ~ v3_pre_topc(k1_tops_1(X0_53,X2_52),sK4)
    | ~ m1_subset_1(k1_tops_1(X0_53,X2_52),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1_52,k1_tops_1(X0_53,X2_52))
    | r2_hidden(k1_tops_1(X0_53,X2_52),X0_52) ),
    inference(instantiation,[status(thm)],[c_2202])).

cnf(c_7312,plain,
    ( ~ r2_waybel_7(sK4,X0_52,sK5)
    | ~ v3_pre_topc(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK4)
    | ~ m1_subset_1(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),X0_52)
    | ~ r2_hidden(sK5,k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6))) ),
    inference(instantiation,[status(thm)],[c_5882])).

cnf(c_7314,plain,
    ( ~ r2_waybel_7(sK4,sK6,sK5)
    | ~ v3_pre_topc(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK4)
    | ~ m1_subset_1(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK6)
    | ~ r2_hidden(sK5,k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6))) ),
    inference(instantiation,[status(thm)],[c_7312])).

cnf(c_24,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_783,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_784,plain,
    ( r1_tarski(k1_tops_1(sK4,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_783])).

cnf(c_2195,plain,
    ( r1_tarski(k1_tops_1(sK4,X0_52),X0_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_784])).

cnf(c_7047,plain,
    ( r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK0(k1_yellow19(sK4,sK5),sK6))
    | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_2195])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_766,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_31])).

cnf(c_767,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k1_tops_1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_766])).

cnf(c_2197,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k1_tops_1(sK4,X0_52),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_767])).

cnf(c_6351,plain,
    ( ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_2197])).

cnf(c_21,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2209,plain,
    ( r1_tarski(X0_52,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_3388,plain,
    ( r1_tarski(X0_52,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_2209])).

cnf(c_6352,plain,
    ( r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_3388])).

cnf(c_23,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k1_yellow19(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_518,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k1_yellow19(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_519,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,k1_yellow19(sK4,X1))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_523,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,k1_yellow19(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_519,c_32,c_31])).

cnf(c_1,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_13,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_215,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1,c_13])).

cnf(c_470,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_215,c_33])).

cnf(c_471,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k1_tops_1(sK4,X0))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_475,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k1_tops_1(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_471,c_32,c_31])).

cnf(c_1245,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k1_yellow19(sK4,X0))
    | r2_hidden(X0,k1_tops_1(sK4,X1)) ),
    inference(resolution,[status(thm)],[c_523,c_475])).

cnf(c_2192,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK4))
    | ~ r2_hidden(X1_52,k1_yellow19(sK4,X0_52))
    | r2_hidden(X0_52,k1_tops_1(sK4,X1_52)) ),
    inference(subtyping,[status(esa)],[c_1245])).

cnf(c_3223,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(X0_52,k1_yellow19(sK4,sK5))
    | r2_hidden(sK5,k1_tops_1(sK4,X0_52)) ),
    inference(instantiation,[status(thm)],[c_2192])).

cnf(c_3487,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),k1_yellow19(sK4,sK5))
    | r2_hidden(sK5,k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6))) ),
    inference(instantiation,[status(thm)],[c_3223])).

cnf(c_560,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_33])).

cnf(c_561,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_565,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_561,c_32,c_31])).

cnf(c_1230,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,k1_yellow19(sK4,X1)) ),
    inference(resolution,[status(thm)],[c_523,c_565])).

cnf(c_2193,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK4))
    | ~ r2_hidden(X0_52,k1_yellow19(sK4,X1_52)) ),
    inference(subtyping,[status(esa)],[c_1230])).

cnf(c_3218,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(X0_52,k1_yellow19(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2193])).

cnf(c_3488,plain,
    ( m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),k1_yellow19(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3218])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2218,plain,
    ( r1_tarski(X0_52,X1_52)
    | ~ r2_hidden(sK0(X0_52,X1_52),X1_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3252,plain,
    ( r1_tarski(k1_yellow19(sK4,sK5),sK6)
    | ~ r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_2218])).

cnf(c_3249,plain,
    ( r1_tarski(k1_yellow19(sK4,sK5),sK6)
    | r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),k1_yellow19(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2217])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2206,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_2983,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2206])).

cnf(c_12,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_456,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_12,c_2])).

cnf(c_778,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_456,c_31])).

cnf(c_779,plain,
    ( k2_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_778])).

cnf(c_2196,plain,
    ( k2_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_779])).

cnf(c_3006,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK4))))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2983,c_2196])).

cnf(c_3168,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK4))))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3006])).

cnf(c_29,negated_conjecture,
    ( v13_waybel_0(sK6,k3_yellow_1(k2_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2205,negated_conjecture,
    ( v13_waybel_0(sK6,k3_yellow_1(k2_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_2984,plain,
    ( v13_waybel_0(sK6,k3_yellow_1(k2_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2205])).

cnf(c_3003,plain,
    ( v13_waybel_0(sK6,k3_yellow_1(u1_struct_0(sK4))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2984,c_2196])).

cnf(c_3156,plain,
    ( v13_waybel_0(sK6,k3_yellow_1(u1_struct_0(sK4))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3003])).

cnf(c_26,negated_conjecture,
    ( ~ r2_waybel_7(sK4,sK6,sK5)
    | ~ r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26180,c_10475,c_10202,c_7314,c_7047,c_6351,c_6352,c_3487,c_3488,c_3252,c_3249,c_3168,c_3156,c_26,c_30])).


%------------------------------------------------------------------------------
