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
% DateTime   : Thu Dec  3 12:29:02 EST 2020

% Result     : Theorem 11.63s
% Output     : CNFRefutation 11.63s
% Verified   : 
% Statistics : Number of formulae       :  257 ( 796 expanded)
%              Number of clauses        :  162 ( 206 expanded)
%              Number of leaves         :   28 ( 205 expanded)
%              Depth                    :   21
%              Number of atoms          : 1039 (5763 expanded)
%              Number of equality atoms :  103 ( 113 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
     => ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) )
           => r2_hidden(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(flattening,[],[f36])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f54,plain,(
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

fof(f55,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f53,f54])).

fof(f84,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f12,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f103,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) ) ),
    inference(definition_unfolding,[],[f84,f78,f78])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

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
    inference(nnf_transformation,[],[f41])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f61,plain,(
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

fof(f60,plain,(
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

fof(f59,plain,
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

fof(f62,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f58,f61,f60,f59])).

fof(f93,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f92,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
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

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f97,plain,
    ( r1_tarski(k1_yellow19(sK4,sK5),sK6)
    | r2_waybel_7(sK4,sK6,sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | v3_pre_topc(sK1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | r2_hidden(X2,sK1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f91,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
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

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f9,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f69,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f98,plain,
    ( ~ r1_tarski(k1_yellow19(sK4,sK5),sK6)
    | ~ r2_waybel_7(sK4,sK6,sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f96,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) ),
    inference(cnf_transformation,[],[f62])).

fof(f104,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) ),
    inference(definition_unfolding,[],[f96,f78])).

fof(f95,plain,(
    v13_waybel_0(sK6,k3_yellow_1(k2_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f62])).

fof(f105,plain,(
    v13_waybel_0(sK6,k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
    inference(definition_unfolding,[],[f95,f78])).

fof(f94,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_24,plain,
    ( ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X3,X0)
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2200,plain,
    ( ~ v13_waybel_0(X0_53,k3_lattice3(k1_lattice3(X1_53)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1_53)))))
    | ~ r2_hidden(X2_53,X0_53)
    | r2_hidden(X3_53,X0_53)
    | ~ r1_tarski(X3_53,X1_53)
    | ~ r1_tarski(X2_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_14966,plain,
    ( ~ v13_waybel_0(X0_53,k3_lattice3(k1_lattice3(X1_53)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1_53)))))
    | r2_hidden(X2_53,X0_53)
    | ~ r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),X0_53)
    | ~ r1_tarski(X2_53,X1_53)
    | ~ r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),X2_53) ),
    inference(instantiation,[status(thm)],[c_2200])).

cnf(c_50928,plain,
    ( ~ v13_waybel_0(sK6,k3_lattice3(k1_lattice3(k2_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))))
    | r2_hidden(X0_53,sK6)
    | ~ r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK6)
    | ~ r1_tarski(X0_53,k2_struct_0(sK4))
    | ~ r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),X0_53) ),
    inference(instantiation,[status(thm)],[c_14966])).

cnf(c_56428,plain,
    ( ~ v13_waybel_0(sK6,k3_lattice3(k1_lattice3(k2_struct_0(sK4))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))))
    | ~ r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK6)
    | r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),sK6)
    | ~ r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK0(k1_yellow19(sK4,sK5),sK6))
    | ~ r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_50928])).

cnf(c_2219,plain,
    ( ~ m1_subset_1(X0_53,X1_53)
    | m1_subset_1(X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_4066,plain,
    ( m1_subset_1(X0_53,X1_53)
    | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),X2_53)
    | X1_53 != X2_53
    | X0_53 != sK0(k1_yellow19(sK4,sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_2219])).

cnf(c_5221,plain,
    ( m1_subset_1(X0_53,X1_53)
    | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(X2_53))
    | X0_53 != sK0(k1_yellow19(sK4,sK5),sK6)
    | X1_53 != k1_zfmisc_1(X2_53) ),
    inference(instantiation,[status(thm)],[c_4066])).

cnf(c_9321,plain,
    ( m1_subset_1(X0_53,X1_53)
    | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | X0_53 != sK0(k1_yellow19(sK4,sK5),sK6)
    | X1_53 != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5221])).

cnf(c_12357,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | X0_53 != sK0(k1_yellow19(sK4,sK5),sK6)
    | k1_zfmisc_1(X1_53) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_9321])).

cnf(c_19959,plain,
    ( m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(X0_53))
    | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | sK0(k1_yellow19(sK4,sK5),sK6) != sK0(k1_yellow19(sK4,sK5),sK6)
    | k1_zfmisc_1(X0_53) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_12357])).

cnf(c_53444,plain,
    ( ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(k2_struct_0(sK4)))
    | sK0(k1_yellow19(sK4,sK5),sK6) != sK0(k1_yellow19(sK4,sK5),sK6)
    | k1_zfmisc_1(k2_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_19959])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2206,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | r1_tarski(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_13518,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK4)))
    | r1_tarski(X0_53,k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2206])).

cnf(c_31018,plain,
    ( ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(k2_struct_0(sK4)))
    | r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_13518])).

cnf(c_2218,plain,
    ( X0_53 != X1_53
    | k1_zfmisc_1(X0_53) = k1_zfmisc_1(X1_53) ),
    theory(equality)).

cnf(c_12358,plain,
    ( X0_53 != u1_struct_0(sK4)
    | k1_zfmisc_1(X0_53) = k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2218])).

cnf(c_17992,plain,
    ( k2_struct_0(sK4) != u1_struct_0(sK4)
    | k1_zfmisc_1(k2_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_12358])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_788,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_32])).

cnf(c_789,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k1_tops_1(sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_788])).

cnf(c_2187,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k1_tops_1(sK4,X0_53),X0_53) ),
    inference(subtyping,[status(esa)],[c_789])).

cnf(c_10975,plain,
    ( ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK0(k1_yellow19(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_2187])).

cnf(c_9,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_744,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_33])).

cnf(c_745,plain,
    ( v3_pre_topc(k1_tops_1(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_744])).

cnf(c_749,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v3_pre_topc(k1_tops_1(sK4,X0),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_745,c_32])).

cnf(c_750,plain,
    ( v3_pre_topc(k1_tops_1(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_749])).

cnf(c_2189,plain,
    ( v3_pre_topc(k1_tops_1(sK4,X0_53),sK4)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_750])).

cnf(c_10726,plain,
    ( v3_pre_topc(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK4)
    | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_2189])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_800,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_32])).

cnf(c_801,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k1_tops_1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_800])).

cnf(c_2186,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k1_tops_1(sK4,X0_53),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_801])).

cnf(c_10166,plain,
    ( m1_subset_1(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_2186])).

cnf(c_2212,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_8164,plain,
    ( sK0(k1_yellow19(sK4,sK5),sK6) = sK0(k1_yellow19(sK4,sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_2212])).

cnf(c_19,plain,
    ( ~ r2_waybel_7(X0,X1,X2)
    | ~ v3_pre_topc(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_649,plain,
    ( ~ r2_waybel_7(X0,X1,X2)
    | ~ v3_pre_topc(X3,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_33])).

cnf(c_650,plain,
    ( ~ r2_waybel_7(sK4,X0,X1)
    | ~ v3_pre_topc(X2,sK4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X2,X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_649])).

cnf(c_652,plain,
    ( r2_hidden(X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_pre_topc(X2,sK4)
    | ~ r2_waybel_7(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_650,c_32])).

cnf(c_653,plain,
    ( ~ r2_waybel_7(sK4,X0,X1)
    | ~ v3_pre_topc(X2,sK4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X2,X0) ),
    inference(renaming,[status(thm)],[c_652])).

cnf(c_2194,plain,
    ( ~ r2_waybel_7(sK4,X0_53,X1_53)
    | ~ v3_pre_topc(X2_53,sK4)
    | ~ m1_subset_1(X2_53,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1_53,X2_53)
    | r2_hidden(X2_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_653])).

cnf(c_3734,plain,
    ( ~ r2_waybel_7(sK4,X0_53,X1_53)
    | ~ v3_pre_topc(k1_tops_1(sK4,X2_53),sK4)
    | ~ m1_subset_1(k1_tops_1(sK4,X2_53),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1_53,k1_tops_1(sK4,X2_53))
    | r2_hidden(k1_tops_1(sK4,X2_53),X0_53) ),
    inference(instantiation,[status(thm)],[c_2194])).

cnf(c_4736,plain,
    ( ~ r2_waybel_7(sK4,X0_53,sK5)
    | ~ v3_pre_topc(k1_tops_1(sK4,X1_53),sK4)
    | ~ m1_subset_1(k1_tops_1(sK4,X1_53),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k1_tops_1(sK4,X1_53),X0_53)
    | ~ r2_hidden(sK5,k1_tops_1(sK4,X1_53)) ),
    inference(instantiation,[status(thm)],[c_3734])).

cnf(c_7740,plain,
    ( ~ r2_waybel_7(sK4,X0_53,sK5)
    | ~ v3_pre_topc(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK4)
    | ~ m1_subset_1(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),X0_53)
    | ~ r2_hidden(sK5,k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6))) ),
    inference(instantiation,[status(thm)],[c_4736])).

cnf(c_7742,plain,
    ( ~ r2_waybel_7(sK4,sK6,sK5)
    | ~ v3_pre_topc(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK4)
    | ~ m1_subset_1(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK6)
    | ~ r2_hidden(sK5,k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6))) ),
    inference(instantiation,[status(thm)],[c_7740])).

cnf(c_28,negated_conjecture,
    ( r2_waybel_7(sK4,sK6,sK5)
    | r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2198,negated_conjecture,
    ( r2_waybel_7(sK4,sK6,sK5)
    | r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_3009,plain,
    ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
    | r1_tarski(k1_yellow19(sK4,sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2198])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2209,plain,
    ( r2_hidden(sK0(X0_53,X1_53),X0_53)
    | r1_tarski(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2998,plain,
    ( r2_hidden(sK0(X0_53,X1_53),X0_53) = iProver_top
    | r1_tarski(X0_53,X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2209])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2208,plain,
    ( ~ r2_hidden(X0_53,X1_53)
    | r2_hidden(X0_53,X2_53)
    | ~ r1_tarski(X1_53,X2_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2999,plain,
    ( r2_hidden(X0_53,X1_53) != iProver_top
    | r2_hidden(X0_53,X2_53) = iProver_top
    | r1_tarski(X1_53,X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2208])).

cnf(c_3433,plain,
    ( r2_hidden(sK0(X0_53,X1_53),X2_53) = iProver_top
    | r1_tarski(X0_53,X2_53) != iProver_top
    | r1_tarski(X0_53,X1_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_2998,c_2999])).

cnf(c_5262,plain,
    ( r2_hidden(sK0(X0_53,X1_53),X2_53) = iProver_top
    | r1_tarski(X0_53,X3_53) != iProver_top
    | r1_tarski(X3_53,X2_53) != iProver_top
    | r1_tarski(X0_53,X1_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_3433,c_2999])).

cnf(c_7280,plain,
    ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
    | r2_hidden(sK0(k1_yellow19(sK4,sK5),X0_53),X1_53) = iProver_top
    | r1_tarski(k1_yellow19(sK4,sK5),X0_53) = iProver_top
    | r1_tarski(sK6,X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_3009,c_5262])).

cnf(c_41,plain,
    ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
    | r1_tarski(k1_yellow19(sK4,sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_17,plain,
    ( r2_waybel_7(X0,X1,X2)
    | v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_690,plain,
    ( r2_waybel_7(X0,X1,X2)
    | v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_691,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | v3_pre_topc(sK1(sK4,X0,X1),sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_690])).

cnf(c_695,plain,
    ( v3_pre_topc(sK1(sK4,X0,X1),sK4)
    | r2_waybel_7(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_691,c_32])).

cnf(c_696,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | v3_pre_topc(sK1(sK4,X0,X1),sK4) ),
    inference(renaming,[status(thm)],[c_695])).

cnf(c_2192,plain,
    ( r2_waybel_7(sK4,X0_53,X1_53)
    | v3_pre_topc(sK1(sK4,X0_53,X1_53),sK4) ),
    inference(subtyping,[status(esa)],[c_696])).

cnf(c_3373,plain,
    ( r2_waybel_7(sK4,sK6,sK5)
    | v3_pre_topc(sK1(sK4,sK6,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_2192])).

cnf(c_3374,plain,
    ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
    | v3_pre_topc(sK1(sK4,sK6,sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3373])).

cnf(c_18,plain,
    ( r2_waybel_7(X0,X1,X2)
    | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_672,plain,
    ( r2_waybel_7(X0,X1,X2)
    | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_33])).

cnf(c_673,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | m1_subset_1(sK1(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_677,plain,
    ( m1_subset_1(sK1(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_waybel_7(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_673,c_32])).

cnf(c_678,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | m1_subset_1(sK1(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_677])).

cnf(c_2193,plain,
    ( r2_waybel_7(sK4,X0_53,X1_53)
    | m1_subset_1(sK1(sK4,X0_53,X1_53),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_678])).

cnf(c_3372,plain,
    ( r2_waybel_7(sK4,sK6,sK5)
    | m1_subset_1(sK1(sK4,sK6,sK5),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_2193])).

cnf(c_3376,plain,
    ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
    | m1_subset_1(sK1(sK4,sK6,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3372])).

cnf(c_15,plain,
    ( r2_waybel_7(X0,X1,X2)
    | ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_726,plain,
    ( r2_waybel_7(X0,X1,X2)
    | ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_33])).

cnf(c_727,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | ~ r2_hidden(sK1(sK4,X0,X1),X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_731,plain,
    ( ~ r2_hidden(sK1(sK4,X0,X1),X0)
    | r2_waybel_7(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_727,c_32])).

cnf(c_732,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | ~ r2_hidden(sK1(sK4,X0,X1),X0) ),
    inference(renaming,[status(thm)],[c_731])).

cnf(c_2190,plain,
    ( r2_waybel_7(sK4,X0_53,X1_53)
    | ~ r2_hidden(sK1(sK4,X0_53,X1_53),X0_53) ),
    inference(subtyping,[status(esa)],[c_732])).

cnf(c_3371,plain,
    ( r2_waybel_7(sK4,sK6,sK5)
    | ~ r2_hidden(sK1(sK4,sK6,sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_2190])).

cnf(c_3378,plain,
    ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
    | r2_hidden(sK1(sK4,sK6,sK5),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3371])).

cnf(c_16,plain,
    ( r2_waybel_7(X0,X1,X2)
    | r2_hidden(X2,sK1(X0,X1,X2))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_708,plain,
    ( r2_waybel_7(X0,X1,X2)
    | r2_hidden(X2,sK1(X0,X1,X2))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_33])).

cnf(c_709,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | r2_hidden(X1,sK1(sK4,X0,X1))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_708])).

cnf(c_713,plain,
    ( r2_hidden(X1,sK1(sK4,X0,X1))
    | r2_waybel_7(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_709,c_32])).

cnf(c_714,plain,
    ( r2_waybel_7(sK4,X0,X1)
    | r2_hidden(X1,sK1(sK4,X0,X1)) ),
    inference(renaming,[status(thm)],[c_713])).

cnf(c_2191,plain,
    ( r2_waybel_7(sK4,X0_53,X1_53)
    | r2_hidden(X1_53,sK1(sK4,X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_714])).

cnf(c_3370,plain,
    ( r2_waybel_7(sK4,sK6,sK5)
    | r2_hidden(sK5,sK1(sK4,sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_2191])).

cnf(c_3380,plain,
    ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
    | r2_hidden(sK5,sK1(sK4,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3370])).

cnf(c_14,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_549,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_34])).

cnf(c_550,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_554,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_550,c_33,c_32])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_570,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_554,c_5])).

cnf(c_25,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X0,k1_yellow19(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_528,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X0,k1_yellow19(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_529,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X0,k1_yellow19(sK4,X1))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_533,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X0,k1_yellow19(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_529,c_33,c_32])).

cnf(c_1240,plain,
    ( ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,k1_yellow19(sK4,X1)) ),
    inference(resolution,[status(thm)],[c_570,c_533])).

cnf(c_1254,plain,
    ( ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,k1_yellow19(sK4,X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1240,c_5])).

cnf(c_2184,plain,
    ( ~ v3_pre_topc(X0_53,sK4)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1_53,X0_53)
    | r2_hidden(X0_53,k1_yellow19(sK4,X1_53)) ),
    inference(subtyping,[status(esa)],[c_1254])).

cnf(c_4176,plain,
    ( ~ v3_pre_topc(sK1(sK4,sK6,sK5),sK4)
    | ~ m1_subset_1(sK1(sK4,sK6,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0_53,sK1(sK4,sK6,sK5))
    | r2_hidden(sK1(sK4,sK6,sK5),k1_yellow19(sK4,X0_53)) ),
    inference(instantiation,[status(thm)],[c_2184])).

cnf(c_4322,plain,
    ( ~ v3_pre_topc(sK1(sK4,sK6,sK5),sK4)
    | ~ m1_subset_1(sK1(sK4,sK6,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK1(sK4,sK6,sK5),k1_yellow19(sK4,sK5))
    | ~ r2_hidden(sK5,sK1(sK4,sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_4176])).

cnf(c_4323,plain,
    ( v3_pre_topc(sK1(sK4,sK6,sK5),sK4) != iProver_top
    | m1_subset_1(sK1(sK4,sK6,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK1(sK4,sK6,sK5),k1_yellow19(sK4,sK5)) = iProver_top
    | r2_hidden(sK5,sK1(sK4,sK6,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4322])).

cnf(c_5473,plain,
    ( r2_hidden(sK1(sK4,sK6,sK5),X0_53)
    | ~ r2_hidden(sK1(sK4,sK6,sK5),k1_yellow19(sK4,sK5))
    | ~ r1_tarski(k1_yellow19(sK4,sK5),X0_53) ),
    inference(instantiation,[status(thm)],[c_2208])).

cnf(c_5474,plain,
    ( r2_hidden(sK1(sK4,sK6,sK5),X0_53) = iProver_top
    | r2_hidden(sK1(sK4,sK6,sK5),k1_yellow19(sK4,sK5)) != iProver_top
    | r1_tarski(k1_yellow19(sK4,sK5),X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5473])).

cnf(c_5476,plain,
    ( r2_hidden(sK1(sK4,sK6,sK5),k1_yellow19(sK4,sK5)) != iProver_top
    | r2_hidden(sK1(sK4,sK6,sK5),sK6) = iProver_top
    | r1_tarski(k1_yellow19(sK4,sK5),sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5474])).

cnf(c_7488,plain,
    ( r2_waybel_7(sK4,sK6,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7280,c_41,c_3374,c_3376,c_3378,c_3380,c_4323,c_5476])).

cnf(c_7490,plain,
    ( r2_waybel_7(sK4,sK6,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7488])).

cnf(c_2215,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_3632,plain,
    ( X0_53 != X1_53
    | X0_53 = u1_struct_0(sK4)
    | u1_struct_0(sK4) != X1_53 ),
    inference(instantiation,[status(thm)],[c_2215])).

cnf(c_5046,plain,
    ( X0_53 = u1_struct_0(sK4)
    | X0_53 != k2_struct_0(sK4)
    | u1_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3632])).

cnf(c_5779,plain,
    ( u1_struct_0(sK4) != k2_struct_0(sK4)
    | k2_struct_0(sK4) = u1_struct_0(sK4)
    | k2_struct_0(sK4) != k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_5046])).

cnf(c_26,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k1_yellow19(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_507,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k1_yellow19(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_34])).

cnf(c_508,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,k1_yellow19(sK4,X1))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_512,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X0,k1_yellow19(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_508,c_33,c_32])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_13,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_211,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_13])).

cnf(c_212,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_211])).

cnf(c_486,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_212,c_34])).

cnf(c_487,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k1_tops_1(sK4,X0))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_491,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k1_tops_1(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_487,c_33,c_32])).

cnf(c_1299,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k1_yellow19(sK4,X0))
    | r2_hidden(X0,k1_tops_1(sK4,X1)) ),
    inference(resolution,[status(thm)],[c_512,c_491])).

cnf(c_2181,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ r2_hidden(X1_53,k1_yellow19(sK4,X0_53))
    | r2_hidden(X0_53,k1_tops_1(sK4,X1_53)) ),
    inference(subtyping,[status(esa)],[c_1299])).

cnf(c_3281,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(X0_53,k1_yellow19(sK4,sK5))
    | r2_hidden(sK5,k1_tops_1(sK4,X0_53)) ),
    inference(instantiation,[status(thm)],[c_2181])).

cnf(c_3561,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),k1_yellow19(sK4,sK5))
    | r2_hidden(sK5,k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6))) ),
    inference(instantiation,[status(thm)],[c_3281])).

cnf(c_578,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_34])).

cnf(c_579,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_583,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_579,c_33,c_32])).

cnf(c_1284,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,k1_yellow19(sK4,X0)) ),
    inference(resolution,[status(thm)],[c_512,c_583])).

cnf(c_2182,plain,
    ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1_53,k1_yellow19(sK4,X0_53)) ),
    inference(subtyping,[status(esa)],[c_1284])).

cnf(c_3276,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(X0_53,k1_yellow19(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2182])).

cnf(c_3562,plain,
    ( m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),k1_yellow19(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3276])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2210,plain,
    ( ~ r2_hidden(sK0(X0_53,X1_53),X1_53)
    | r1_tarski(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3307,plain,
    ( ~ r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),sK6)
    | r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_2210])).

cnf(c_3304,plain,
    ( r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),k1_yellow19(sK4,sK5))
    | r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
    inference(instantiation,[status(thm)],[c_2209])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_472,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_7,c_6])).

cnf(c_783,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_472,c_32])).

cnf(c_784,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_783])).

cnf(c_2188,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_784])).

cnf(c_2213,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_2246,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2213])).

cnf(c_2220,plain,
    ( X0_54 != X1_54
    | k2_struct_0(X0_54) = k2_struct_0(X1_54) ),
    theory(equality)).

cnf(c_2234,plain,
    ( sK4 != sK4
    | k2_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2220])).

cnf(c_27,negated_conjecture,
    ( ~ r2_waybel_7(sK4,sK6,sK5)
    | ~ r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_30,negated_conjecture,
    ( v13_waybel_0(sK6,k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f94])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_56428,c_53444,c_31018,c_17992,c_10975,c_10726,c_10166,c_8164,c_7742,c_7490,c_5779,c_3561,c_3562,c_3307,c_3304,c_2188,c_2246,c_2234,c_27,c_29,c_30,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:41:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.63/2.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.63/2.02  
% 11.63/2.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.63/2.02  
% 11.63/2.02  ------  iProver source info
% 11.63/2.02  
% 11.63/2.02  git: date: 2020-06-30 10:37:57 +0100
% 11.63/2.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.63/2.02  git: non_committed_changes: false
% 11.63/2.02  git: last_make_outside_of_git: false
% 11.63/2.02  
% 11.63/2.02  ------ 
% 11.63/2.02  
% 11.63/2.02  ------ Input Options
% 11.63/2.02  
% 11.63/2.02  --out_options                           all
% 11.63/2.02  --tptp_safe_out                         true
% 11.63/2.02  --problem_path                          ""
% 11.63/2.02  --include_path                          ""
% 11.63/2.02  --clausifier                            res/vclausify_rel
% 11.63/2.02  --clausifier_options                    --mode clausify
% 11.63/2.02  --stdin                                 false
% 11.63/2.02  --stats_out                             all
% 11.63/2.02  
% 11.63/2.02  ------ General Options
% 11.63/2.02  
% 11.63/2.02  --fof                                   false
% 11.63/2.02  --time_out_real                         305.
% 11.63/2.02  --time_out_virtual                      -1.
% 11.63/2.02  --symbol_type_check                     false
% 11.63/2.02  --clausify_out                          false
% 11.63/2.02  --sig_cnt_out                           false
% 11.63/2.02  --trig_cnt_out                          false
% 11.63/2.02  --trig_cnt_out_tolerance                1.
% 11.63/2.02  --trig_cnt_out_sk_spl                   false
% 11.63/2.02  --abstr_cl_out                          false
% 11.63/2.02  
% 11.63/2.02  ------ Global Options
% 11.63/2.02  
% 11.63/2.02  --schedule                              default
% 11.63/2.02  --add_important_lit                     false
% 11.63/2.02  --prop_solver_per_cl                    1000
% 11.63/2.02  --min_unsat_core                        false
% 11.63/2.02  --soft_assumptions                      false
% 11.63/2.02  --soft_lemma_size                       3
% 11.63/2.02  --prop_impl_unit_size                   0
% 11.63/2.02  --prop_impl_unit                        []
% 11.63/2.02  --share_sel_clauses                     true
% 11.63/2.02  --reset_solvers                         false
% 11.63/2.02  --bc_imp_inh                            [conj_cone]
% 11.63/2.02  --conj_cone_tolerance                   3.
% 11.63/2.02  --extra_neg_conj                        none
% 11.63/2.02  --large_theory_mode                     true
% 11.63/2.02  --prolific_symb_bound                   200
% 11.63/2.02  --lt_threshold                          2000
% 11.63/2.02  --clause_weak_htbl                      true
% 11.63/2.02  --gc_record_bc_elim                     false
% 11.63/2.02  
% 11.63/2.02  ------ Preprocessing Options
% 11.63/2.02  
% 11.63/2.02  --preprocessing_flag                    true
% 11.63/2.02  --time_out_prep_mult                    0.1
% 11.63/2.02  --splitting_mode                        input
% 11.63/2.02  --splitting_grd                         true
% 11.63/2.02  --splitting_cvd                         false
% 11.63/2.02  --splitting_cvd_svl                     false
% 11.63/2.02  --splitting_nvd                         32
% 11.63/2.02  --sub_typing                            true
% 11.63/2.02  --prep_gs_sim                           true
% 11.63/2.02  --prep_unflatten                        true
% 11.63/2.02  --prep_res_sim                          true
% 11.63/2.02  --prep_upred                            true
% 11.63/2.02  --prep_sem_filter                       exhaustive
% 11.63/2.02  --prep_sem_filter_out                   false
% 11.63/2.02  --pred_elim                             true
% 11.63/2.02  --res_sim_input                         true
% 11.63/2.02  --eq_ax_congr_red                       true
% 11.63/2.02  --pure_diseq_elim                       true
% 11.63/2.02  --brand_transform                       false
% 11.63/2.02  --non_eq_to_eq                          false
% 11.63/2.02  --prep_def_merge                        true
% 11.63/2.02  --prep_def_merge_prop_impl              false
% 11.63/2.02  --prep_def_merge_mbd                    true
% 11.63/2.02  --prep_def_merge_tr_red                 false
% 11.63/2.02  --prep_def_merge_tr_cl                  false
% 11.63/2.02  --smt_preprocessing                     true
% 11.63/2.02  --smt_ac_axioms                         fast
% 11.63/2.02  --preprocessed_out                      false
% 11.63/2.02  --preprocessed_stats                    false
% 11.63/2.02  
% 11.63/2.02  ------ Abstraction refinement Options
% 11.63/2.02  
% 11.63/2.02  --abstr_ref                             []
% 11.63/2.02  --abstr_ref_prep                        false
% 11.63/2.02  --abstr_ref_until_sat                   false
% 11.63/2.02  --abstr_ref_sig_restrict                funpre
% 11.63/2.02  --abstr_ref_af_restrict_to_split_sk     false
% 11.63/2.02  --abstr_ref_under                       []
% 11.63/2.02  
% 11.63/2.02  ------ SAT Options
% 11.63/2.02  
% 11.63/2.02  --sat_mode                              false
% 11.63/2.02  --sat_fm_restart_options                ""
% 11.63/2.02  --sat_gr_def                            false
% 11.63/2.02  --sat_epr_types                         true
% 11.63/2.02  --sat_non_cyclic_types                  false
% 11.63/2.02  --sat_finite_models                     false
% 11.63/2.02  --sat_fm_lemmas                         false
% 11.63/2.02  --sat_fm_prep                           false
% 11.63/2.02  --sat_fm_uc_incr                        true
% 11.63/2.02  --sat_out_model                         small
% 11.63/2.02  --sat_out_clauses                       false
% 11.63/2.02  
% 11.63/2.02  ------ QBF Options
% 11.63/2.02  
% 11.63/2.02  --qbf_mode                              false
% 11.63/2.02  --qbf_elim_univ                         false
% 11.63/2.02  --qbf_dom_inst                          none
% 11.63/2.02  --qbf_dom_pre_inst                      false
% 11.63/2.02  --qbf_sk_in                             false
% 11.63/2.02  --qbf_pred_elim                         true
% 11.63/2.02  --qbf_split                             512
% 11.63/2.02  
% 11.63/2.02  ------ BMC1 Options
% 11.63/2.02  
% 11.63/2.02  --bmc1_incremental                      false
% 11.63/2.02  --bmc1_axioms                           reachable_all
% 11.63/2.02  --bmc1_min_bound                        0
% 11.63/2.02  --bmc1_max_bound                        -1
% 11.63/2.02  --bmc1_max_bound_default                -1
% 11.63/2.02  --bmc1_symbol_reachability              true
% 11.63/2.02  --bmc1_property_lemmas                  false
% 11.63/2.02  --bmc1_k_induction                      false
% 11.63/2.02  --bmc1_non_equiv_states                 false
% 11.63/2.02  --bmc1_deadlock                         false
% 11.63/2.02  --bmc1_ucm                              false
% 11.63/2.02  --bmc1_add_unsat_core                   none
% 11.63/2.02  --bmc1_unsat_core_children              false
% 11.63/2.02  --bmc1_unsat_core_extrapolate_axioms    false
% 11.63/2.02  --bmc1_out_stat                         full
% 11.63/2.02  --bmc1_ground_init                      false
% 11.63/2.02  --bmc1_pre_inst_next_state              false
% 11.63/2.02  --bmc1_pre_inst_state                   false
% 11.63/2.02  --bmc1_pre_inst_reach_state             false
% 11.63/2.02  --bmc1_out_unsat_core                   false
% 11.63/2.02  --bmc1_aig_witness_out                  false
% 11.63/2.02  --bmc1_verbose                          false
% 11.63/2.02  --bmc1_dump_clauses_tptp                false
% 11.63/2.02  --bmc1_dump_unsat_core_tptp             false
% 11.63/2.02  --bmc1_dump_file                        -
% 11.63/2.02  --bmc1_ucm_expand_uc_limit              128
% 11.63/2.02  --bmc1_ucm_n_expand_iterations          6
% 11.63/2.02  --bmc1_ucm_extend_mode                  1
% 11.63/2.02  --bmc1_ucm_init_mode                    2
% 11.63/2.02  --bmc1_ucm_cone_mode                    none
% 11.63/2.02  --bmc1_ucm_reduced_relation_type        0
% 11.63/2.02  --bmc1_ucm_relax_model                  4
% 11.63/2.02  --bmc1_ucm_full_tr_after_sat            true
% 11.63/2.02  --bmc1_ucm_expand_neg_assumptions       false
% 11.63/2.02  --bmc1_ucm_layered_model                none
% 11.63/2.02  --bmc1_ucm_max_lemma_size               10
% 11.63/2.02  
% 11.63/2.02  ------ AIG Options
% 11.63/2.02  
% 11.63/2.02  --aig_mode                              false
% 11.63/2.02  
% 11.63/2.02  ------ Instantiation Options
% 11.63/2.02  
% 11.63/2.02  --instantiation_flag                    true
% 11.63/2.02  --inst_sos_flag                         false
% 11.63/2.02  --inst_sos_phase                        true
% 11.63/2.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.63/2.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.63/2.02  --inst_lit_sel_side                     num_symb
% 11.63/2.02  --inst_solver_per_active                1400
% 11.63/2.02  --inst_solver_calls_frac                1.
% 11.63/2.02  --inst_passive_queue_type               priority_queues
% 11.63/2.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.63/2.02  --inst_passive_queues_freq              [25;2]
% 11.63/2.02  --inst_dismatching                      true
% 11.63/2.02  --inst_eager_unprocessed_to_passive     true
% 11.63/2.02  --inst_prop_sim_given                   true
% 11.63/2.02  --inst_prop_sim_new                     false
% 11.63/2.02  --inst_subs_new                         false
% 11.63/2.02  --inst_eq_res_simp                      false
% 11.63/2.02  --inst_subs_given                       false
% 11.63/2.02  --inst_orphan_elimination               true
% 11.63/2.02  --inst_learning_loop_flag               true
% 11.63/2.02  --inst_learning_start                   3000
% 11.63/2.02  --inst_learning_factor                  2
% 11.63/2.02  --inst_start_prop_sim_after_learn       3
% 11.63/2.02  --inst_sel_renew                        solver
% 11.63/2.02  --inst_lit_activity_flag                true
% 11.63/2.02  --inst_restr_to_given                   false
% 11.63/2.02  --inst_activity_threshold               500
% 11.63/2.02  --inst_out_proof                        true
% 11.63/2.02  
% 11.63/2.02  ------ Resolution Options
% 11.63/2.02  
% 11.63/2.02  --resolution_flag                       true
% 11.63/2.02  --res_lit_sel                           adaptive
% 11.63/2.02  --res_lit_sel_side                      none
% 11.63/2.02  --res_ordering                          kbo
% 11.63/2.02  --res_to_prop_solver                    active
% 11.63/2.02  --res_prop_simpl_new                    false
% 11.63/2.02  --res_prop_simpl_given                  true
% 11.63/2.02  --res_passive_queue_type                priority_queues
% 11.63/2.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.63/2.02  --res_passive_queues_freq               [15;5]
% 11.63/2.02  --res_forward_subs                      full
% 11.63/2.02  --res_backward_subs                     full
% 11.63/2.02  --res_forward_subs_resolution           true
% 11.63/2.02  --res_backward_subs_resolution          true
% 11.63/2.02  --res_orphan_elimination                true
% 11.63/2.02  --res_time_limit                        2.
% 11.63/2.02  --res_out_proof                         true
% 11.63/2.02  
% 11.63/2.02  ------ Superposition Options
% 11.63/2.02  
% 11.63/2.02  --superposition_flag                    true
% 11.63/2.02  --sup_passive_queue_type                priority_queues
% 11.63/2.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.63/2.02  --sup_passive_queues_freq               [8;1;4]
% 11.63/2.02  --demod_completeness_check              fast
% 11.63/2.02  --demod_use_ground                      true
% 11.63/2.02  --sup_to_prop_solver                    passive
% 11.63/2.02  --sup_prop_simpl_new                    true
% 11.63/2.02  --sup_prop_simpl_given                  true
% 11.63/2.02  --sup_fun_splitting                     false
% 11.63/2.02  --sup_smt_interval                      50000
% 11.63/2.02  
% 11.63/2.02  ------ Superposition Simplification Setup
% 11.63/2.02  
% 11.63/2.02  --sup_indices_passive                   []
% 11.63/2.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.63/2.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.63/2.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.63/2.02  --sup_full_triv                         [TrivRules;PropSubs]
% 11.63/2.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.63/2.02  --sup_full_bw                           [BwDemod]
% 11.63/2.02  --sup_immed_triv                        [TrivRules]
% 11.63/2.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.63/2.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.63/2.02  --sup_immed_bw_main                     []
% 11.63/2.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.63/2.02  --sup_input_triv                        [Unflattening;TrivRules]
% 11.63/2.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.63/2.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.63/2.02  
% 11.63/2.02  ------ Combination Options
% 11.63/2.02  
% 11.63/2.02  --comb_res_mult                         3
% 11.63/2.02  --comb_sup_mult                         2
% 11.63/2.02  --comb_inst_mult                        10
% 11.63/2.02  
% 11.63/2.02  ------ Debug Options
% 11.63/2.02  
% 11.63/2.02  --dbg_backtrace                         false
% 11.63/2.02  --dbg_dump_prop_clauses                 false
% 11.63/2.02  --dbg_dump_prop_clauses_file            -
% 11.63/2.02  --dbg_out_stat                          false
% 11.63/2.02  ------ Parsing...
% 11.63/2.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.63/2.02  
% 11.63/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.63/2.02  
% 11.63/2.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.63/2.02  
% 11.63/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.63/2.02  ------ Proving...
% 11.63/2.02  ------ Problem Properties 
% 11.63/2.02  
% 11.63/2.02  
% 11.63/2.02  clauses                                 30
% 11.63/2.02  conjectures                             5
% 11.63/2.02  EPR                                     1
% 11.63/2.02  Horn                                    22
% 11.63/2.02  unary                                   4
% 11.63/2.02  binary                                  13
% 11.63/2.02  lits                                    77
% 11.63/2.02  lits eq                                 1
% 11.63/2.02  fd_pure                                 0
% 11.63/2.02  fd_pseudo                               0
% 11.63/2.02  fd_cond                                 0
% 11.63/2.02  fd_pseudo_cond                          0
% 11.63/2.02  AC symbols                              0
% 11.63/2.02  
% 11.63/2.02  ------ Schedule dynamic 5 is on 
% 11.63/2.02  
% 11.63/2.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.63/2.02  
% 11.63/2.02  
% 11.63/2.02  ------ 
% 11.63/2.02  Current options:
% 11.63/2.02  ------ 
% 11.63/2.02  
% 11.63/2.02  ------ Input Options
% 11.63/2.02  
% 11.63/2.02  --out_options                           all
% 11.63/2.02  --tptp_safe_out                         true
% 11.63/2.02  --problem_path                          ""
% 11.63/2.02  --include_path                          ""
% 11.63/2.02  --clausifier                            res/vclausify_rel
% 11.63/2.02  --clausifier_options                    --mode clausify
% 11.63/2.02  --stdin                                 false
% 11.63/2.02  --stats_out                             all
% 11.63/2.02  
% 11.63/2.02  ------ General Options
% 11.63/2.02  
% 11.63/2.02  --fof                                   false
% 11.63/2.02  --time_out_real                         305.
% 11.63/2.02  --time_out_virtual                      -1.
% 11.63/2.02  --symbol_type_check                     false
% 11.63/2.02  --clausify_out                          false
% 11.63/2.02  --sig_cnt_out                           false
% 11.63/2.02  --trig_cnt_out                          false
% 11.63/2.02  --trig_cnt_out_tolerance                1.
% 11.63/2.02  --trig_cnt_out_sk_spl                   false
% 11.63/2.02  --abstr_cl_out                          false
% 11.63/2.02  
% 11.63/2.02  ------ Global Options
% 11.63/2.02  
% 11.63/2.02  --schedule                              default
% 11.63/2.02  --add_important_lit                     false
% 11.63/2.02  --prop_solver_per_cl                    1000
% 11.63/2.02  --min_unsat_core                        false
% 11.63/2.02  --soft_assumptions                      false
% 11.63/2.02  --soft_lemma_size                       3
% 11.63/2.02  --prop_impl_unit_size                   0
% 11.63/2.02  --prop_impl_unit                        []
% 11.63/2.02  --share_sel_clauses                     true
% 11.63/2.02  --reset_solvers                         false
% 11.63/2.02  --bc_imp_inh                            [conj_cone]
% 11.63/2.02  --conj_cone_tolerance                   3.
% 11.63/2.02  --extra_neg_conj                        none
% 11.63/2.02  --large_theory_mode                     true
% 11.63/2.02  --prolific_symb_bound                   200
% 11.63/2.02  --lt_threshold                          2000
% 11.63/2.02  --clause_weak_htbl                      true
% 11.63/2.02  --gc_record_bc_elim                     false
% 11.63/2.02  
% 11.63/2.02  ------ Preprocessing Options
% 11.63/2.02  
% 11.63/2.02  --preprocessing_flag                    true
% 11.63/2.02  --time_out_prep_mult                    0.1
% 11.63/2.02  --splitting_mode                        input
% 11.63/2.02  --splitting_grd                         true
% 11.63/2.02  --splitting_cvd                         false
% 11.63/2.02  --splitting_cvd_svl                     false
% 11.63/2.02  --splitting_nvd                         32
% 11.63/2.02  --sub_typing                            true
% 11.63/2.02  --prep_gs_sim                           true
% 11.63/2.02  --prep_unflatten                        true
% 11.63/2.02  --prep_res_sim                          true
% 11.63/2.02  --prep_upred                            true
% 11.63/2.02  --prep_sem_filter                       exhaustive
% 11.63/2.02  --prep_sem_filter_out                   false
% 11.63/2.02  --pred_elim                             true
% 11.63/2.02  --res_sim_input                         true
% 11.63/2.02  --eq_ax_congr_red                       true
% 11.63/2.02  --pure_diseq_elim                       true
% 11.63/2.02  --brand_transform                       false
% 11.63/2.02  --non_eq_to_eq                          false
% 11.63/2.02  --prep_def_merge                        true
% 11.63/2.02  --prep_def_merge_prop_impl              false
% 11.63/2.02  --prep_def_merge_mbd                    true
% 11.63/2.02  --prep_def_merge_tr_red                 false
% 11.63/2.02  --prep_def_merge_tr_cl                  false
% 11.63/2.02  --smt_preprocessing                     true
% 11.63/2.02  --smt_ac_axioms                         fast
% 11.63/2.02  --preprocessed_out                      false
% 11.63/2.02  --preprocessed_stats                    false
% 11.63/2.02  
% 11.63/2.02  ------ Abstraction refinement Options
% 11.63/2.02  
% 11.63/2.02  --abstr_ref                             []
% 11.63/2.02  --abstr_ref_prep                        false
% 11.63/2.02  --abstr_ref_until_sat                   false
% 11.63/2.02  --abstr_ref_sig_restrict                funpre
% 11.63/2.02  --abstr_ref_af_restrict_to_split_sk     false
% 11.63/2.02  --abstr_ref_under                       []
% 11.63/2.02  
% 11.63/2.02  ------ SAT Options
% 11.63/2.02  
% 11.63/2.02  --sat_mode                              false
% 11.63/2.02  --sat_fm_restart_options                ""
% 11.63/2.02  --sat_gr_def                            false
% 11.63/2.02  --sat_epr_types                         true
% 11.63/2.02  --sat_non_cyclic_types                  false
% 11.63/2.02  --sat_finite_models                     false
% 11.63/2.02  --sat_fm_lemmas                         false
% 11.63/2.02  --sat_fm_prep                           false
% 11.63/2.02  --sat_fm_uc_incr                        true
% 11.63/2.02  --sat_out_model                         small
% 11.63/2.02  --sat_out_clauses                       false
% 11.63/2.02  
% 11.63/2.02  ------ QBF Options
% 11.63/2.02  
% 11.63/2.02  --qbf_mode                              false
% 11.63/2.02  --qbf_elim_univ                         false
% 11.63/2.02  --qbf_dom_inst                          none
% 11.63/2.02  --qbf_dom_pre_inst                      false
% 11.63/2.02  --qbf_sk_in                             false
% 11.63/2.02  --qbf_pred_elim                         true
% 11.63/2.02  --qbf_split                             512
% 11.63/2.02  
% 11.63/2.02  ------ BMC1 Options
% 11.63/2.02  
% 11.63/2.02  --bmc1_incremental                      false
% 11.63/2.02  --bmc1_axioms                           reachable_all
% 11.63/2.02  --bmc1_min_bound                        0
% 11.63/2.02  --bmc1_max_bound                        -1
% 11.63/2.02  --bmc1_max_bound_default                -1
% 11.63/2.02  --bmc1_symbol_reachability              true
% 11.63/2.02  --bmc1_property_lemmas                  false
% 11.63/2.02  --bmc1_k_induction                      false
% 11.63/2.02  --bmc1_non_equiv_states                 false
% 11.63/2.02  --bmc1_deadlock                         false
% 11.63/2.02  --bmc1_ucm                              false
% 11.63/2.02  --bmc1_add_unsat_core                   none
% 11.63/2.02  --bmc1_unsat_core_children              false
% 11.63/2.02  --bmc1_unsat_core_extrapolate_axioms    false
% 11.63/2.02  --bmc1_out_stat                         full
% 11.63/2.02  --bmc1_ground_init                      false
% 11.63/2.02  --bmc1_pre_inst_next_state              false
% 11.63/2.02  --bmc1_pre_inst_state                   false
% 11.63/2.02  --bmc1_pre_inst_reach_state             false
% 11.63/2.02  --bmc1_out_unsat_core                   false
% 11.63/2.02  --bmc1_aig_witness_out                  false
% 11.63/2.02  --bmc1_verbose                          false
% 11.63/2.02  --bmc1_dump_clauses_tptp                false
% 11.63/2.02  --bmc1_dump_unsat_core_tptp             false
% 11.63/2.02  --bmc1_dump_file                        -
% 11.63/2.02  --bmc1_ucm_expand_uc_limit              128
% 11.63/2.02  --bmc1_ucm_n_expand_iterations          6
% 11.63/2.02  --bmc1_ucm_extend_mode                  1
% 11.63/2.02  --bmc1_ucm_init_mode                    2
% 11.63/2.02  --bmc1_ucm_cone_mode                    none
% 11.63/2.02  --bmc1_ucm_reduced_relation_type        0
% 11.63/2.02  --bmc1_ucm_relax_model                  4
% 11.63/2.02  --bmc1_ucm_full_tr_after_sat            true
% 11.63/2.02  --bmc1_ucm_expand_neg_assumptions       false
% 11.63/2.02  --bmc1_ucm_layered_model                none
% 11.63/2.02  --bmc1_ucm_max_lemma_size               10
% 11.63/2.02  
% 11.63/2.02  ------ AIG Options
% 11.63/2.02  
% 11.63/2.02  --aig_mode                              false
% 11.63/2.02  
% 11.63/2.02  ------ Instantiation Options
% 11.63/2.02  
% 11.63/2.02  --instantiation_flag                    true
% 11.63/2.02  --inst_sos_flag                         false
% 11.63/2.02  --inst_sos_phase                        true
% 11.63/2.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.63/2.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.63/2.02  --inst_lit_sel_side                     none
% 11.63/2.02  --inst_solver_per_active                1400
% 11.63/2.02  --inst_solver_calls_frac                1.
% 11.63/2.02  --inst_passive_queue_type               priority_queues
% 11.63/2.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.63/2.02  --inst_passive_queues_freq              [25;2]
% 11.63/2.02  --inst_dismatching                      true
% 11.63/2.02  --inst_eager_unprocessed_to_passive     true
% 11.63/2.02  --inst_prop_sim_given                   true
% 11.63/2.02  --inst_prop_sim_new                     false
% 11.63/2.02  --inst_subs_new                         false
% 11.63/2.02  --inst_eq_res_simp                      false
% 11.63/2.02  --inst_subs_given                       false
% 11.63/2.02  --inst_orphan_elimination               true
% 11.63/2.02  --inst_learning_loop_flag               true
% 11.63/2.02  --inst_learning_start                   3000
% 11.63/2.02  --inst_learning_factor                  2
% 11.63/2.02  --inst_start_prop_sim_after_learn       3
% 11.63/2.02  --inst_sel_renew                        solver
% 11.63/2.02  --inst_lit_activity_flag                true
% 11.63/2.02  --inst_restr_to_given                   false
% 11.63/2.02  --inst_activity_threshold               500
% 11.63/2.02  --inst_out_proof                        true
% 11.63/2.02  
% 11.63/2.02  ------ Resolution Options
% 11.63/2.02  
% 11.63/2.02  --resolution_flag                       false
% 11.63/2.02  --res_lit_sel                           adaptive
% 11.63/2.02  --res_lit_sel_side                      none
% 11.63/2.02  --res_ordering                          kbo
% 11.63/2.02  --res_to_prop_solver                    active
% 11.63/2.02  --res_prop_simpl_new                    false
% 11.63/2.02  --res_prop_simpl_given                  true
% 11.63/2.02  --res_passive_queue_type                priority_queues
% 11.63/2.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.63/2.02  --res_passive_queues_freq               [15;5]
% 11.63/2.02  --res_forward_subs                      full
% 11.63/2.02  --res_backward_subs                     full
% 11.63/2.02  --res_forward_subs_resolution           true
% 11.63/2.02  --res_backward_subs_resolution          true
% 11.63/2.02  --res_orphan_elimination                true
% 11.63/2.02  --res_time_limit                        2.
% 11.63/2.02  --res_out_proof                         true
% 11.63/2.02  
% 11.63/2.02  ------ Superposition Options
% 11.63/2.02  
% 11.63/2.02  --superposition_flag                    true
% 11.63/2.02  --sup_passive_queue_type                priority_queues
% 11.63/2.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.63/2.02  --sup_passive_queues_freq               [8;1;4]
% 11.63/2.02  --demod_completeness_check              fast
% 11.63/2.02  --demod_use_ground                      true
% 11.63/2.02  --sup_to_prop_solver                    passive
% 11.63/2.02  --sup_prop_simpl_new                    true
% 11.63/2.02  --sup_prop_simpl_given                  true
% 11.63/2.02  --sup_fun_splitting                     false
% 11.63/2.02  --sup_smt_interval                      50000
% 11.63/2.02  
% 11.63/2.02  ------ Superposition Simplification Setup
% 11.63/2.02  
% 11.63/2.02  --sup_indices_passive                   []
% 11.63/2.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.63/2.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.63/2.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.63/2.02  --sup_full_triv                         [TrivRules;PropSubs]
% 11.63/2.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.63/2.02  --sup_full_bw                           [BwDemod]
% 11.63/2.02  --sup_immed_triv                        [TrivRules]
% 11.63/2.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.63/2.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.63/2.02  --sup_immed_bw_main                     []
% 11.63/2.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.63/2.02  --sup_input_triv                        [Unflattening;TrivRules]
% 11.63/2.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.63/2.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.63/2.02  
% 11.63/2.02  ------ Combination Options
% 11.63/2.02  
% 11.63/2.02  --comb_res_mult                         3
% 11.63/2.02  --comb_sup_mult                         2
% 11.63/2.02  --comb_inst_mult                        10
% 11.63/2.02  
% 11.63/2.02  ------ Debug Options
% 11.63/2.02  
% 11.63/2.02  --dbg_backtrace                         false
% 11.63/2.02  --dbg_dump_prop_clauses                 false
% 11.63/2.02  --dbg_dump_prop_clauses_file            -
% 11.63/2.02  --dbg_out_stat                          false
% 11.63/2.02  
% 11.63/2.02  
% 11.63/2.02  
% 11.63/2.02  
% 11.63/2.02  ------ Proving...
% 11.63/2.02  
% 11.63/2.02  
% 11.63/2.02  % SZS status Theorem for theBenchmark.p
% 11.63/2.02  
% 11.63/2.02  % SZS output start CNFRefutation for theBenchmark.p
% 11.63/2.02  
% 11.63/2.02  fof(f14,axiom,(
% 11.63/2.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) => (v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : ((r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => r2_hidden(X3,X1))))),
% 11.63/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.02  
% 11.63/2.02  fof(f36,plain,(
% 11.63/2.02    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | (~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 11.63/2.02    inference(ennf_transformation,[],[f14])).
% 11.63/2.02  
% 11.63/2.02  fof(f37,plain,(
% 11.63/2.02    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 11.63/2.02    inference(flattening,[],[f36])).
% 11.63/2.02  
% 11.63/2.02  fof(f52,plain,(
% 11.63/2.02    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 11.63/2.02    inference(nnf_transformation,[],[f37])).
% 11.63/2.02  
% 11.63/2.02  fof(f53,plain,(
% 11.63/2.02    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 11.63/2.02    inference(rectify,[],[f52])).
% 11.63/2.02  
% 11.63/2.02  fof(f54,plain,(
% 11.63/2.02    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK2(X0,X1),X1) & r1_tarski(sK3(X0,X1),X0) & r1_tarski(sK2(X0,X1),sK3(X0,X1))))),
% 11.63/2.02    introduced(choice_axiom,[])).
% 11.63/2.02  
% 11.63/2.02  fof(f55,plain,(
% 11.63/2.02    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK2(X0,X1),X1) & r1_tarski(sK3(X0,X1),X0) & r1_tarski(sK2(X0,X1),sK3(X0,X1)))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 11.63/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f53,f54])).
% 11.63/2.02  
% 11.63/2.02  fof(f84,plain,(
% 11.63/2.02    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))) )),
% 11.63/2.02    inference(cnf_transformation,[],[f55])).
% 11.63/2.02  
% 11.63/2.02  fof(f12,axiom,(
% 11.63/2.02    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 11.63/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.02  
% 11.63/2.02  fof(f78,plain,(
% 11.63/2.02    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 11.63/2.02    inference(cnf_transformation,[],[f12])).
% 11.63/2.02  
% 11.63/2.02  fof(f103,plain,(
% 11.63/2.02    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))) )),
% 11.63/2.02    inference(definition_unfolding,[],[f84,f78,f78])).
% 11.63/2.02  
% 11.63/2.02  fof(f2,axiom,(
% 11.63/2.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.63/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.02  
% 11.63/2.02  fof(f46,plain,(
% 11.63/2.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.63/2.02    inference(nnf_transformation,[],[f2])).
% 11.63/2.02  
% 11.63/2.02  fof(f66,plain,(
% 11.63/2.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.63/2.02    inference(cnf_transformation,[],[f46])).
% 11.63/2.02  
% 11.63/2.02  fof(f8,axiom,(
% 11.63/2.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 11.63/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.02  
% 11.63/2.02  fof(f27,plain,(
% 11.63/2.02    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.63/2.02    inference(ennf_transformation,[],[f8])).
% 11.63/2.02  
% 11.63/2.02  fof(f73,plain,(
% 11.63/2.02    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f27])).
% 11.63/2.02  
% 11.63/2.02  fof(f16,conjecture,(
% 11.63/2.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => (r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)))))),
% 11.63/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.02  
% 11.63/2.02  fof(f17,negated_conjecture,(
% 11.63/2.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => (r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)))))),
% 11.63/2.02    inference(negated_conjecture,[],[f16])).
% 11.63/2.02  
% 11.63/2.02  fof(f40,plain,(
% 11.63/2.02    ? [X0] : (? [X1] : (? [X2] : ((r2_waybel_7(X0,X2,X1) <~> r1_tarski(k1_yellow19(X0,X1),X2)) & (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.63/2.02    inference(ennf_transformation,[],[f17])).
% 11.63/2.02  
% 11.63/2.02  fof(f41,plain,(
% 11.63/2.02    ? [X0] : (? [X1] : (? [X2] : ((r2_waybel_7(X0,X2,X1) <~> r1_tarski(k1_yellow19(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.63/2.02    inference(flattening,[],[f40])).
% 11.63/2.02  
% 11.63/2.02  fof(f57,plain,(
% 11.63/2.02    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.63/2.02    inference(nnf_transformation,[],[f41])).
% 11.63/2.02  
% 11.63/2.02  fof(f58,plain,(
% 11.63/2.02    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.63/2.02    inference(flattening,[],[f57])).
% 11.63/2.02  
% 11.63/2.02  fof(f61,plain,(
% 11.63/2.02    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => ((~r1_tarski(k1_yellow19(X0,X1),sK6) | ~r2_waybel_7(X0,sK6,X1)) & (r1_tarski(k1_yellow19(X0,X1),sK6) | r2_waybel_7(X0,sK6,X1)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK6,k3_yellow_1(k2_struct_0(X0))))) )),
% 11.63/2.02    introduced(choice_axiom,[])).
% 11.63/2.02  
% 11.63/2.02  fof(f60,plain,(
% 11.63/2.02    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : ((~r1_tarski(k1_yellow19(X0,sK5),X2) | ~r2_waybel_7(X0,X2,sK5)) & (r1_tarski(k1_yellow19(X0,sK5),X2) | r2_waybel_7(X0,X2,sK5)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 11.63/2.02    introduced(choice_axiom,[])).
% 11.63/2.02  
% 11.63/2.02  fof(f59,plain,(
% 11.63/2.02    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(sK4,X1),X2) | ~r2_waybel_7(sK4,X2,X1)) & (r1_tarski(k1_yellow19(sK4,X1),X2) | r2_waybel_7(sK4,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK4)))) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 11.63/2.02    introduced(choice_axiom,[])).
% 11.63/2.02  
% 11.63/2.02  fof(f62,plain,(
% 11.63/2.02    (((~r1_tarski(k1_yellow19(sK4,sK5),sK6) | ~r2_waybel_7(sK4,sK6,sK5)) & (r1_tarski(k1_yellow19(sK4,sK5),sK6) | r2_waybel_7(sK4,sK6,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4))))) & v13_waybel_0(sK6,k3_yellow_1(k2_struct_0(sK4)))) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 11.63/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f58,f61,f60,f59])).
% 11.63/2.02  
% 11.63/2.02  fof(f93,plain,(
% 11.63/2.02    l1_pre_topc(sK4)),
% 11.63/2.02    inference(cnf_transformation,[],[f62])).
% 11.63/2.02  
% 11.63/2.02  fof(f7,axiom,(
% 11.63/2.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 11.63/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.02  
% 11.63/2.02  fof(f25,plain,(
% 11.63/2.02    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.63/2.02    inference(ennf_transformation,[],[f7])).
% 11.63/2.02  
% 11.63/2.02  fof(f26,plain,(
% 11.63/2.02    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.63/2.02    inference(flattening,[],[f25])).
% 11.63/2.02  
% 11.63/2.02  fof(f72,plain,(
% 11.63/2.02    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f26])).
% 11.63/2.02  
% 11.63/2.02  fof(f92,plain,(
% 11.63/2.02    v2_pre_topc(sK4)),
% 11.63/2.02    inference(cnf_transformation,[],[f62])).
% 11.63/2.02  
% 11.63/2.02  fof(f6,axiom,(
% 11.63/2.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.63/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.02  
% 11.63/2.02  fof(f23,plain,(
% 11.63/2.02    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.63/2.02    inference(ennf_transformation,[],[f6])).
% 11.63/2.02  
% 11.63/2.02  fof(f24,plain,(
% 11.63/2.02    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.63/2.02    inference(flattening,[],[f23])).
% 11.63/2.02  
% 11.63/2.02  fof(f71,plain,(
% 11.63/2.02    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f24])).
% 11.63/2.02  
% 11.63/2.02  fof(f13,axiom,(
% 11.63/2.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,X3) & v3_pre_topc(X3,X0)) => r2_hidden(X3,X1)))))),
% 11.63/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.02  
% 11.63/2.02  fof(f34,plain,(
% 11.63/2.02    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : ((r2_hidden(X3,X1) | (~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.63/2.02    inference(ennf_transformation,[],[f13])).
% 11.63/2.02  
% 11.63/2.02  fof(f35,plain,(
% 11.63/2.02    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.63/2.02    inference(flattening,[],[f34])).
% 11.63/2.02  
% 11.63/2.02  fof(f48,plain,(
% 11.63/2.02    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | ? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.63/2.02    inference(nnf_transformation,[],[f35])).
% 11.63/2.02  
% 11.63/2.02  fof(f49,plain,(
% 11.63/2.02    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | ? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.63/2.02    inference(rectify,[],[f48])).
% 11.63/2.02  
% 11.63/2.02  fof(f50,plain,(
% 11.63/2.02    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(X2,sK1(X0,X1,X2)) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.63/2.02    introduced(choice_axiom,[])).
% 11.63/2.02  
% 11.63/2.02  fof(f51,plain,(
% 11.63/2.02    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | (~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(X2,sK1(X0,X1,X2)) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.63/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).
% 11.63/2.02  
% 11.63/2.02  fof(f79,plain,(
% 11.63/2.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_waybel_7(X0,X1,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f51])).
% 11.63/2.02  
% 11.63/2.02  fof(f97,plain,(
% 11.63/2.02    r1_tarski(k1_yellow19(sK4,sK5),sK6) | r2_waybel_7(sK4,sK6,sK5)),
% 11.63/2.02    inference(cnf_transformation,[],[f62])).
% 11.63/2.02  
% 11.63/2.02  fof(f1,axiom,(
% 11.63/2.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.63/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.02  
% 11.63/2.02  fof(f18,plain,(
% 11.63/2.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.63/2.02    inference(ennf_transformation,[],[f1])).
% 11.63/2.02  
% 11.63/2.02  fof(f42,plain,(
% 11.63/2.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.63/2.02    inference(nnf_transformation,[],[f18])).
% 11.63/2.02  
% 11.63/2.02  fof(f43,plain,(
% 11.63/2.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.63/2.02    inference(rectify,[],[f42])).
% 11.63/2.02  
% 11.63/2.02  fof(f44,plain,(
% 11.63/2.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.63/2.02    introduced(choice_axiom,[])).
% 11.63/2.02  
% 11.63/2.02  fof(f45,plain,(
% 11.63/2.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.63/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 11.63/2.02  
% 11.63/2.02  fof(f64,plain,(
% 11.63/2.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f45])).
% 11.63/2.02  
% 11.63/2.02  fof(f63,plain,(
% 11.63/2.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f45])).
% 11.63/2.02  
% 11.63/2.02  fof(f81,plain,(
% 11.63/2.02    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | v3_pre_topc(sK1(X0,X1,X2),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f51])).
% 11.63/2.02  
% 11.63/2.02  fof(f80,plain,(
% 11.63/2.02    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f51])).
% 11.63/2.02  
% 11.63/2.02  fof(f83,plain,(
% 11.63/2.02    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | ~r2_hidden(sK1(X0,X1,X2),X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f51])).
% 11.63/2.02  
% 11.63/2.02  fof(f82,plain,(
% 11.63/2.02    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,sK1(X0,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f51])).
% 11.63/2.02  
% 11.63/2.02  fof(f11,axiom,(
% 11.63/2.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 11.63/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.02  
% 11.63/2.02  fof(f32,plain,(
% 11.63/2.02    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.63/2.02    inference(ennf_transformation,[],[f11])).
% 11.63/2.02  
% 11.63/2.02  fof(f33,plain,(
% 11.63/2.02    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.63/2.02    inference(flattening,[],[f32])).
% 11.63/2.02  
% 11.63/2.02  fof(f77,plain,(
% 11.63/2.02    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f33])).
% 11.63/2.02  
% 11.63/2.02  fof(f91,plain,(
% 11.63/2.02    ~v2_struct_0(sK4)),
% 11.63/2.02    inference(cnf_transformation,[],[f62])).
% 11.63/2.02  
% 11.63/2.02  fof(f3,axiom,(
% 11.63/2.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 11.63/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.02  
% 11.63/2.02  fof(f19,plain,(
% 11.63/2.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 11.63/2.02    inference(ennf_transformation,[],[f3])).
% 11.63/2.02  
% 11.63/2.02  fof(f20,plain,(
% 11.63/2.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 11.63/2.02    inference(flattening,[],[f19])).
% 11.63/2.02  
% 11.63/2.02  fof(f68,plain,(
% 11.63/2.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f20])).
% 11.63/2.02  
% 11.63/2.02  fof(f15,axiom,(
% 11.63/2.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1))))),
% 11.63/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.02  
% 11.63/2.02  fof(f38,plain,(
% 11.63/2.02    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.63/2.02    inference(ennf_transformation,[],[f15])).
% 11.63/2.02  
% 11.63/2.02  fof(f39,plain,(
% 11.63/2.02    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.63/2.02    inference(flattening,[],[f38])).
% 11.63/2.02  
% 11.63/2.02  fof(f56,plain,(
% 11.63/2.02    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_connsp_2(X2,X0,X1)) & (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X2,k1_yellow19(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.63/2.02    inference(nnf_transformation,[],[f39])).
% 11.63/2.02  
% 11.63/2.02  fof(f90,plain,(
% 11.63/2.02    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f56])).
% 11.63/2.02  
% 11.63/2.02  fof(f89,plain,(
% 11.63/2.02    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f56])).
% 11.63/2.02  
% 11.63/2.02  fof(f9,axiom,(
% 11.63/2.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 11.63/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.02  
% 11.63/2.02  fof(f28,plain,(
% 11.63/2.02    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.63/2.02    inference(ennf_transformation,[],[f9])).
% 11.63/2.02  
% 11.63/2.02  fof(f29,plain,(
% 11.63/2.02    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.63/2.02    inference(flattening,[],[f28])).
% 11.63/2.02  
% 11.63/2.02  fof(f47,plain,(
% 11.63/2.02    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.63/2.02    inference(nnf_transformation,[],[f29])).
% 11.63/2.02  
% 11.63/2.02  fof(f74,plain,(
% 11.63/2.02    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f47])).
% 11.63/2.02  
% 11.63/2.02  fof(f10,axiom,(
% 11.63/2.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.63/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.02  
% 11.63/2.02  fof(f30,plain,(
% 11.63/2.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.63/2.02    inference(ennf_transformation,[],[f10])).
% 11.63/2.02  
% 11.63/2.02  fof(f31,plain,(
% 11.63/2.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.63/2.02    inference(flattening,[],[f30])).
% 11.63/2.02  
% 11.63/2.02  fof(f76,plain,(
% 11.63/2.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f31])).
% 11.63/2.02  
% 11.63/2.02  fof(f65,plain,(
% 11.63/2.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f45])).
% 11.63/2.02  
% 11.63/2.02  fof(f5,axiom,(
% 11.63/2.02    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 11.63/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.02  
% 11.63/2.02  fof(f22,plain,(
% 11.63/2.02    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 11.63/2.02    inference(ennf_transformation,[],[f5])).
% 11.63/2.02  
% 11.63/2.02  fof(f70,plain,(
% 11.63/2.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f22])).
% 11.63/2.02  
% 11.63/2.02  fof(f4,axiom,(
% 11.63/2.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 11.63/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/2.02  
% 11.63/2.02  fof(f21,plain,(
% 11.63/2.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 11.63/2.02    inference(ennf_transformation,[],[f4])).
% 11.63/2.02  
% 11.63/2.02  fof(f69,plain,(
% 11.63/2.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 11.63/2.02    inference(cnf_transformation,[],[f21])).
% 11.63/2.02  
% 11.63/2.02  fof(f98,plain,(
% 11.63/2.02    ~r1_tarski(k1_yellow19(sK4,sK5),sK6) | ~r2_waybel_7(sK4,sK6,sK5)),
% 11.63/2.02    inference(cnf_transformation,[],[f62])).
% 11.63/2.02  
% 11.63/2.02  fof(f96,plain,(
% 11.63/2.02    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK4)))))),
% 11.63/2.02    inference(cnf_transformation,[],[f62])).
% 11.63/2.02  
% 11.63/2.02  fof(f104,plain,(
% 11.63/2.02    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))))),
% 11.63/2.02    inference(definition_unfolding,[],[f96,f78])).
% 11.63/2.02  
% 11.63/2.02  fof(f95,plain,(
% 11.63/2.02    v13_waybel_0(sK6,k3_yellow_1(k2_struct_0(sK4)))),
% 11.63/2.02    inference(cnf_transformation,[],[f62])).
% 11.63/2.02  
% 11.63/2.02  fof(f105,plain,(
% 11.63/2.02    v13_waybel_0(sK6,k3_lattice3(k1_lattice3(k2_struct_0(sK4))))),
% 11.63/2.02    inference(definition_unfolding,[],[f95,f78])).
% 11.63/2.02  
% 11.63/2.02  fof(f94,plain,(
% 11.63/2.02    m1_subset_1(sK5,u1_struct_0(sK4))),
% 11.63/2.02    inference(cnf_transformation,[],[f62])).
% 11.63/2.02  
% 11.63/2.02  cnf(c_24,plain,
% 11.63/2.02      ( ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 11.63/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 11.63/2.02      | ~ r2_hidden(X2,X0)
% 11.63/2.02      | r2_hidden(X3,X0)
% 11.63/2.02      | ~ r1_tarski(X3,X1)
% 11.63/2.02      | ~ r1_tarski(X2,X3) ),
% 11.63/2.02      inference(cnf_transformation,[],[f103]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2200,plain,
% 11.63/2.02      ( ~ v13_waybel_0(X0_53,k3_lattice3(k1_lattice3(X1_53)))
% 11.63/2.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1_53)))))
% 11.63/2.02      | ~ r2_hidden(X2_53,X0_53)
% 11.63/2.02      | r2_hidden(X3_53,X0_53)
% 11.63/2.02      | ~ r1_tarski(X3_53,X1_53)
% 11.63/2.02      | ~ r1_tarski(X2_53,X3_53) ),
% 11.63/2.02      inference(subtyping,[status(esa)],[c_24]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_14966,plain,
% 11.63/2.02      ( ~ v13_waybel_0(X0_53,k3_lattice3(k1_lattice3(X1_53)))
% 11.63/2.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1_53)))))
% 11.63/2.02      | r2_hidden(X2_53,X0_53)
% 11.63/2.02      | ~ r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),X0_53)
% 11.63/2.02      | ~ r1_tarski(X2_53,X1_53)
% 11.63/2.02      | ~ r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),X2_53) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2200]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_50928,plain,
% 11.63/2.02      ( ~ v13_waybel_0(sK6,k3_lattice3(k1_lattice3(k2_struct_0(sK4))))
% 11.63/2.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))))
% 11.63/2.02      | r2_hidden(X0_53,sK6)
% 11.63/2.02      | ~ r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK6)
% 11.63/2.02      | ~ r1_tarski(X0_53,k2_struct_0(sK4))
% 11.63/2.02      | ~ r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),X0_53) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_14966]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_56428,plain,
% 11.63/2.02      ( ~ v13_waybel_0(sK6,k3_lattice3(k1_lattice3(k2_struct_0(sK4))))
% 11.63/2.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4))))))
% 11.63/2.02      | ~ r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK6)
% 11.63/2.02      | r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),sK6)
% 11.63/2.02      | ~ r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK0(k1_yellow19(sK4,sK5),sK6))
% 11.63/2.02      | ~ r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),k2_struct_0(sK4)) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_50928]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2219,plain,
% 11.63/2.02      ( ~ m1_subset_1(X0_53,X1_53)
% 11.63/2.02      | m1_subset_1(X2_53,X3_53)
% 11.63/2.02      | X2_53 != X0_53
% 11.63/2.02      | X3_53 != X1_53 ),
% 11.63/2.02      theory(equality) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_4066,plain,
% 11.63/2.02      ( m1_subset_1(X0_53,X1_53)
% 11.63/2.02      | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),X2_53)
% 11.63/2.02      | X1_53 != X2_53
% 11.63/2.02      | X0_53 != sK0(k1_yellow19(sK4,sK5),sK6) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2219]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_5221,plain,
% 11.63/2.02      ( m1_subset_1(X0_53,X1_53)
% 11.63/2.02      | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(X2_53))
% 11.63/2.02      | X0_53 != sK0(k1_yellow19(sK4,sK5),sK6)
% 11.63/2.02      | X1_53 != k1_zfmisc_1(X2_53) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_4066]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_9321,plain,
% 11.63/2.02      ( m1_subset_1(X0_53,X1_53)
% 11.63/2.02      | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | X0_53 != sK0(k1_yellow19(sK4,sK5),sK6)
% 11.63/2.02      | X1_53 != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_5221]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_12357,plain,
% 11.63/2.02      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 11.63/2.02      | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | X0_53 != sK0(k1_yellow19(sK4,sK5),sK6)
% 11.63/2.02      | k1_zfmisc_1(X1_53) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_9321]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_19959,plain,
% 11.63/2.02      ( m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(X0_53))
% 11.63/2.02      | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | sK0(k1_yellow19(sK4,sK5),sK6) != sK0(k1_yellow19(sK4,sK5),sK6)
% 11.63/2.02      | k1_zfmisc_1(X0_53) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_12357]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_53444,plain,
% 11.63/2.02      ( ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(k2_struct_0(sK4)))
% 11.63/2.02      | sK0(k1_yellow19(sK4,sK5),sK6) != sK0(k1_yellow19(sK4,sK5),sK6)
% 11.63/2.02      | k1_zfmisc_1(k2_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_19959]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_4,plain,
% 11.63/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.63/2.02      inference(cnf_transformation,[],[f66]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2206,plain,
% 11.63/2.02      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 11.63/2.02      | r1_tarski(X0_53,X1_53) ),
% 11.63/2.02      inference(subtyping,[status(esa)],[c_4]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_13518,plain,
% 11.63/2.02      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_struct_0(sK4)))
% 11.63/2.02      | r1_tarski(X0_53,k2_struct_0(sK4)) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2206]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_31018,plain,
% 11.63/2.02      ( ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(k2_struct_0(sK4)))
% 11.63/2.02      | r1_tarski(sK0(k1_yellow19(sK4,sK5),sK6),k2_struct_0(sK4)) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_13518]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2218,plain,
% 11.63/2.02      ( X0_53 != X1_53 | k1_zfmisc_1(X0_53) = k1_zfmisc_1(X1_53) ),
% 11.63/2.02      theory(equality) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_12358,plain,
% 11.63/2.02      ( X0_53 != u1_struct_0(sK4)
% 11.63/2.02      | k1_zfmisc_1(X0_53) = k1_zfmisc_1(u1_struct_0(sK4)) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2218]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_17992,plain,
% 11.63/2.02      ( k2_struct_0(sK4) != u1_struct_0(sK4)
% 11.63/2.02      | k1_zfmisc_1(k2_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_12358]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_10,plain,
% 11.63/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.63/2.02      | r1_tarski(k1_tops_1(X1,X0),X0)
% 11.63/2.02      | ~ l1_pre_topc(X1) ),
% 11.63/2.02      inference(cnf_transformation,[],[f73]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_32,negated_conjecture,
% 11.63/2.02      ( l1_pre_topc(sK4) ),
% 11.63/2.02      inference(cnf_transformation,[],[f93]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_788,plain,
% 11.63/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.63/2.02      | r1_tarski(k1_tops_1(X1,X0),X0)
% 11.63/2.02      | sK4 != X1 ),
% 11.63/2.02      inference(resolution_lifted,[status(thm)],[c_10,c_32]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_789,plain,
% 11.63/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | r1_tarski(k1_tops_1(sK4,X0),X0) ),
% 11.63/2.02      inference(unflattening,[status(thm)],[c_788]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2187,plain,
% 11.63/2.02      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | r1_tarski(k1_tops_1(sK4,X0_53),X0_53) ),
% 11.63/2.02      inference(subtyping,[status(esa)],[c_789]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_10975,plain,
% 11.63/2.02      ( ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | r1_tarski(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK0(k1_yellow19(sK4,sK5),sK6)) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2187]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_9,plain,
% 11.63/2.02      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 11.63/2.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.63/2.02      | ~ v2_pre_topc(X0)
% 11.63/2.02      | ~ l1_pre_topc(X0) ),
% 11.63/2.02      inference(cnf_transformation,[],[f72]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_33,negated_conjecture,
% 11.63/2.02      ( v2_pre_topc(sK4) ),
% 11.63/2.02      inference(cnf_transformation,[],[f92]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_744,plain,
% 11.63/2.02      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 11.63/2.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.63/2.02      | ~ l1_pre_topc(X0)
% 11.63/2.02      | sK4 != X0 ),
% 11.63/2.02      inference(resolution_lifted,[status(thm)],[c_9,c_33]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_745,plain,
% 11.63/2.02      ( v3_pre_topc(k1_tops_1(sK4,X0),sK4)
% 11.63/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ l1_pre_topc(sK4) ),
% 11.63/2.02      inference(unflattening,[status(thm)],[c_744]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_749,plain,
% 11.63/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | v3_pre_topc(k1_tops_1(sK4,X0),sK4) ),
% 11.63/2.02      inference(global_propositional_subsumption,
% 11.63/2.02                [status(thm)],
% 11.63/2.02                [c_745,c_32]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_750,plain,
% 11.63/2.02      ( v3_pre_topc(k1_tops_1(sK4,X0),sK4)
% 11.63/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 11.63/2.02      inference(renaming,[status(thm)],[c_749]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2189,plain,
% 11.63/2.02      ( v3_pre_topc(k1_tops_1(sK4,X0_53),sK4)
% 11.63/2.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 11.63/2.02      inference(subtyping,[status(esa)],[c_750]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_10726,plain,
% 11.63/2.02      ( v3_pre_topc(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK4)
% 11.63/2.02      | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2189]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_8,plain,
% 11.63/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.63/2.02      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.63/2.02      | ~ l1_pre_topc(X1) ),
% 11.63/2.02      inference(cnf_transformation,[],[f71]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_800,plain,
% 11.63/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.63/2.02      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.63/2.02      | sK4 != X1 ),
% 11.63/2.02      inference(resolution_lifted,[status(thm)],[c_8,c_32]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_801,plain,
% 11.63/2.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | m1_subset_1(k1_tops_1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 11.63/2.02      inference(unflattening,[status(thm)],[c_800]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2186,plain,
% 11.63/2.02      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | m1_subset_1(k1_tops_1(sK4,X0_53),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 11.63/2.02      inference(subtyping,[status(esa)],[c_801]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_10166,plain,
% 11.63/2.02      ( m1_subset_1(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2186]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2212,plain,( X0_53 = X0_53 ),theory(equality) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_8164,plain,
% 11.63/2.02      ( sK0(k1_yellow19(sK4,sK5),sK6) = sK0(k1_yellow19(sK4,sK5),sK6) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2212]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_19,plain,
% 11.63/2.02      ( ~ r2_waybel_7(X0,X1,X2)
% 11.63/2.02      | ~ v3_pre_topc(X3,X0)
% 11.63/2.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 11.63/2.02      | ~ r2_hidden(X2,X3)
% 11.63/2.02      | r2_hidden(X3,X1)
% 11.63/2.02      | ~ v2_pre_topc(X0)
% 11.63/2.02      | ~ l1_pre_topc(X0) ),
% 11.63/2.02      inference(cnf_transformation,[],[f79]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_649,plain,
% 11.63/2.02      ( ~ r2_waybel_7(X0,X1,X2)
% 11.63/2.02      | ~ v3_pre_topc(X3,X0)
% 11.63/2.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 11.63/2.02      | ~ r2_hidden(X2,X3)
% 11.63/2.02      | r2_hidden(X3,X1)
% 11.63/2.02      | ~ l1_pre_topc(X0)
% 11.63/2.02      | sK4 != X0 ),
% 11.63/2.02      inference(resolution_lifted,[status(thm)],[c_19,c_33]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_650,plain,
% 11.63/2.02      ( ~ r2_waybel_7(sK4,X0,X1)
% 11.63/2.02      | ~ v3_pre_topc(X2,sK4)
% 11.63/2.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ r2_hidden(X1,X2)
% 11.63/2.02      | r2_hidden(X2,X0)
% 11.63/2.02      | ~ l1_pre_topc(sK4) ),
% 11.63/2.02      inference(unflattening,[status(thm)],[c_649]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_652,plain,
% 11.63/2.02      ( r2_hidden(X2,X0)
% 11.63/2.02      | ~ r2_hidden(X1,X2)
% 11.63/2.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ v3_pre_topc(X2,sK4)
% 11.63/2.02      | ~ r2_waybel_7(sK4,X0,X1) ),
% 11.63/2.02      inference(global_propositional_subsumption,
% 11.63/2.02                [status(thm)],
% 11.63/2.02                [c_650,c_32]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_653,plain,
% 11.63/2.02      ( ~ r2_waybel_7(sK4,X0,X1)
% 11.63/2.02      | ~ v3_pre_topc(X2,sK4)
% 11.63/2.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ r2_hidden(X1,X2)
% 11.63/2.02      | r2_hidden(X2,X0) ),
% 11.63/2.02      inference(renaming,[status(thm)],[c_652]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2194,plain,
% 11.63/2.02      ( ~ r2_waybel_7(sK4,X0_53,X1_53)
% 11.63/2.02      | ~ v3_pre_topc(X2_53,sK4)
% 11.63/2.02      | ~ m1_subset_1(X2_53,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ r2_hidden(X1_53,X2_53)
% 11.63/2.02      | r2_hidden(X2_53,X0_53) ),
% 11.63/2.02      inference(subtyping,[status(esa)],[c_653]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_3734,plain,
% 11.63/2.02      ( ~ r2_waybel_7(sK4,X0_53,X1_53)
% 11.63/2.02      | ~ v3_pre_topc(k1_tops_1(sK4,X2_53),sK4)
% 11.63/2.02      | ~ m1_subset_1(k1_tops_1(sK4,X2_53),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ r2_hidden(X1_53,k1_tops_1(sK4,X2_53))
% 11.63/2.02      | r2_hidden(k1_tops_1(sK4,X2_53),X0_53) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2194]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_4736,plain,
% 11.63/2.02      ( ~ r2_waybel_7(sK4,X0_53,sK5)
% 11.63/2.02      | ~ v3_pre_topc(k1_tops_1(sK4,X1_53),sK4)
% 11.63/2.02      | ~ m1_subset_1(k1_tops_1(sK4,X1_53),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | r2_hidden(k1_tops_1(sK4,X1_53),X0_53)
% 11.63/2.02      | ~ r2_hidden(sK5,k1_tops_1(sK4,X1_53)) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_3734]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_7740,plain,
% 11.63/2.02      ( ~ r2_waybel_7(sK4,X0_53,sK5)
% 11.63/2.02      | ~ v3_pre_topc(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK4)
% 11.63/2.02      | ~ m1_subset_1(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),X0_53)
% 11.63/2.02      | ~ r2_hidden(sK5,k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6))) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_4736]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_7742,plain,
% 11.63/2.02      ( ~ r2_waybel_7(sK4,sK6,sK5)
% 11.63/2.02      | ~ v3_pre_topc(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK4)
% 11.63/2.02      | ~ m1_subset_1(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | r2_hidden(k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6)),sK6)
% 11.63/2.02      | ~ r2_hidden(sK5,k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6))) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_7740]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_28,negated_conjecture,
% 11.63/2.02      ( r2_waybel_7(sK4,sK6,sK5) | r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
% 11.63/2.02      inference(cnf_transformation,[],[f97]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2198,negated_conjecture,
% 11.63/2.02      ( r2_waybel_7(sK4,sK6,sK5) | r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
% 11.63/2.02      inference(subtyping,[status(esa)],[c_28]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_3009,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
% 11.63/2.02      | r1_tarski(k1_yellow19(sK4,sK5),sK6) = iProver_top ),
% 11.63/2.02      inference(predicate_to_equality,[status(thm)],[c_2198]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_1,plain,
% 11.63/2.02      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.63/2.02      inference(cnf_transformation,[],[f64]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2209,plain,
% 11.63/2.02      ( r2_hidden(sK0(X0_53,X1_53),X0_53) | r1_tarski(X0_53,X1_53) ),
% 11.63/2.02      inference(subtyping,[status(esa)],[c_1]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2998,plain,
% 11.63/2.02      ( r2_hidden(sK0(X0_53,X1_53),X0_53) = iProver_top
% 11.63/2.02      | r1_tarski(X0_53,X1_53) = iProver_top ),
% 11.63/2.02      inference(predicate_to_equality,[status(thm)],[c_2209]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2,plain,
% 11.63/2.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 11.63/2.02      inference(cnf_transformation,[],[f63]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2208,plain,
% 11.63/2.02      ( ~ r2_hidden(X0_53,X1_53)
% 11.63/2.02      | r2_hidden(X0_53,X2_53)
% 11.63/2.02      | ~ r1_tarski(X1_53,X2_53) ),
% 11.63/2.02      inference(subtyping,[status(esa)],[c_2]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2999,plain,
% 11.63/2.02      ( r2_hidden(X0_53,X1_53) != iProver_top
% 11.63/2.02      | r2_hidden(X0_53,X2_53) = iProver_top
% 11.63/2.02      | r1_tarski(X1_53,X2_53) != iProver_top ),
% 11.63/2.02      inference(predicate_to_equality,[status(thm)],[c_2208]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_3433,plain,
% 11.63/2.02      ( r2_hidden(sK0(X0_53,X1_53),X2_53) = iProver_top
% 11.63/2.02      | r1_tarski(X0_53,X2_53) != iProver_top
% 11.63/2.02      | r1_tarski(X0_53,X1_53) = iProver_top ),
% 11.63/2.02      inference(superposition,[status(thm)],[c_2998,c_2999]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_5262,plain,
% 11.63/2.02      ( r2_hidden(sK0(X0_53,X1_53),X2_53) = iProver_top
% 11.63/2.02      | r1_tarski(X0_53,X3_53) != iProver_top
% 11.63/2.02      | r1_tarski(X3_53,X2_53) != iProver_top
% 11.63/2.02      | r1_tarski(X0_53,X1_53) = iProver_top ),
% 11.63/2.02      inference(superposition,[status(thm)],[c_3433,c_2999]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_7280,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
% 11.63/2.02      | r2_hidden(sK0(k1_yellow19(sK4,sK5),X0_53),X1_53) = iProver_top
% 11.63/2.02      | r1_tarski(k1_yellow19(sK4,sK5),X0_53) = iProver_top
% 11.63/2.02      | r1_tarski(sK6,X1_53) != iProver_top ),
% 11.63/2.02      inference(superposition,[status(thm)],[c_3009,c_5262]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_41,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
% 11.63/2.02      | r1_tarski(k1_yellow19(sK4,sK5),sK6) = iProver_top ),
% 11.63/2.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_17,plain,
% 11.63/2.02      ( r2_waybel_7(X0,X1,X2)
% 11.63/2.02      | v3_pre_topc(sK1(X0,X1,X2),X0)
% 11.63/2.02      | ~ v2_pre_topc(X0)
% 11.63/2.02      | ~ l1_pre_topc(X0) ),
% 11.63/2.02      inference(cnf_transformation,[],[f81]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_690,plain,
% 11.63/2.02      ( r2_waybel_7(X0,X1,X2)
% 11.63/2.02      | v3_pre_topc(sK1(X0,X1,X2),X0)
% 11.63/2.02      | ~ l1_pre_topc(X0)
% 11.63/2.02      | sK4 != X0 ),
% 11.63/2.02      inference(resolution_lifted,[status(thm)],[c_17,c_33]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_691,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,X0,X1)
% 11.63/2.02      | v3_pre_topc(sK1(sK4,X0,X1),sK4)
% 11.63/2.02      | ~ l1_pre_topc(sK4) ),
% 11.63/2.02      inference(unflattening,[status(thm)],[c_690]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_695,plain,
% 11.63/2.02      ( v3_pre_topc(sK1(sK4,X0,X1),sK4) | r2_waybel_7(sK4,X0,X1) ),
% 11.63/2.02      inference(global_propositional_subsumption,
% 11.63/2.02                [status(thm)],
% 11.63/2.02                [c_691,c_32]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_696,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,X0,X1) | v3_pre_topc(sK1(sK4,X0,X1),sK4) ),
% 11.63/2.02      inference(renaming,[status(thm)],[c_695]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2192,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,X0_53,X1_53)
% 11.63/2.02      | v3_pre_topc(sK1(sK4,X0_53,X1_53),sK4) ),
% 11.63/2.02      inference(subtyping,[status(esa)],[c_696]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_3373,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,sK6,sK5) | v3_pre_topc(sK1(sK4,sK6,sK5),sK4) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2192]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_3374,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
% 11.63/2.02      | v3_pre_topc(sK1(sK4,sK6,sK5),sK4) = iProver_top ),
% 11.63/2.02      inference(predicate_to_equality,[status(thm)],[c_3373]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_18,plain,
% 11.63/2.02      ( r2_waybel_7(X0,X1,X2)
% 11.63/2.02      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 11.63/2.02      | ~ v2_pre_topc(X0)
% 11.63/2.02      | ~ l1_pre_topc(X0) ),
% 11.63/2.02      inference(cnf_transformation,[],[f80]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_672,plain,
% 11.63/2.02      ( r2_waybel_7(X0,X1,X2)
% 11.63/2.02      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 11.63/2.02      | ~ l1_pre_topc(X0)
% 11.63/2.02      | sK4 != X0 ),
% 11.63/2.02      inference(resolution_lifted,[status(thm)],[c_18,c_33]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_673,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,X0,X1)
% 11.63/2.02      | m1_subset_1(sK1(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ l1_pre_topc(sK4) ),
% 11.63/2.02      inference(unflattening,[status(thm)],[c_672]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_677,plain,
% 11.63/2.02      ( m1_subset_1(sK1(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | r2_waybel_7(sK4,X0,X1) ),
% 11.63/2.02      inference(global_propositional_subsumption,
% 11.63/2.02                [status(thm)],
% 11.63/2.02                [c_673,c_32]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_678,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,X0,X1)
% 11.63/2.02      | m1_subset_1(sK1(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 11.63/2.02      inference(renaming,[status(thm)],[c_677]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2193,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,X0_53,X1_53)
% 11.63/2.02      | m1_subset_1(sK1(sK4,X0_53,X1_53),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 11.63/2.02      inference(subtyping,[status(esa)],[c_678]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_3372,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,sK6,sK5)
% 11.63/2.02      | m1_subset_1(sK1(sK4,sK6,sK5),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2193]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_3376,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
% 11.63/2.02      | m1_subset_1(sK1(sK4,sK6,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 11.63/2.02      inference(predicate_to_equality,[status(thm)],[c_3372]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_15,plain,
% 11.63/2.02      ( r2_waybel_7(X0,X1,X2)
% 11.63/2.02      | ~ r2_hidden(sK1(X0,X1,X2),X1)
% 11.63/2.02      | ~ v2_pre_topc(X0)
% 11.63/2.02      | ~ l1_pre_topc(X0) ),
% 11.63/2.02      inference(cnf_transformation,[],[f83]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_726,plain,
% 11.63/2.02      ( r2_waybel_7(X0,X1,X2)
% 11.63/2.02      | ~ r2_hidden(sK1(X0,X1,X2),X1)
% 11.63/2.02      | ~ l1_pre_topc(X0)
% 11.63/2.02      | sK4 != X0 ),
% 11.63/2.02      inference(resolution_lifted,[status(thm)],[c_15,c_33]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_727,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,X0,X1)
% 11.63/2.02      | ~ r2_hidden(sK1(sK4,X0,X1),X0)
% 11.63/2.02      | ~ l1_pre_topc(sK4) ),
% 11.63/2.02      inference(unflattening,[status(thm)],[c_726]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_731,plain,
% 11.63/2.02      ( ~ r2_hidden(sK1(sK4,X0,X1),X0) | r2_waybel_7(sK4,X0,X1) ),
% 11.63/2.02      inference(global_propositional_subsumption,
% 11.63/2.02                [status(thm)],
% 11.63/2.02                [c_727,c_32]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_732,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,X0,X1) | ~ r2_hidden(sK1(sK4,X0,X1),X0) ),
% 11.63/2.02      inference(renaming,[status(thm)],[c_731]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2190,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,X0_53,X1_53)
% 11.63/2.02      | ~ r2_hidden(sK1(sK4,X0_53,X1_53),X0_53) ),
% 11.63/2.02      inference(subtyping,[status(esa)],[c_732]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_3371,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,sK6,sK5) | ~ r2_hidden(sK1(sK4,sK6,sK5),sK6) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2190]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_3378,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
% 11.63/2.02      | r2_hidden(sK1(sK4,sK6,sK5),sK6) != iProver_top ),
% 11.63/2.02      inference(predicate_to_equality,[status(thm)],[c_3371]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_16,plain,
% 11.63/2.02      ( r2_waybel_7(X0,X1,X2)
% 11.63/2.02      | r2_hidden(X2,sK1(X0,X1,X2))
% 11.63/2.02      | ~ v2_pre_topc(X0)
% 11.63/2.02      | ~ l1_pre_topc(X0) ),
% 11.63/2.02      inference(cnf_transformation,[],[f82]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_708,plain,
% 11.63/2.02      ( r2_waybel_7(X0,X1,X2)
% 11.63/2.02      | r2_hidden(X2,sK1(X0,X1,X2))
% 11.63/2.02      | ~ l1_pre_topc(X0)
% 11.63/2.02      | sK4 != X0 ),
% 11.63/2.02      inference(resolution_lifted,[status(thm)],[c_16,c_33]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_709,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,X0,X1)
% 11.63/2.02      | r2_hidden(X1,sK1(sK4,X0,X1))
% 11.63/2.02      | ~ l1_pre_topc(sK4) ),
% 11.63/2.02      inference(unflattening,[status(thm)],[c_708]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_713,plain,
% 11.63/2.02      ( r2_hidden(X1,sK1(sK4,X0,X1)) | r2_waybel_7(sK4,X0,X1) ),
% 11.63/2.02      inference(global_propositional_subsumption,
% 11.63/2.02                [status(thm)],
% 11.63/2.02                [c_709,c_32]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_714,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,X0,X1) | r2_hidden(X1,sK1(sK4,X0,X1)) ),
% 11.63/2.02      inference(renaming,[status(thm)],[c_713]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2191,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,X0_53,X1_53)
% 11.63/2.02      | r2_hidden(X1_53,sK1(sK4,X0_53,X1_53)) ),
% 11.63/2.02      inference(subtyping,[status(esa)],[c_714]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_3370,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,sK6,sK5) | r2_hidden(sK5,sK1(sK4,sK6,sK5)) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2191]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_3380,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,sK6,sK5) = iProver_top
% 11.63/2.02      | r2_hidden(sK5,sK1(sK4,sK6,sK5)) = iProver_top ),
% 11.63/2.02      inference(predicate_to_equality,[status(thm)],[c_3370]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_14,plain,
% 11.63/2.02      ( m1_connsp_2(X0,X1,X2)
% 11.63/2.02      | ~ v3_pre_topc(X0,X1)
% 11.63/2.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.63/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.63/2.02      | ~ r2_hidden(X2,X0)
% 11.63/2.02      | v2_struct_0(X1)
% 11.63/2.02      | ~ v2_pre_topc(X1)
% 11.63/2.02      | ~ l1_pre_topc(X1) ),
% 11.63/2.02      inference(cnf_transformation,[],[f77]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_34,negated_conjecture,
% 11.63/2.02      ( ~ v2_struct_0(sK4) ),
% 11.63/2.02      inference(cnf_transformation,[],[f91]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_549,plain,
% 11.63/2.02      ( m1_connsp_2(X0,X1,X2)
% 11.63/2.02      | ~ v3_pre_topc(X0,X1)
% 11.63/2.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.63/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.63/2.02      | ~ r2_hidden(X2,X0)
% 11.63/2.02      | ~ v2_pre_topc(X1)
% 11.63/2.02      | ~ l1_pre_topc(X1)
% 11.63/2.02      | sK4 != X1 ),
% 11.63/2.02      inference(resolution_lifted,[status(thm)],[c_14,c_34]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_550,plain,
% 11.63/2.02      ( m1_connsp_2(X0,sK4,X1)
% 11.63/2.02      | ~ v3_pre_topc(X0,sK4)
% 11.63/2.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 11.63/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ r2_hidden(X1,X0)
% 11.63/2.02      | ~ v2_pre_topc(sK4)
% 11.63/2.02      | ~ l1_pre_topc(sK4) ),
% 11.63/2.02      inference(unflattening,[status(thm)],[c_549]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_554,plain,
% 11.63/2.02      ( m1_connsp_2(X0,sK4,X1)
% 11.63/2.02      | ~ v3_pre_topc(X0,sK4)
% 11.63/2.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 11.63/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ r2_hidden(X1,X0) ),
% 11.63/2.02      inference(global_propositional_subsumption,
% 11.63/2.02                [status(thm)],
% 11.63/2.02                [c_550,c_33,c_32]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_5,plain,
% 11.63/2.02      ( m1_subset_1(X0,X1)
% 11.63/2.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.63/2.02      | ~ r2_hidden(X0,X2) ),
% 11.63/2.02      inference(cnf_transformation,[],[f68]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_570,plain,
% 11.63/2.02      ( m1_connsp_2(X0,sK4,X1)
% 11.63/2.02      | ~ v3_pre_topc(X0,sK4)
% 11.63/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ r2_hidden(X1,X0) ),
% 11.63/2.02      inference(forward_subsumption_resolution,[status(thm)],[c_554,c_5]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_25,plain,
% 11.63/2.02      ( ~ m1_connsp_2(X0,X1,X2)
% 11.63/2.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.63/2.02      | r2_hidden(X0,k1_yellow19(X1,X2))
% 11.63/2.02      | v2_struct_0(X1)
% 11.63/2.02      | ~ v2_pre_topc(X1)
% 11.63/2.02      | ~ l1_pre_topc(X1) ),
% 11.63/2.02      inference(cnf_transformation,[],[f90]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_528,plain,
% 11.63/2.02      ( ~ m1_connsp_2(X0,X1,X2)
% 11.63/2.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.63/2.02      | r2_hidden(X0,k1_yellow19(X1,X2))
% 11.63/2.02      | ~ v2_pre_topc(X1)
% 11.63/2.02      | ~ l1_pre_topc(X1)
% 11.63/2.02      | sK4 != X1 ),
% 11.63/2.02      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_529,plain,
% 11.63/2.02      ( ~ m1_connsp_2(X0,sK4,X1)
% 11.63/2.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 11.63/2.02      | r2_hidden(X0,k1_yellow19(sK4,X1))
% 11.63/2.02      | ~ v2_pre_topc(sK4)
% 11.63/2.02      | ~ l1_pre_topc(sK4) ),
% 11.63/2.02      inference(unflattening,[status(thm)],[c_528]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_533,plain,
% 11.63/2.02      ( ~ m1_connsp_2(X0,sK4,X1)
% 11.63/2.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 11.63/2.02      | r2_hidden(X0,k1_yellow19(sK4,X1)) ),
% 11.63/2.02      inference(global_propositional_subsumption,
% 11.63/2.02                [status(thm)],
% 11.63/2.02                [c_529,c_33,c_32]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_1240,plain,
% 11.63/2.02      ( ~ v3_pre_topc(X0,sK4)
% 11.63/2.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 11.63/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ r2_hidden(X1,X0)
% 11.63/2.02      | r2_hidden(X0,k1_yellow19(sK4,X1)) ),
% 11.63/2.02      inference(resolution,[status(thm)],[c_570,c_533]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_1254,plain,
% 11.63/2.02      ( ~ v3_pre_topc(X0,sK4)
% 11.63/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ r2_hidden(X1,X0)
% 11.63/2.02      | r2_hidden(X0,k1_yellow19(sK4,X1)) ),
% 11.63/2.02      inference(forward_subsumption_resolution,
% 11.63/2.02                [status(thm)],
% 11.63/2.02                [c_1240,c_5]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2184,plain,
% 11.63/2.02      ( ~ v3_pre_topc(X0_53,sK4)
% 11.63/2.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ r2_hidden(X1_53,X0_53)
% 11.63/2.02      | r2_hidden(X0_53,k1_yellow19(sK4,X1_53)) ),
% 11.63/2.02      inference(subtyping,[status(esa)],[c_1254]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_4176,plain,
% 11.63/2.02      ( ~ v3_pre_topc(sK1(sK4,sK6,sK5),sK4)
% 11.63/2.02      | ~ m1_subset_1(sK1(sK4,sK6,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ r2_hidden(X0_53,sK1(sK4,sK6,sK5))
% 11.63/2.02      | r2_hidden(sK1(sK4,sK6,sK5),k1_yellow19(sK4,X0_53)) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2184]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_4322,plain,
% 11.63/2.02      ( ~ v3_pre_topc(sK1(sK4,sK6,sK5),sK4)
% 11.63/2.02      | ~ m1_subset_1(sK1(sK4,sK6,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | r2_hidden(sK1(sK4,sK6,sK5),k1_yellow19(sK4,sK5))
% 11.63/2.02      | ~ r2_hidden(sK5,sK1(sK4,sK6,sK5)) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_4176]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_4323,plain,
% 11.63/2.02      ( v3_pre_topc(sK1(sK4,sK6,sK5),sK4) != iProver_top
% 11.63/2.02      | m1_subset_1(sK1(sK4,sK6,sK5),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 11.63/2.02      | r2_hidden(sK1(sK4,sK6,sK5),k1_yellow19(sK4,sK5)) = iProver_top
% 11.63/2.02      | r2_hidden(sK5,sK1(sK4,sK6,sK5)) != iProver_top ),
% 11.63/2.02      inference(predicate_to_equality,[status(thm)],[c_4322]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_5473,plain,
% 11.63/2.02      ( r2_hidden(sK1(sK4,sK6,sK5),X0_53)
% 11.63/2.02      | ~ r2_hidden(sK1(sK4,sK6,sK5),k1_yellow19(sK4,sK5))
% 11.63/2.02      | ~ r1_tarski(k1_yellow19(sK4,sK5),X0_53) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2208]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_5474,plain,
% 11.63/2.02      ( r2_hidden(sK1(sK4,sK6,sK5),X0_53) = iProver_top
% 11.63/2.02      | r2_hidden(sK1(sK4,sK6,sK5),k1_yellow19(sK4,sK5)) != iProver_top
% 11.63/2.02      | r1_tarski(k1_yellow19(sK4,sK5),X0_53) != iProver_top ),
% 11.63/2.02      inference(predicate_to_equality,[status(thm)],[c_5473]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_5476,plain,
% 11.63/2.02      ( r2_hidden(sK1(sK4,sK6,sK5),k1_yellow19(sK4,sK5)) != iProver_top
% 11.63/2.02      | r2_hidden(sK1(sK4,sK6,sK5),sK6) = iProver_top
% 11.63/2.02      | r1_tarski(k1_yellow19(sK4,sK5),sK6) != iProver_top ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_5474]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_7488,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,sK6,sK5) = iProver_top ),
% 11.63/2.02      inference(global_propositional_subsumption,
% 11.63/2.02                [status(thm)],
% 11.63/2.02                [c_7280,c_41,c_3374,c_3376,c_3378,c_3380,c_4323,c_5476]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_7490,plain,
% 11.63/2.02      ( r2_waybel_7(sK4,sK6,sK5) ),
% 11.63/2.02      inference(predicate_to_equality_rev,[status(thm)],[c_7488]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2215,plain,
% 11.63/2.02      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 11.63/2.02      theory(equality) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_3632,plain,
% 11.63/2.02      ( X0_53 != X1_53
% 11.63/2.02      | X0_53 = u1_struct_0(sK4)
% 11.63/2.02      | u1_struct_0(sK4) != X1_53 ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2215]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_5046,plain,
% 11.63/2.02      ( X0_53 = u1_struct_0(sK4)
% 11.63/2.02      | X0_53 != k2_struct_0(sK4)
% 11.63/2.02      | u1_struct_0(sK4) != k2_struct_0(sK4) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_3632]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_5779,plain,
% 11.63/2.02      ( u1_struct_0(sK4) != k2_struct_0(sK4)
% 11.63/2.02      | k2_struct_0(sK4) = u1_struct_0(sK4)
% 11.63/2.02      | k2_struct_0(sK4) != k2_struct_0(sK4) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_5046]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_26,plain,
% 11.63/2.02      ( m1_connsp_2(X0,X1,X2)
% 11.63/2.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.63/2.02      | ~ r2_hidden(X0,k1_yellow19(X1,X2))
% 11.63/2.02      | v2_struct_0(X1)
% 11.63/2.02      | ~ v2_pre_topc(X1)
% 11.63/2.02      | ~ l1_pre_topc(X1) ),
% 11.63/2.02      inference(cnf_transformation,[],[f89]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_507,plain,
% 11.63/2.02      ( m1_connsp_2(X0,X1,X2)
% 11.63/2.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.63/2.02      | ~ r2_hidden(X0,k1_yellow19(X1,X2))
% 11.63/2.02      | ~ v2_pre_topc(X1)
% 11.63/2.02      | ~ l1_pre_topc(X1)
% 11.63/2.02      | sK4 != X1 ),
% 11.63/2.02      inference(resolution_lifted,[status(thm)],[c_26,c_34]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_508,plain,
% 11.63/2.02      ( m1_connsp_2(X0,sK4,X1)
% 11.63/2.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 11.63/2.02      | ~ r2_hidden(X0,k1_yellow19(sK4,X1))
% 11.63/2.02      | ~ v2_pre_topc(sK4)
% 11.63/2.02      | ~ l1_pre_topc(sK4) ),
% 11.63/2.02      inference(unflattening,[status(thm)],[c_507]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_512,plain,
% 11.63/2.02      ( m1_connsp_2(X0,sK4,X1)
% 11.63/2.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 11.63/2.02      | ~ r2_hidden(X0,k1_yellow19(sK4,X1)) ),
% 11.63/2.02      inference(global_propositional_subsumption,
% 11.63/2.02                [status(thm)],
% 11.63/2.02                [c_508,c_33,c_32]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_12,plain,
% 11.63/2.02      ( ~ m1_connsp_2(X0,X1,X2)
% 11.63/2.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.63/2.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.63/2.02      | r2_hidden(X2,k1_tops_1(X1,X0))
% 11.63/2.02      | v2_struct_0(X1)
% 11.63/2.02      | ~ v2_pre_topc(X1)
% 11.63/2.02      | ~ l1_pre_topc(X1) ),
% 11.63/2.02      inference(cnf_transformation,[],[f74]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_13,plain,
% 11.63/2.02      ( ~ m1_connsp_2(X0,X1,X2)
% 11.63/2.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.63/2.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.63/2.02      | v2_struct_0(X1)
% 11.63/2.02      | ~ v2_pre_topc(X1)
% 11.63/2.02      | ~ l1_pre_topc(X1) ),
% 11.63/2.02      inference(cnf_transformation,[],[f76]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_211,plain,
% 11.63/2.02      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.63/2.02      | ~ m1_connsp_2(X0,X1,X2)
% 11.63/2.02      | r2_hidden(X2,k1_tops_1(X1,X0))
% 11.63/2.02      | v2_struct_0(X1)
% 11.63/2.02      | ~ v2_pre_topc(X1)
% 11.63/2.02      | ~ l1_pre_topc(X1) ),
% 11.63/2.02      inference(global_propositional_subsumption,
% 11.63/2.02                [status(thm)],
% 11.63/2.02                [c_12,c_13]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_212,plain,
% 11.63/2.02      ( ~ m1_connsp_2(X0,X1,X2)
% 11.63/2.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.63/2.02      | r2_hidden(X2,k1_tops_1(X1,X0))
% 11.63/2.02      | v2_struct_0(X1)
% 11.63/2.02      | ~ v2_pre_topc(X1)
% 11.63/2.02      | ~ l1_pre_topc(X1) ),
% 11.63/2.02      inference(renaming,[status(thm)],[c_211]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_486,plain,
% 11.63/2.02      ( ~ m1_connsp_2(X0,X1,X2)
% 11.63/2.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.63/2.02      | r2_hidden(X2,k1_tops_1(X1,X0))
% 11.63/2.02      | ~ v2_pre_topc(X1)
% 11.63/2.02      | ~ l1_pre_topc(X1)
% 11.63/2.02      | sK4 != X1 ),
% 11.63/2.02      inference(resolution_lifted,[status(thm)],[c_212,c_34]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_487,plain,
% 11.63/2.02      ( ~ m1_connsp_2(X0,sK4,X1)
% 11.63/2.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 11.63/2.02      | r2_hidden(X1,k1_tops_1(sK4,X0))
% 11.63/2.02      | ~ v2_pre_topc(sK4)
% 11.63/2.02      | ~ l1_pre_topc(sK4) ),
% 11.63/2.02      inference(unflattening,[status(thm)],[c_486]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_491,plain,
% 11.63/2.02      ( ~ m1_connsp_2(X0,sK4,X1)
% 11.63/2.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 11.63/2.02      | r2_hidden(X1,k1_tops_1(sK4,X0)) ),
% 11.63/2.02      inference(global_propositional_subsumption,
% 11.63/2.02                [status(thm)],
% 11.63/2.02                [c_487,c_33,c_32]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_1299,plain,
% 11.63/2.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 11.63/2.02      | ~ r2_hidden(X1,k1_yellow19(sK4,X0))
% 11.63/2.02      | r2_hidden(X0,k1_tops_1(sK4,X1)) ),
% 11.63/2.02      inference(resolution,[status(thm)],[c_512,c_491]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2181,plain,
% 11.63/2.02      ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 11.63/2.02      | ~ r2_hidden(X1_53,k1_yellow19(sK4,X0_53))
% 11.63/2.02      | r2_hidden(X0_53,k1_tops_1(sK4,X1_53)) ),
% 11.63/2.02      inference(subtyping,[status(esa)],[c_1299]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_3281,plain,
% 11.63/2.02      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 11.63/2.02      | ~ r2_hidden(X0_53,k1_yellow19(sK4,sK5))
% 11.63/2.02      | r2_hidden(sK5,k1_tops_1(sK4,X0_53)) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2181]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_3561,plain,
% 11.63/2.02      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 11.63/2.02      | ~ r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),k1_yellow19(sK4,sK5))
% 11.63/2.02      | r2_hidden(sK5,k1_tops_1(sK4,sK0(k1_yellow19(sK4,sK5),sK6))) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_3281]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_578,plain,
% 11.63/2.02      ( ~ m1_connsp_2(X0,X1,X2)
% 11.63/2.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.63/2.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.63/2.02      | ~ v2_pre_topc(X1)
% 11.63/2.02      | ~ l1_pre_topc(X1)
% 11.63/2.02      | sK4 != X1 ),
% 11.63/2.02      inference(resolution_lifted,[status(thm)],[c_13,c_34]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_579,plain,
% 11.63/2.02      ( ~ m1_connsp_2(X0,sK4,X1)
% 11.63/2.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 11.63/2.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ v2_pre_topc(sK4)
% 11.63/2.02      | ~ l1_pre_topc(sK4) ),
% 11.63/2.02      inference(unflattening,[status(thm)],[c_578]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_583,plain,
% 11.63/2.02      ( ~ m1_connsp_2(X0,sK4,X1)
% 11.63/2.02      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 11.63/2.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 11.63/2.02      inference(global_propositional_subsumption,
% 11.63/2.02                [status(thm)],
% 11.63/2.02                [c_579,c_33,c_32]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_1284,plain,
% 11.63/2.02      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 11.63/2.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ r2_hidden(X1,k1_yellow19(sK4,X0)) ),
% 11.63/2.02      inference(resolution,[status(thm)],[c_512,c_583]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2182,plain,
% 11.63/2.02      ( ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 11.63/2.02      | m1_subset_1(X1_53,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ r2_hidden(X1_53,k1_yellow19(sK4,X0_53)) ),
% 11.63/2.02      inference(subtyping,[status(esa)],[c_1284]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_3276,plain,
% 11.63/2.02      ( m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 11.63/2.02      | ~ r2_hidden(X0_53,k1_yellow19(sK4,sK5)) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2182]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_3562,plain,
% 11.63/2.02      ( m1_subset_1(sK0(k1_yellow19(sK4,sK5),sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 11.63/2.02      | ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 11.63/2.02      | ~ r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),k1_yellow19(sK4,sK5)) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_3276]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_0,plain,
% 11.63/2.02      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.63/2.02      inference(cnf_transformation,[],[f65]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2210,plain,
% 11.63/2.02      ( ~ r2_hidden(sK0(X0_53,X1_53),X1_53) | r1_tarski(X0_53,X1_53) ),
% 11.63/2.02      inference(subtyping,[status(esa)],[c_0]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_3307,plain,
% 11.63/2.02      ( ~ r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),sK6)
% 11.63/2.02      | r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2210]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_3304,plain,
% 11.63/2.02      ( r2_hidden(sK0(k1_yellow19(sK4,sK5),sK6),k1_yellow19(sK4,sK5))
% 11.63/2.02      | r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2209]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_7,plain,
% 11.63/2.02      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 11.63/2.02      inference(cnf_transformation,[],[f70]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_6,plain,
% 11.63/2.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 11.63/2.02      inference(cnf_transformation,[],[f69]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_472,plain,
% 11.63/2.02      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 11.63/2.02      inference(resolution,[status(thm)],[c_7,c_6]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_783,plain,
% 11.63/2.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK4 != X0 ),
% 11.63/2.02      inference(resolution_lifted,[status(thm)],[c_472,c_32]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_784,plain,
% 11.63/2.02      ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
% 11.63/2.02      inference(unflattening,[status(thm)],[c_783]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2188,plain,
% 11.63/2.02      ( u1_struct_0(sK4) = k2_struct_0(sK4) ),
% 11.63/2.02      inference(subtyping,[status(esa)],[c_784]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2213,plain,( X0_54 = X0_54 ),theory(equality) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2246,plain,
% 11.63/2.02      ( sK4 = sK4 ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2213]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2220,plain,
% 11.63/2.02      ( X0_54 != X1_54 | k2_struct_0(X0_54) = k2_struct_0(X1_54) ),
% 11.63/2.02      theory(equality) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_2234,plain,
% 11.63/2.02      ( sK4 != sK4 | k2_struct_0(sK4) = k2_struct_0(sK4) ),
% 11.63/2.02      inference(instantiation,[status(thm)],[c_2220]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_27,negated_conjecture,
% 11.63/2.02      ( ~ r2_waybel_7(sK4,sK6,sK5)
% 11.63/2.02      | ~ r1_tarski(k1_yellow19(sK4,sK5),sK6) ),
% 11.63/2.02      inference(cnf_transformation,[],[f98]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_29,negated_conjecture,
% 11.63/2.02      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK4)))))) ),
% 11.63/2.02      inference(cnf_transformation,[],[f104]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_30,negated_conjecture,
% 11.63/2.02      ( v13_waybel_0(sK6,k3_lattice3(k1_lattice3(k2_struct_0(sK4)))) ),
% 11.63/2.02      inference(cnf_transformation,[],[f105]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(c_31,negated_conjecture,
% 11.63/2.02      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 11.63/2.02      inference(cnf_transformation,[],[f94]) ).
% 11.63/2.02  
% 11.63/2.02  cnf(contradiction,plain,
% 11.63/2.02      ( $false ),
% 11.63/2.02      inference(minisat,
% 11.63/2.02                [status(thm)],
% 11.63/2.02                [c_56428,c_53444,c_31018,c_17992,c_10975,c_10726,c_10166,
% 11.63/2.02                 c_8164,c_7742,c_7490,c_5779,c_3561,c_3562,c_3307,c_3304,
% 11.63/2.02                 c_2188,c_2246,c_2234,c_27,c_29,c_30,c_31]) ).
% 11.63/2.02  
% 11.63/2.02  
% 11.63/2.02  % SZS output end CNFRefutation for theBenchmark.p
% 11.63/2.02  
% 11.63/2.02  ------                               Statistics
% 11.63/2.02  
% 11.63/2.02  ------ General
% 11.63/2.02  
% 11.63/2.02  abstr_ref_over_cycles:                  0
% 11.63/2.02  abstr_ref_under_cycles:                 0
% 11.63/2.02  gc_basic_clause_elim:                   0
% 11.63/2.02  forced_gc_time:                         0
% 11.63/2.02  parsing_time:                           0.012
% 11.63/2.02  unif_index_cands_time:                  0.
% 11.63/2.02  unif_index_add_time:                    0.
% 11.63/2.02  orderings_time:                         0.
% 11.63/2.02  out_proof_time:                         0.021
% 11.63/2.02  total_time:                             1.477
% 11.63/2.02  num_of_symbols:                         59
% 11.63/2.02  num_of_terms:                           33943
% 11.63/2.02  
% 11.63/2.02  ------ Preprocessing
% 11.63/2.02  
% 11.63/2.02  num_of_splits:                          0
% 11.63/2.02  num_of_split_atoms:                     0
% 11.63/2.02  num_of_reused_defs:                     0
% 11.63/2.02  num_eq_ax_congr_red:                    34
% 11.63/2.02  num_of_sem_filtered_clauses:            1
% 11.63/2.02  num_of_subtypes:                        3
% 11.63/2.02  monotx_restored_types:                  0
% 11.63/2.02  sat_num_of_epr_types:                   0
% 11.63/2.02  sat_num_of_non_cyclic_types:            0
% 11.63/2.02  sat_guarded_non_collapsed_types:        0
% 11.63/2.02  num_pure_diseq_elim:                    0
% 11.63/2.02  simp_replaced_by:                       0
% 11.63/2.02  res_preprocessed:                       162
% 11.63/2.02  prep_upred:                             0
% 11.63/2.02  prep_unflattend:                        53
% 11.63/2.02  smt_new_axioms:                         0
% 11.63/2.02  pred_elim_cands:                        6
% 11.63/2.02  pred_elim:                              5
% 11.63/2.02  pred_elim_cl:                           5
% 11.63/2.02  pred_elim_cycles:                       12
% 11.63/2.02  merged_defs:                            16
% 11.63/2.02  merged_defs_ncl:                        0
% 11.63/2.02  bin_hyper_res:                          16
% 11.63/2.02  prep_cycles:                            4
% 11.63/2.02  pred_elim_time:                         0.024
% 11.63/2.02  splitting_time:                         0.
% 11.63/2.02  sem_filter_time:                        0.
% 11.63/2.02  monotx_time:                            0.
% 11.63/2.02  subtype_inf_time:                       0.
% 11.63/2.02  
% 11.63/2.02  ------ Problem properties
% 11.63/2.02  
% 11.63/2.02  clauses:                                30
% 11.63/2.02  conjectures:                            5
% 11.63/2.02  epr:                                    1
% 11.63/2.02  horn:                                   22
% 11.63/2.02  ground:                                 6
% 11.63/2.02  unary:                                  4
% 11.63/2.02  binary:                                 13
% 11.63/2.02  lits:                                   77
% 11.63/2.02  lits_eq:                                1
% 11.63/2.02  fd_pure:                                0
% 11.63/2.02  fd_pseudo:                              0
% 11.63/2.02  fd_cond:                                0
% 11.63/2.02  fd_pseudo_cond:                         0
% 11.63/2.02  ac_symbols:                             0
% 11.63/2.02  
% 11.63/2.02  ------ Propositional Solver
% 11.63/2.02  
% 11.63/2.02  prop_solver_calls:                      33
% 11.63/2.02  prop_fast_solver_calls:                 2950
% 11.63/2.02  smt_solver_calls:                       0
% 11.63/2.02  smt_fast_solver_calls:                  0
% 11.63/2.02  prop_num_of_clauses:                    15846
% 11.63/2.02  prop_preprocess_simplified:             28495
% 11.63/2.02  prop_fo_subsumed:                       83
% 11.63/2.02  prop_solver_time:                       0.
% 11.63/2.02  smt_solver_time:                        0.
% 11.63/2.02  smt_fast_solver_time:                   0.
% 11.63/2.02  prop_fast_solver_time:                  0.
% 11.63/2.02  prop_unsat_core_time:                   0.001
% 11.63/2.02  
% 11.63/2.02  ------ QBF
% 11.63/2.02  
% 11.63/2.02  qbf_q_res:                              0
% 11.63/2.02  qbf_num_tautologies:                    0
% 11.63/2.02  qbf_prep_cycles:                        0
% 11.63/2.02  
% 11.63/2.02  ------ BMC1
% 11.63/2.02  
% 11.63/2.02  bmc1_current_bound:                     -1
% 11.63/2.02  bmc1_last_solved_bound:                 -1
% 11.63/2.02  bmc1_unsat_core_size:                   -1
% 11.63/2.02  bmc1_unsat_core_parents_size:           -1
% 11.63/2.02  bmc1_merge_next_fun:                    0
% 11.63/2.02  bmc1_unsat_core_clauses_time:           0.
% 11.63/2.02  
% 11.63/2.02  ------ Instantiation
% 11.63/2.02  
% 11.63/2.02  inst_num_of_clauses:                    3432
% 11.63/2.02  inst_num_in_passive:                    1840
% 11.63/2.02  inst_num_in_active:                     1459
% 11.63/2.02  inst_num_in_unprocessed:                132
% 11.63/2.02  inst_num_of_loops:                      1831
% 11.63/2.02  inst_num_of_learning_restarts:          0
% 11.63/2.02  inst_num_moves_active_passive:          364
% 11.63/2.02  inst_lit_activity:                      0
% 11.63/2.02  inst_lit_activity_moves:                0
% 11.63/2.02  inst_num_tautologies:                   0
% 11.63/2.02  inst_num_prop_implied:                  0
% 11.63/2.02  inst_num_existing_simplified:           0
% 11.63/2.02  inst_num_eq_res_simplified:             0
% 11.63/2.02  inst_num_child_elim:                    0
% 11.63/2.02  inst_num_of_dismatching_blockings:      2490
% 11.63/2.02  inst_num_of_non_proper_insts:           4569
% 11.63/2.02  inst_num_of_duplicates:                 0
% 11.63/2.02  inst_inst_num_from_inst_to_res:         0
% 11.63/2.02  inst_dismatching_checking_time:         0.
% 11.63/2.02  
% 11.63/2.02  ------ Resolution
% 11.63/2.02  
% 11.63/2.02  res_num_of_clauses:                     0
% 11.63/2.02  res_num_in_passive:                     0
% 11.63/2.02  res_num_in_active:                      0
% 11.63/2.02  res_num_of_loops:                       166
% 11.63/2.02  res_forward_subset_subsumed:            177
% 11.63/2.02  res_backward_subset_subsumed:           2
% 11.63/2.02  res_forward_subsumed:                   0
% 11.63/2.02  res_backward_subsumed:                  0
% 11.63/2.02  res_forward_subsumption_resolution:     5
% 11.63/2.02  res_backward_subsumption_resolution:    0
% 11.63/2.02  res_clause_to_clause_subsumption:       18597
% 11.63/2.02  res_orphan_elimination:                 0
% 11.63/2.02  res_tautology_del:                      590
% 11.63/2.02  res_num_eq_res_simplified:              0
% 11.63/2.02  res_num_sel_changes:                    0
% 11.63/2.02  res_moves_from_active_to_pass:          0
% 11.63/2.02  
% 11.63/2.02  ------ Superposition
% 11.63/2.02  
% 11.63/2.02  sup_time_total:                         0.
% 11.63/2.02  sup_time_generating:                    0.
% 11.63/2.02  sup_time_sim_full:                      0.
% 11.63/2.02  sup_time_sim_immed:                     0.
% 11.63/2.02  
% 11.63/2.02  sup_num_of_clauses:                     1781
% 11.63/2.02  sup_num_in_active:                      362
% 11.63/2.02  sup_num_in_passive:                     1419
% 11.63/2.02  sup_num_of_loops:                       366
% 11.63/2.02  sup_fw_superposition:                   1168
% 11.63/2.02  sup_bw_superposition:                   1168
% 11.63/2.02  sup_immediate_simplified:               284
% 11.63/2.02  sup_given_eliminated:                   0
% 11.63/2.02  comparisons_done:                       0
% 11.63/2.02  comparisons_avoided:                    0
% 11.63/2.02  
% 11.63/2.02  ------ Simplifications
% 11.63/2.02  
% 11.63/2.02  
% 11.63/2.02  sim_fw_subset_subsumed:                 102
% 11.63/2.02  sim_bw_subset_subsumed:                 16
% 11.63/2.02  sim_fw_subsumed:                        166
% 11.63/2.02  sim_bw_subsumed:                        18
% 11.63/2.02  sim_fw_subsumption_res:                 20
% 11.63/2.02  sim_bw_subsumption_res:                 0
% 11.63/2.02  sim_tautology_del:                      90
% 11.63/2.02  sim_eq_tautology_del:                   0
% 11.63/2.02  sim_eq_res_simp:                        0
% 11.63/2.02  sim_fw_demodulated:                     0
% 11.63/2.02  sim_bw_demodulated:                     0
% 11.63/2.02  sim_light_normalised:                   11
% 11.63/2.02  sim_joinable_taut:                      0
% 11.63/2.02  sim_joinable_simp:                      0
% 11.63/2.02  sim_ac_normalised:                      0
% 11.63/2.02  sim_smt_subsumption:                    0
% 11.63/2.02  
%------------------------------------------------------------------------------
