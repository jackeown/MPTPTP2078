%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:20 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  194 (1610 expanded)
%              Number of clauses        :  121 ( 314 expanded)
%              Number of leaves         :   15 ( 462 expanded)
%              Depth                    :   29
%              Number of atoms          : 1265 (14574 expanded)
%              Number of equality atoms :  202 ( 497 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   26 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
                <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <~> r2_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <~> r2_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & ( r2_waybel_7(X0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & ( r2_waybel_7(X0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_waybel_7(X0,X1,X2)
            | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
          & ( r2_waybel_7(X0,X1,X2)
            | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r2_waybel_7(X0,X1,sK2)
          | ~ r2_hidden(sK2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
        & ( r2_waybel_7(X0,X1,sK2)
          | r2_hidden(sK2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & ( r2_waybel_7(X0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ( ~ r2_waybel_7(X0,sK1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK1))) )
            & ( r2_waybel_7(X0,sK1,X2)
              | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK1))) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_waybel_7(X0,X1,X2)
                  | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
                & ( r2_waybel_7(X0,X1,X2)
                  | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(sK0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1))) )
              & ( r2_waybel_7(sK0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1))) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r2_waybel_7(sK0,sK1,sK2)
      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    & ( r2_waybel_7(sK0,sK1,sK2)
      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).

fof(f61,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f76,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f61,f46])).

fof(f62,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f62,f46])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f52,f46,f46,f46,f46])).

fof(f60,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f77,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f60,f46])).

fof(f59,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f47,f46,f46,f46])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f50,f46,f46,f46])).

fof(f66,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
                  | ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
                & ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f48,f46,f46,f46])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f55,f46,f46,f46,f46])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f63,f46])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f65,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_19,negated_conjecture,
    ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_18,negated_conjecture,
    ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_9,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_20,negated_conjecture,
    ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_322,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_323,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_21,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_327,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ l1_struct_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_323,c_21])).

cnf(c_328,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_327])).

cnf(c_1279,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_328])).

cnf(c_1672,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1279])).

cnf(c_3,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_494,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_22])).

cnf(c_495,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_2049,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1672,c_495])).

cnf(c_2050,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_2049])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2054,plain,
    ( v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2050,c_24])).

cnf(c_2055,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_2054])).

cnf(c_6,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1207,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_1208,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1207])).

cnf(c_1212,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1208,c_21])).

cnf(c_1213,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1212])).

cnf(c_1733,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1213])).

cnf(c_2022,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1733,c_495])).

cnf(c_2023,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_2022])).

cnf(c_2027,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2023,c_24])).

cnf(c_2028,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_2027])).

cnf(c_7,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1171,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_1172,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1171])).

cnf(c_1176,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(X1)
    | v4_orders_2(k3_yellow19(X1,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1172,c_21])).

cnf(c_1177,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1176])).

cnf(c_1762,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1177])).

cnf(c_1995,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1762,c_495])).

cnf(c_1996,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1995])).

cnf(c_2000,plain,
    ( v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1996,c_24])).

cnf(c_2001,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_2000])).

cnf(c_14,negated_conjecture,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_176,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_11,plain,
    ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_445,plain,
    ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_446,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_450,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_446,c_24,c_22])).

cnf(c_830,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_176,c_450])).

cnf(c_831,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_830])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_835,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_831,c_16])).

cnf(c_836,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(X0,sK0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
    inference(renaming,[status(thm)],[c_835])).

cnf(c_5,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1243,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_1244,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1243])).

cnf(c_1248,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1244,c_21])).

cnf(c_1249,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1248])).

cnf(c_1704,plain,
    ( l1_waybel_0(k3_yellow19(X0,X1,sK1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X0)
    | v1_xboole_0(X1)
    | ~ l1_struct_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1249])).

cnf(c_1862,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | ~ l1_struct_0(X2)
    | k3_yellow19(X2,X1,sK1) != X0
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != sK1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_836,c_1704])).

cnf(c_1863,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(sK0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1862])).

cnf(c_65,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1867,plain,
    ( v1_xboole_0(X0)
    | ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1863,c_24,c_22,c_65])).

cnf(c_1868,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1867])).

cnf(c_2087,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2001,c_1868])).

cnf(c_2102,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2028,c_2087])).

cnf(c_2119,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(resolution,[status(thm)],[c_2055,c_2102])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1979,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_495])).

cnf(c_1980,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_1979])).

cnf(c_62,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1982,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1980,c_24,c_22,c_62,c_65])).

cnf(c_2270,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(sK0) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2119,c_1982])).

cnf(c_2271,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,u1_struct_0(sK0),sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,u1_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_2270])).

cnf(c_2532,plain,
    ( k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,u1_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))
    | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,u1_struct_0(sK0),sK1)),sK2) != iProver_top
    | r2_waybel_7(sK0,sK1,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2271])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1990,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_495])).

cnf(c_1991,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_1990])).

cnf(c_13,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_361,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_362,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_366,plain,
    ( v2_struct_0(X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_362,c_21])).

cnf(c_367,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(renaming,[status(thm)],[c_366])).

cnf(c_1314,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_367])).

cnf(c_1791,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_1314])).

cnf(c_1968,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK1 != sK1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1791,c_495])).

cnf(c_1969,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_1968])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_369,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_1971,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1969,c_24,c_22,c_19,c_18,c_17,c_65,c_369])).

cnf(c_2338,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_1971])).

cnf(c_2603,plain,
    ( k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | r2_waybel_7(sK0,sK1,sK2) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2532,c_1991,c_2338])).

cnf(c_2604,plain,
    ( r2_waybel_7(sK0,sK1,sK2) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2603])).

cnf(c_2536,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2538,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2546,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2538,c_0])).

cnf(c_15,negated_conjecture,
    ( r2_waybel_7(sK0,sK1,sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_178,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_12,plain,
    ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_412,plain,
    ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_413,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_417,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_413,c_24,c_22])).

cnf(c_797,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_178,c_417])).

cnf(c_798,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_797])).

cnf(c_802,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | r2_waybel_7(sK0,sK1,sK2)
    | r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_798,c_16])).

cnf(c_803,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(X0,sK0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
    inference(renaming,[status(thm)],[c_802])).

cnf(c_1904,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | ~ l1_struct_0(X2)
    | k3_yellow19(X2,X1,sK1) != X0
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != sK1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_803,c_1704])).

cnf(c_1905,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(sK0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1904])).

cnf(c_1909,plain,
    ( v1_xboole_0(X0)
    | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1905,c_24,c_22,c_65])).

cnf(c_1910,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1909])).

cnf(c_2088,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2001,c_1910])).

cnf(c_2101,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2028,c_2088])).

cnf(c_2148,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(resolution,[status(thm)],[c_2055,c_2101])).

cnf(c_2245,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(sK0) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2148,c_1982])).

cnf(c_2246,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,u1_struct_0(sK0),sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,u1_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_2245])).

cnf(c_2533,plain,
    ( k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,u1_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))
    | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,u1_struct_0(sK0),sK1)),sK2) = iProver_top
    | r2_waybel_7(sK0,sK1,sK2) = iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2246])).

cnf(c_2583,plain,
    ( k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | r2_waybel_7(sK0,sK1,sK2) = iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2533,c_1991,c_2338])).

cnf(c_2584,plain,
    ( r2_waybel_7(sK0,sK1,sK2) = iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2583])).

cnf(c_2588,plain,
    ( r2_waybel_7(sK0,sK1,sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2584,c_2536,c_2546])).

cnf(c_2608,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2604,c_2536,c_2546,c_2588])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:31:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.68/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/0.99  
% 1.68/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.68/0.99  
% 1.68/0.99  ------  iProver source info
% 1.68/0.99  
% 1.68/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.68/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.68/0.99  git: non_committed_changes: false
% 1.68/0.99  git: last_make_outside_of_git: false
% 1.68/0.99  
% 1.68/0.99  ------ 
% 1.68/0.99  
% 1.68/0.99  ------ Input Options
% 1.68/0.99  
% 1.68/0.99  --out_options                           all
% 1.68/0.99  --tptp_safe_out                         true
% 1.68/0.99  --problem_path                          ""
% 1.68/0.99  --include_path                          ""
% 1.68/0.99  --clausifier                            res/vclausify_rel
% 1.68/0.99  --clausifier_options                    --mode clausify
% 1.68/0.99  --stdin                                 false
% 1.68/0.99  --stats_out                             all
% 1.68/0.99  
% 1.68/0.99  ------ General Options
% 1.68/0.99  
% 1.68/0.99  --fof                                   false
% 1.68/0.99  --time_out_real                         305.
% 1.68/0.99  --time_out_virtual                      -1.
% 1.68/0.99  --symbol_type_check                     false
% 1.68/0.99  --clausify_out                          false
% 1.68/0.99  --sig_cnt_out                           false
% 1.68/0.99  --trig_cnt_out                          false
% 1.68/0.99  --trig_cnt_out_tolerance                1.
% 1.68/0.99  --trig_cnt_out_sk_spl                   false
% 1.68/0.99  --abstr_cl_out                          false
% 1.68/0.99  
% 1.68/0.99  ------ Global Options
% 1.68/0.99  
% 1.68/0.99  --schedule                              default
% 1.68/0.99  --add_important_lit                     false
% 1.68/0.99  --prop_solver_per_cl                    1000
% 1.68/0.99  --min_unsat_core                        false
% 1.68/0.99  --soft_assumptions                      false
% 1.68/0.99  --soft_lemma_size                       3
% 1.68/0.99  --prop_impl_unit_size                   0
% 1.68/0.99  --prop_impl_unit                        []
% 1.68/0.99  --share_sel_clauses                     true
% 1.68/0.99  --reset_solvers                         false
% 1.68/0.99  --bc_imp_inh                            [conj_cone]
% 1.68/0.99  --conj_cone_tolerance                   3.
% 1.68/0.99  --extra_neg_conj                        none
% 1.68/0.99  --large_theory_mode                     true
% 1.68/0.99  --prolific_symb_bound                   200
% 1.68/0.99  --lt_threshold                          2000
% 1.68/0.99  --clause_weak_htbl                      true
% 1.68/0.99  --gc_record_bc_elim                     false
% 1.68/0.99  
% 1.68/0.99  ------ Preprocessing Options
% 1.68/0.99  
% 1.68/0.99  --preprocessing_flag                    true
% 1.68/0.99  --time_out_prep_mult                    0.1
% 1.68/0.99  --splitting_mode                        input
% 1.68/0.99  --splitting_grd                         true
% 1.68/0.99  --splitting_cvd                         false
% 1.68/0.99  --splitting_cvd_svl                     false
% 1.68/0.99  --splitting_nvd                         32
% 1.68/0.99  --sub_typing                            true
% 1.68/0.99  --prep_gs_sim                           true
% 1.68/0.99  --prep_unflatten                        true
% 1.68/0.99  --prep_res_sim                          true
% 1.68/0.99  --prep_upred                            true
% 1.68/0.99  --prep_sem_filter                       exhaustive
% 1.68/0.99  --prep_sem_filter_out                   false
% 1.68/0.99  --pred_elim                             true
% 1.68/0.99  --res_sim_input                         true
% 1.68/0.99  --eq_ax_congr_red                       true
% 1.68/0.99  --pure_diseq_elim                       true
% 1.68/0.99  --brand_transform                       false
% 1.68/0.99  --non_eq_to_eq                          false
% 1.68/0.99  --prep_def_merge                        true
% 1.68/0.99  --prep_def_merge_prop_impl              false
% 1.68/0.99  --prep_def_merge_mbd                    true
% 1.68/0.99  --prep_def_merge_tr_red                 false
% 1.68/0.99  --prep_def_merge_tr_cl                  false
% 1.68/0.99  --smt_preprocessing                     true
% 1.68/0.99  --smt_ac_axioms                         fast
% 1.68/0.99  --preprocessed_out                      false
% 1.68/0.99  --preprocessed_stats                    false
% 1.68/0.99  
% 1.68/0.99  ------ Abstraction refinement Options
% 1.68/0.99  
% 1.68/0.99  --abstr_ref                             []
% 1.68/0.99  --abstr_ref_prep                        false
% 1.68/0.99  --abstr_ref_until_sat                   false
% 1.68/0.99  --abstr_ref_sig_restrict                funpre
% 1.68/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.68/0.99  --abstr_ref_under                       []
% 1.68/0.99  
% 1.68/0.99  ------ SAT Options
% 1.68/0.99  
% 1.68/0.99  --sat_mode                              false
% 1.68/0.99  --sat_fm_restart_options                ""
% 1.68/0.99  --sat_gr_def                            false
% 1.68/0.99  --sat_epr_types                         true
% 1.68/0.99  --sat_non_cyclic_types                  false
% 1.68/0.99  --sat_finite_models                     false
% 1.68/0.99  --sat_fm_lemmas                         false
% 1.68/0.99  --sat_fm_prep                           false
% 1.68/0.99  --sat_fm_uc_incr                        true
% 1.68/0.99  --sat_out_model                         small
% 1.68/0.99  --sat_out_clauses                       false
% 1.68/0.99  
% 1.68/0.99  ------ QBF Options
% 1.68/0.99  
% 1.68/0.99  --qbf_mode                              false
% 1.68/0.99  --qbf_elim_univ                         false
% 1.68/0.99  --qbf_dom_inst                          none
% 1.68/0.99  --qbf_dom_pre_inst                      false
% 1.68/0.99  --qbf_sk_in                             false
% 1.68/0.99  --qbf_pred_elim                         true
% 1.68/0.99  --qbf_split                             512
% 1.68/0.99  
% 1.68/0.99  ------ BMC1 Options
% 1.68/0.99  
% 1.68/0.99  --bmc1_incremental                      false
% 1.68/0.99  --bmc1_axioms                           reachable_all
% 1.68/0.99  --bmc1_min_bound                        0
% 1.68/0.99  --bmc1_max_bound                        -1
% 1.68/0.99  --bmc1_max_bound_default                -1
% 1.68/0.99  --bmc1_symbol_reachability              true
% 1.68/0.99  --bmc1_property_lemmas                  false
% 1.68/0.99  --bmc1_k_induction                      false
% 1.68/0.99  --bmc1_non_equiv_states                 false
% 1.68/0.99  --bmc1_deadlock                         false
% 1.68/0.99  --bmc1_ucm                              false
% 1.68/0.99  --bmc1_add_unsat_core                   none
% 1.68/0.99  --bmc1_unsat_core_children              false
% 1.68/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.68/0.99  --bmc1_out_stat                         full
% 1.68/0.99  --bmc1_ground_init                      false
% 1.68/0.99  --bmc1_pre_inst_next_state              false
% 1.68/0.99  --bmc1_pre_inst_state                   false
% 1.68/0.99  --bmc1_pre_inst_reach_state             false
% 1.68/0.99  --bmc1_out_unsat_core                   false
% 1.68/0.99  --bmc1_aig_witness_out                  false
% 1.68/0.99  --bmc1_verbose                          false
% 1.68/0.99  --bmc1_dump_clauses_tptp                false
% 1.68/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.68/0.99  --bmc1_dump_file                        -
% 1.68/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.68/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.68/0.99  --bmc1_ucm_extend_mode                  1
% 1.68/0.99  --bmc1_ucm_init_mode                    2
% 1.68/0.99  --bmc1_ucm_cone_mode                    none
% 1.68/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.68/0.99  --bmc1_ucm_relax_model                  4
% 1.68/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.68/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.68/0.99  --bmc1_ucm_layered_model                none
% 1.68/0.99  --bmc1_ucm_max_lemma_size               10
% 1.68/0.99  
% 1.68/0.99  ------ AIG Options
% 1.68/0.99  
% 1.68/0.99  --aig_mode                              false
% 1.68/0.99  
% 1.68/0.99  ------ Instantiation Options
% 1.68/0.99  
% 1.68/0.99  --instantiation_flag                    true
% 1.68/0.99  --inst_sos_flag                         false
% 1.68/0.99  --inst_sos_phase                        true
% 1.68/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.68/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.68/0.99  --inst_lit_sel_side                     num_symb
% 1.68/0.99  --inst_solver_per_active                1400
% 1.68/0.99  --inst_solver_calls_frac                1.
% 1.68/0.99  --inst_passive_queue_type               priority_queues
% 1.68/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.68/0.99  --inst_passive_queues_freq              [25;2]
% 1.68/0.99  --inst_dismatching                      true
% 1.68/0.99  --inst_eager_unprocessed_to_passive     true
% 1.68/0.99  --inst_prop_sim_given                   true
% 1.68/0.99  --inst_prop_sim_new                     false
% 1.68/0.99  --inst_subs_new                         false
% 1.68/0.99  --inst_eq_res_simp                      false
% 1.68/0.99  --inst_subs_given                       false
% 1.68/0.99  --inst_orphan_elimination               true
% 1.68/0.99  --inst_learning_loop_flag               true
% 1.68/0.99  --inst_learning_start                   3000
% 1.68/0.99  --inst_learning_factor                  2
% 1.68/0.99  --inst_start_prop_sim_after_learn       3
% 1.68/0.99  --inst_sel_renew                        solver
% 1.68/0.99  --inst_lit_activity_flag                true
% 1.68/0.99  --inst_restr_to_given                   false
% 1.68/0.99  --inst_activity_threshold               500
% 1.68/0.99  --inst_out_proof                        true
% 1.68/0.99  
% 1.68/0.99  ------ Resolution Options
% 1.68/0.99  
% 1.68/0.99  --resolution_flag                       true
% 1.68/0.99  --res_lit_sel                           adaptive
% 1.68/0.99  --res_lit_sel_side                      none
% 1.68/0.99  --res_ordering                          kbo
% 1.68/0.99  --res_to_prop_solver                    active
% 1.68/0.99  --res_prop_simpl_new                    false
% 1.68/0.99  --res_prop_simpl_given                  true
% 1.68/0.99  --res_passive_queue_type                priority_queues
% 1.68/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.68/0.99  --res_passive_queues_freq               [15;5]
% 1.68/0.99  --res_forward_subs                      full
% 1.68/0.99  --res_backward_subs                     full
% 1.68/0.99  --res_forward_subs_resolution           true
% 1.68/0.99  --res_backward_subs_resolution          true
% 1.68/0.99  --res_orphan_elimination                true
% 1.68/0.99  --res_time_limit                        2.
% 1.68/0.99  --res_out_proof                         true
% 1.68/0.99  
% 1.68/0.99  ------ Superposition Options
% 1.68/0.99  
% 1.68/0.99  --superposition_flag                    true
% 1.68/0.99  --sup_passive_queue_type                priority_queues
% 1.68/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.68/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.68/0.99  --demod_completeness_check              fast
% 1.68/0.99  --demod_use_ground                      true
% 1.68/0.99  --sup_to_prop_solver                    passive
% 1.68/0.99  --sup_prop_simpl_new                    true
% 1.68/0.99  --sup_prop_simpl_given                  true
% 1.68/0.99  --sup_fun_splitting                     false
% 1.68/0.99  --sup_smt_interval                      50000
% 1.68/0.99  
% 1.68/0.99  ------ Superposition Simplification Setup
% 1.68/0.99  
% 1.68/0.99  --sup_indices_passive                   []
% 1.68/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.68/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.99  --sup_full_bw                           [BwDemod]
% 1.68/0.99  --sup_immed_triv                        [TrivRules]
% 1.68/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.68/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.99  --sup_immed_bw_main                     []
% 1.68/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.68/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/0.99  
% 1.68/0.99  ------ Combination Options
% 1.68/0.99  
% 1.68/0.99  --comb_res_mult                         3
% 1.68/0.99  --comb_sup_mult                         2
% 1.68/0.99  --comb_inst_mult                        10
% 1.68/0.99  
% 1.68/0.99  ------ Debug Options
% 1.68/0.99  
% 1.68/0.99  --dbg_backtrace                         false
% 1.68/0.99  --dbg_dump_prop_clauses                 false
% 1.68/0.99  --dbg_dump_prop_clauses_file            -
% 1.68/0.99  --dbg_out_stat                          false
% 1.68/0.99  ------ Parsing...
% 1.68/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.68/0.99  
% 1.68/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 12 0s  sf_e  pe_s  pe_e 
% 1.68/0.99  
% 1.68/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.68/0.99  
% 1.68/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.68/0.99  ------ Proving...
% 1.68/0.99  ------ Problem Properties 
% 1.68/0.99  
% 1.68/0.99  
% 1.68/0.99  clauses                                 10
% 1.68/0.99  conjectures                             2
% 1.68/0.99  EPR                                     0
% 1.68/0.99  Horn                                    8
% 1.68/0.99  unary                                   6
% 1.68/0.99  binary                                  0
% 1.68/0.99  lits                                    34
% 1.68/0.99  lits eq                                 15
% 1.68/0.99  fd_pure                                 0
% 1.68/0.99  fd_pseudo                               0
% 1.68/0.99  fd_cond                                 0
% 1.68/0.99  fd_pseudo_cond                          0
% 1.68/0.99  AC symbols                              0
% 1.68/0.99  
% 1.68/0.99  ------ Schedule dynamic 5 is on 
% 1.68/0.99  
% 1.68/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.68/0.99  
% 1.68/0.99  
% 1.68/0.99  ------ 
% 1.68/0.99  Current options:
% 1.68/0.99  ------ 
% 1.68/0.99  
% 1.68/0.99  ------ Input Options
% 1.68/0.99  
% 1.68/0.99  --out_options                           all
% 1.68/0.99  --tptp_safe_out                         true
% 1.68/0.99  --problem_path                          ""
% 1.68/0.99  --include_path                          ""
% 1.68/0.99  --clausifier                            res/vclausify_rel
% 1.68/0.99  --clausifier_options                    --mode clausify
% 1.68/0.99  --stdin                                 false
% 1.68/0.99  --stats_out                             all
% 1.68/0.99  
% 1.68/0.99  ------ General Options
% 1.68/0.99  
% 1.68/0.99  --fof                                   false
% 1.68/0.99  --time_out_real                         305.
% 1.68/0.99  --time_out_virtual                      -1.
% 1.68/0.99  --symbol_type_check                     false
% 1.68/0.99  --clausify_out                          false
% 1.68/0.99  --sig_cnt_out                           false
% 1.68/0.99  --trig_cnt_out                          false
% 1.68/0.99  --trig_cnt_out_tolerance                1.
% 1.68/0.99  --trig_cnt_out_sk_spl                   false
% 1.68/0.99  --abstr_cl_out                          false
% 1.68/0.99  
% 1.68/0.99  ------ Global Options
% 1.68/0.99  
% 1.68/0.99  --schedule                              default
% 1.68/0.99  --add_important_lit                     false
% 1.68/0.99  --prop_solver_per_cl                    1000
% 1.68/0.99  --min_unsat_core                        false
% 1.68/0.99  --soft_assumptions                      false
% 1.68/0.99  --soft_lemma_size                       3
% 1.68/0.99  --prop_impl_unit_size                   0
% 1.68/0.99  --prop_impl_unit                        []
% 1.68/0.99  --share_sel_clauses                     true
% 1.68/0.99  --reset_solvers                         false
% 1.68/0.99  --bc_imp_inh                            [conj_cone]
% 1.68/0.99  --conj_cone_tolerance                   3.
% 1.68/0.99  --extra_neg_conj                        none
% 1.68/0.99  --large_theory_mode                     true
% 1.68/0.99  --prolific_symb_bound                   200
% 1.68/0.99  --lt_threshold                          2000
% 1.68/0.99  --clause_weak_htbl                      true
% 1.68/0.99  --gc_record_bc_elim                     false
% 1.68/0.99  
% 1.68/0.99  ------ Preprocessing Options
% 1.68/0.99  
% 1.68/0.99  --preprocessing_flag                    true
% 1.68/0.99  --time_out_prep_mult                    0.1
% 1.68/0.99  --splitting_mode                        input
% 1.68/0.99  --splitting_grd                         true
% 1.68/0.99  --splitting_cvd                         false
% 1.68/0.99  --splitting_cvd_svl                     false
% 1.68/0.99  --splitting_nvd                         32
% 1.68/0.99  --sub_typing                            true
% 1.68/0.99  --prep_gs_sim                           true
% 1.68/0.99  --prep_unflatten                        true
% 1.68/0.99  --prep_res_sim                          true
% 1.68/0.99  --prep_upred                            true
% 1.68/0.99  --prep_sem_filter                       exhaustive
% 1.68/0.99  --prep_sem_filter_out                   false
% 1.68/0.99  --pred_elim                             true
% 1.68/0.99  --res_sim_input                         true
% 1.68/0.99  --eq_ax_congr_red                       true
% 1.68/0.99  --pure_diseq_elim                       true
% 1.68/0.99  --brand_transform                       false
% 1.68/0.99  --non_eq_to_eq                          false
% 1.68/0.99  --prep_def_merge                        true
% 1.68/0.99  --prep_def_merge_prop_impl              false
% 1.68/0.99  --prep_def_merge_mbd                    true
% 1.68/0.99  --prep_def_merge_tr_red                 false
% 1.68/0.99  --prep_def_merge_tr_cl                  false
% 1.68/0.99  --smt_preprocessing                     true
% 1.68/0.99  --smt_ac_axioms                         fast
% 1.68/0.99  --preprocessed_out                      false
% 1.68/0.99  --preprocessed_stats                    false
% 1.68/0.99  
% 1.68/0.99  ------ Abstraction refinement Options
% 1.68/0.99  
% 1.68/0.99  --abstr_ref                             []
% 1.68/0.99  --abstr_ref_prep                        false
% 1.68/0.99  --abstr_ref_until_sat                   false
% 1.68/0.99  --abstr_ref_sig_restrict                funpre
% 1.68/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.68/0.99  --abstr_ref_under                       []
% 1.68/0.99  
% 1.68/0.99  ------ SAT Options
% 1.68/0.99  
% 1.68/0.99  --sat_mode                              false
% 1.68/0.99  --sat_fm_restart_options                ""
% 1.68/0.99  --sat_gr_def                            false
% 1.68/0.99  --sat_epr_types                         true
% 1.68/0.99  --sat_non_cyclic_types                  false
% 1.68/0.99  --sat_finite_models                     false
% 1.68/0.99  --sat_fm_lemmas                         false
% 1.68/0.99  --sat_fm_prep                           false
% 1.68/0.99  --sat_fm_uc_incr                        true
% 1.68/0.99  --sat_out_model                         small
% 1.68/0.99  --sat_out_clauses                       false
% 1.68/0.99  
% 1.68/0.99  ------ QBF Options
% 1.68/0.99  
% 1.68/0.99  --qbf_mode                              false
% 1.68/0.99  --qbf_elim_univ                         false
% 1.68/0.99  --qbf_dom_inst                          none
% 1.68/0.99  --qbf_dom_pre_inst                      false
% 1.68/0.99  --qbf_sk_in                             false
% 1.68/0.99  --qbf_pred_elim                         true
% 1.68/0.99  --qbf_split                             512
% 1.68/0.99  
% 1.68/0.99  ------ BMC1 Options
% 1.68/0.99  
% 1.68/0.99  --bmc1_incremental                      false
% 1.68/0.99  --bmc1_axioms                           reachable_all
% 1.68/0.99  --bmc1_min_bound                        0
% 1.68/0.99  --bmc1_max_bound                        -1
% 1.68/0.99  --bmc1_max_bound_default                -1
% 1.68/0.99  --bmc1_symbol_reachability              true
% 1.68/0.99  --bmc1_property_lemmas                  false
% 1.68/0.99  --bmc1_k_induction                      false
% 1.68/0.99  --bmc1_non_equiv_states                 false
% 1.68/0.99  --bmc1_deadlock                         false
% 1.68/0.99  --bmc1_ucm                              false
% 1.68/0.99  --bmc1_add_unsat_core                   none
% 1.68/0.99  --bmc1_unsat_core_children              false
% 1.68/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.68/0.99  --bmc1_out_stat                         full
% 1.68/0.99  --bmc1_ground_init                      false
% 1.68/0.99  --bmc1_pre_inst_next_state              false
% 1.68/0.99  --bmc1_pre_inst_state                   false
% 1.68/0.99  --bmc1_pre_inst_reach_state             false
% 1.68/0.99  --bmc1_out_unsat_core                   false
% 1.68/0.99  --bmc1_aig_witness_out                  false
% 1.68/0.99  --bmc1_verbose                          false
% 1.68/0.99  --bmc1_dump_clauses_tptp                false
% 1.68/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.68/0.99  --bmc1_dump_file                        -
% 1.68/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.68/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.68/0.99  --bmc1_ucm_extend_mode                  1
% 1.68/0.99  --bmc1_ucm_init_mode                    2
% 1.68/0.99  --bmc1_ucm_cone_mode                    none
% 1.68/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.68/0.99  --bmc1_ucm_relax_model                  4
% 1.68/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.68/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.68/0.99  --bmc1_ucm_layered_model                none
% 1.68/0.99  --bmc1_ucm_max_lemma_size               10
% 1.68/0.99  
% 1.68/0.99  ------ AIG Options
% 1.68/0.99  
% 1.68/0.99  --aig_mode                              false
% 1.68/0.99  
% 1.68/0.99  ------ Instantiation Options
% 1.68/0.99  
% 1.68/0.99  --instantiation_flag                    true
% 1.68/0.99  --inst_sos_flag                         false
% 1.68/0.99  --inst_sos_phase                        true
% 1.68/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.68/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.68/0.99  --inst_lit_sel_side                     none
% 1.68/0.99  --inst_solver_per_active                1400
% 1.68/0.99  --inst_solver_calls_frac                1.
% 1.68/0.99  --inst_passive_queue_type               priority_queues
% 1.68/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.68/0.99  --inst_passive_queues_freq              [25;2]
% 1.68/0.99  --inst_dismatching                      true
% 1.68/0.99  --inst_eager_unprocessed_to_passive     true
% 1.68/0.99  --inst_prop_sim_given                   true
% 1.68/0.99  --inst_prop_sim_new                     false
% 1.68/0.99  --inst_subs_new                         false
% 1.68/0.99  --inst_eq_res_simp                      false
% 1.68/0.99  --inst_subs_given                       false
% 1.68/0.99  --inst_orphan_elimination               true
% 1.68/0.99  --inst_learning_loop_flag               true
% 1.68/0.99  --inst_learning_start                   3000
% 1.68/0.99  --inst_learning_factor                  2
% 1.68/0.99  --inst_start_prop_sim_after_learn       3
% 1.68/0.99  --inst_sel_renew                        solver
% 1.68/0.99  --inst_lit_activity_flag                true
% 1.68/0.99  --inst_restr_to_given                   false
% 1.68/0.99  --inst_activity_threshold               500
% 1.68/0.99  --inst_out_proof                        true
% 1.68/0.99  
% 1.68/0.99  ------ Resolution Options
% 1.68/0.99  
% 1.68/0.99  --resolution_flag                       false
% 1.68/0.99  --res_lit_sel                           adaptive
% 1.68/0.99  --res_lit_sel_side                      none
% 1.68/0.99  --res_ordering                          kbo
% 1.68/0.99  --res_to_prop_solver                    active
% 1.68/0.99  --res_prop_simpl_new                    false
% 1.68/0.99  --res_prop_simpl_given                  true
% 1.68/0.99  --res_passive_queue_type                priority_queues
% 1.68/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.68/0.99  --res_passive_queues_freq               [15;5]
% 1.68/0.99  --res_forward_subs                      full
% 1.68/0.99  --res_backward_subs                     full
% 1.68/0.99  --res_forward_subs_resolution           true
% 1.68/0.99  --res_backward_subs_resolution          true
% 1.68/0.99  --res_orphan_elimination                true
% 1.68/0.99  --res_time_limit                        2.
% 1.68/0.99  --res_out_proof                         true
% 1.68/0.99  
% 1.68/0.99  ------ Superposition Options
% 1.68/0.99  
% 1.68/0.99  --superposition_flag                    true
% 1.68/0.99  --sup_passive_queue_type                priority_queues
% 1.68/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.68/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.68/0.99  --demod_completeness_check              fast
% 1.68/0.99  --demod_use_ground                      true
% 1.68/0.99  --sup_to_prop_solver                    passive
% 1.68/0.99  --sup_prop_simpl_new                    true
% 1.68/0.99  --sup_prop_simpl_given                  true
% 1.68/0.99  --sup_fun_splitting                     false
% 1.68/0.99  --sup_smt_interval                      50000
% 1.68/0.99  
% 1.68/0.99  ------ Superposition Simplification Setup
% 1.68/0.99  
% 1.68/0.99  --sup_indices_passive                   []
% 1.68/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.68/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.99  --sup_full_bw                           [BwDemod]
% 1.68/0.99  --sup_immed_triv                        [TrivRules]
% 1.68/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.68/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.99  --sup_immed_bw_main                     []
% 1.68/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.68/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/0.99  
% 1.68/0.99  ------ Combination Options
% 1.68/0.99  
% 1.68/0.99  --comb_res_mult                         3
% 1.68/0.99  --comb_sup_mult                         2
% 1.68/0.99  --comb_inst_mult                        10
% 1.68/0.99  
% 1.68/0.99  ------ Debug Options
% 1.68/0.99  
% 1.68/0.99  --dbg_backtrace                         false
% 1.68/0.99  --dbg_dump_prop_clauses                 false
% 1.68/0.99  --dbg_dump_prop_clauses_file            -
% 1.68/0.99  --dbg_out_stat                          false
% 1.68/0.99  
% 1.68/0.99  
% 1.68/0.99  
% 1.68/0.99  
% 1.68/0.99  ------ Proving...
% 1.68/0.99  
% 1.68/0.99  
% 1.68/0.99  % SZS status Theorem for theBenchmark.p
% 1.68/0.99  
% 1.68/0.99   Resolution empty clause
% 1.68/0.99  
% 1.68/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.68/0.99  
% 1.68/0.99  fof(f12,conjecture,(
% 1.68/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f13,negated_conjecture,(
% 1.68/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 1.68/0.99    inference(negated_conjecture,[],[f12])).
% 1.68/0.99  
% 1.68/0.99  fof(f32,plain,(
% 1.68/0.99    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.68/0.99    inference(ennf_transformation,[],[f13])).
% 1.68/0.99  
% 1.68/0.99  fof(f33,plain,(
% 1.68/0.99    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.68/0.99    inference(flattening,[],[f32])).
% 1.68/0.99  
% 1.68/0.99  fof(f35,plain,(
% 1.68/0.99    ? [X0] : (? [X1] : (? [X2] : (((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.68/0.99    inference(nnf_transformation,[],[f33])).
% 1.68/0.99  
% 1.68/0.99  fof(f36,plain,(
% 1.68/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.68/0.99    inference(flattening,[],[f35])).
% 1.68/0.99  
% 1.68/0.99  fof(f39,plain,(
% 1.68/0.99    ( ! [X0,X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r2_waybel_7(X0,X1,sK2) | ~r2_hidden(sK2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,sK2) | r2_hidden(sK2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.68/0.99    introduced(choice_axiom,[])).
% 1.68/0.99  
% 1.68/0.99  fof(f38,plain,(
% 1.68/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r2_waybel_7(X0,sK1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)))) & (r2_waybel_7(X0,sK1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK1))) )),
% 1.68/0.99    introduced(choice_axiom,[])).
% 1.68/0.99  
% 1.68/0.99  fof(f37,plain,(
% 1.68/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_waybel_7(sK0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & (r2_waybel_7(sK0,X1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.68/0.99    introduced(choice_axiom,[])).
% 1.68/0.99  
% 1.68/0.99  fof(f40,plain,(
% 1.68/0.99    (((~r2_waybel_7(sK0,sK1,sK2) | ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.68/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).
% 1.68/0.99  
% 1.68/0.99  fof(f61,plain,(
% 1.68/0.99    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.68/0.99    inference(cnf_transformation,[],[f40])).
% 1.68/0.99  
% 1.68/0.99  fof(f6,axiom,(
% 1.68/0.99    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f46,plain,(
% 1.68/0.99    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.68/0.99    inference(cnf_transformation,[],[f6])).
% 1.68/0.99  
% 1.68/0.99  fof(f76,plain,(
% 1.68/0.99    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.68/0.99    inference(definition_unfolding,[],[f61,f46])).
% 1.68/0.99  
% 1.68/0.99  fof(f62,plain,(
% 1.68/0.99    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.68/0.99    inference(cnf_transformation,[],[f40])).
% 1.68/0.99  
% 1.68/0.99  fof(f75,plain,(
% 1.68/0.99    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.68/0.99    inference(definition_unfolding,[],[f62,f46])).
% 1.68/0.99  
% 1.68/0.99  fof(f9,axiom,(
% 1.68/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f17,plain,(
% 1.68/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.68/0.99    inference(pure_predicate_removal,[],[f9])).
% 1.68/0.99  
% 1.68/0.99  fof(f26,plain,(
% 1.68/0.99    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.68/0.99    inference(ennf_transformation,[],[f17])).
% 1.68/0.99  
% 1.68/0.99  fof(f27,plain,(
% 1.68/0.99    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.68/0.99    inference(flattening,[],[f26])).
% 1.68/0.99  
% 1.68/0.99  fof(f52,plain,(
% 1.68/0.99    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.68/0.99    inference(cnf_transformation,[],[f27])).
% 1.68/0.99  
% 1.68/0.99  fof(f71,plain,(
% 1.68/0.99    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.68/0.99    inference(definition_unfolding,[],[f52,f46,f46,f46,f46])).
% 1.68/0.99  
% 1.68/0.99  fof(f60,plain,(
% 1.68/0.99    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 1.68/0.99    inference(cnf_transformation,[],[f40])).
% 1.68/0.99  
% 1.68/0.99  fof(f77,plain,(
% 1.68/0.99    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 1.68/0.99    inference(definition_unfolding,[],[f60,f46])).
% 1.68/0.99  
% 1.68/0.99  fof(f59,plain,(
% 1.68/0.99    ~v1_xboole_0(sK1)),
% 1.68/0.99    inference(cnf_transformation,[],[f40])).
% 1.68/0.99  
% 1.68/0.99  fof(f4,axiom,(
% 1.68/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f19,plain,(
% 1.68/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.68/0.99    inference(ennf_transformation,[],[f4])).
% 1.68/0.99  
% 1.68/0.99  fof(f44,plain,(
% 1.68/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.68/0.99    inference(cnf_transformation,[],[f19])).
% 1.68/0.99  
% 1.68/0.99  fof(f58,plain,(
% 1.68/0.99    l1_pre_topc(sK0)),
% 1.68/0.99    inference(cnf_transformation,[],[f40])).
% 1.68/0.99  
% 1.68/0.99  fof(f56,plain,(
% 1.68/0.99    ~v2_struct_0(sK0)),
% 1.68/0.99    inference(cnf_transformation,[],[f40])).
% 1.68/0.99  
% 1.68/0.99  fof(f7,axiom,(
% 1.68/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f16,plain,(
% 1.68/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.68/0.99    inference(pure_predicate_removal,[],[f7])).
% 1.68/0.99  
% 1.68/0.99  fof(f22,plain,(
% 1.68/0.99    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.68/0.99    inference(ennf_transformation,[],[f16])).
% 1.68/0.99  
% 1.68/0.99  fof(f23,plain,(
% 1.68/0.99    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.68/0.99    inference(flattening,[],[f22])).
% 1.68/0.99  
% 1.68/0.99  fof(f47,plain,(
% 1.68/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.68/0.99    inference(cnf_transformation,[],[f23])).
% 1.68/0.99  
% 1.68/0.99  fof(f68,plain,(
% 1.68/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.68/0.99    inference(definition_unfolding,[],[f47,f46,f46,f46])).
% 1.68/0.99  
% 1.68/0.99  fof(f8,axiom,(
% 1.68/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f14,plain,(
% 1.68/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.68/0.99    inference(pure_predicate_removal,[],[f8])).
% 1.68/0.99  
% 1.68/0.99  fof(f15,plain,(
% 1.68/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.68/0.99    inference(pure_predicate_removal,[],[f14])).
% 1.68/0.99  
% 1.68/0.99  fof(f24,plain,(
% 1.68/0.99    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.68/0.99    inference(ennf_transformation,[],[f15])).
% 1.68/0.99  
% 1.68/0.99  fof(f25,plain,(
% 1.68/0.99    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.68/0.99    inference(flattening,[],[f24])).
% 1.68/0.99  
% 1.68/0.99  fof(f50,plain,(
% 1.68/0.99    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.68/0.99    inference(cnf_transformation,[],[f25])).
% 1.68/0.99  
% 1.68/0.99  fof(f69,plain,(
% 1.68/0.99    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.68/0.99    inference(definition_unfolding,[],[f50,f46,f46,f46])).
% 1.68/0.99  
% 1.68/0.99  fof(f66,plain,(
% 1.68/0.99    ~r2_waybel_7(sK0,sK1,sK2) | ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 1.68/0.99    inference(cnf_transformation,[],[f40])).
% 1.68/0.99  
% 1.68/0.99  fof(f10,axiom,(
% 1.68/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f28,plain,(
% 1.68/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.68/0.99    inference(ennf_transformation,[],[f10])).
% 1.68/0.99  
% 1.68/0.99  fof(f29,plain,(
% 1.68/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.68/0.99    inference(flattening,[],[f28])).
% 1.68/0.99  
% 1.68/0.99  fof(f34,plain,(
% 1.68/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.68/0.99    inference(nnf_transformation,[],[f29])).
% 1.68/0.99  
% 1.68/0.99  fof(f54,plain,(
% 1.68/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.99    inference(cnf_transformation,[],[f34])).
% 1.68/0.99  
% 1.68/0.99  fof(f57,plain,(
% 1.68/0.99    v2_pre_topc(sK0)),
% 1.68/0.99    inference(cnf_transformation,[],[f40])).
% 1.68/0.99  
% 1.68/0.99  fof(f64,plain,(
% 1.68/0.99    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.68/0.99    inference(cnf_transformation,[],[f40])).
% 1.68/0.99  
% 1.68/0.99  fof(f48,plain,(
% 1.68/0.99    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.68/0.99    inference(cnf_transformation,[],[f23])).
% 1.68/0.99  
% 1.68/0.99  fof(f67,plain,(
% 1.68/0.99    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.68/0.99    inference(definition_unfolding,[],[f48,f46,f46,f46])).
% 1.68/0.99  
% 1.68/0.99  fof(f5,axiom,(
% 1.68/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f20,plain,(
% 1.68/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.68/0.99    inference(ennf_transformation,[],[f5])).
% 1.68/0.99  
% 1.68/0.99  fof(f21,plain,(
% 1.68/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.68/0.99    inference(flattening,[],[f20])).
% 1.68/0.99  
% 1.68/0.99  fof(f45,plain,(
% 1.68/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.68/0.99    inference(cnf_transformation,[],[f21])).
% 1.68/0.99  
% 1.68/0.99  fof(f3,axiom,(
% 1.68/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f18,plain,(
% 1.68/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.68/0.99    inference(ennf_transformation,[],[f3])).
% 1.68/0.99  
% 1.68/0.99  fof(f43,plain,(
% 1.68/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.68/0.99    inference(cnf_transformation,[],[f18])).
% 1.68/0.99  
% 1.68/0.99  fof(f11,axiom,(
% 1.68/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f30,plain,(
% 1.68/0.99    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.68/0.99    inference(ennf_transformation,[],[f11])).
% 1.68/0.99  
% 1.68/0.99  fof(f31,plain,(
% 1.68/0.99    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.68/0.99    inference(flattening,[],[f30])).
% 1.68/0.99  
% 1.68/0.99  fof(f55,plain,(
% 1.68/0.99    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.68/0.99    inference(cnf_transformation,[],[f31])).
% 1.68/0.99  
% 1.68/0.99  fof(f73,plain,(
% 1.68/0.99    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.68/0.99    inference(definition_unfolding,[],[f55,f46,f46,f46,f46])).
% 1.68/0.99  
% 1.68/0.99  fof(f63,plain,(
% 1.68/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 1.68/0.99    inference(cnf_transformation,[],[f40])).
% 1.68/0.99  
% 1.68/0.99  fof(f74,plain,(
% 1.68/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.68/0.99    inference(definition_unfolding,[],[f63,f46])).
% 1.68/0.99  
% 1.68/0.99  fof(f2,axiom,(
% 1.68/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f42,plain,(
% 1.68/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.68/0.99    inference(cnf_transformation,[],[f2])).
% 1.68/0.99  
% 1.68/0.99  fof(f1,axiom,(
% 1.68/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f41,plain,(
% 1.68/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.68/0.99    inference(cnf_transformation,[],[f1])).
% 1.68/0.99  
% 1.68/0.99  fof(f65,plain,(
% 1.68/0.99    r2_waybel_7(sK0,sK1,sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 1.68/0.99    inference(cnf_transformation,[],[f40])).
% 1.68/0.99  
% 1.68/0.99  fof(f53,plain,(
% 1.68/0.99    ( ! [X2,X0,X1] : (r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.68/0.99    inference(cnf_transformation,[],[f34])).
% 1.68/0.99  
% 1.68/0.99  cnf(c_19,negated_conjecture,
% 1.68/0.99      ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.68/0.99      inference(cnf_transformation,[],[f76]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_18,negated_conjecture,
% 1.68/0.99      ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.68/0.99      inference(cnf_transformation,[],[f75]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_9,plain,
% 1.68/0.99      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.68/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.68/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.68/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.68/0.99      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.68/0.99      | v2_struct_0(X2)
% 1.68/0.99      | v1_xboole_0(X1)
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | ~ l1_struct_0(X2) ),
% 1.68/0.99      inference(cnf_transformation,[],[f71]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_20,negated_conjecture,
% 1.68/0.99      ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
% 1.68/0.99      inference(cnf_transformation,[],[f77]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_322,plain,
% 1.68/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.68/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.68/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.68/0.99      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.68/0.99      | v2_struct_0(X2)
% 1.68/0.99      | v1_xboole_0(X1)
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | ~ l1_struct_0(X2)
% 1.68/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 1.68/0.99      | sK1 != X0 ),
% 1.68/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_323,plain,
% 1.68/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.68/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.68/0.99      | v2_struct_0(X1)
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | v1_xboole_0(sK1)
% 1.68/0.99      | ~ l1_struct_0(X1)
% 1.68/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.68/0.99      inference(unflattening,[status(thm)],[c_322]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_21,negated_conjecture,
% 1.68/0.99      ( ~ v1_xboole_0(sK1) ),
% 1.68/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_327,plain,
% 1.68/0.99      ( v1_xboole_0(X0)
% 1.68/0.99      | v2_struct_0(X1)
% 1.68/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.68/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.68/0.99      | ~ l1_struct_0(X1)
% 1.68/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.68/0.99      inference(global_propositional_subsumption,[status(thm)],[c_323,c_21]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_328,plain,
% 1.68/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.68/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.68/0.99      | v2_struct_0(X1)
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | ~ l1_struct_0(X1)
% 1.68/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.68/0.99      inference(renaming,[status(thm)],[c_327]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_1279,plain,
% 1.68/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.68/0.99      | v2_struct_0(X1)
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | ~ l1_struct_0(X1)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.68/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.68/0.99      | sK1 != sK1 ),
% 1.68/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_328]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_1672,plain,
% 1.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.68/0.99      | v2_struct_0(X1)
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | ~ l1_struct_0(X1)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.68/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.68/0.99      | sK1 != sK1 ),
% 1.68/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_1279]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_3,plain,
% 1.68/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.68/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_22,negated_conjecture,
% 1.68/0.99      ( l1_pre_topc(sK0) ),
% 1.68/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_494,plain,
% 1.68/0.99      ( l1_struct_0(X0) | sK0 != X0 ),
% 1.68/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_22]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_495,plain,
% 1.68/0.99      ( l1_struct_0(sK0) ),
% 1.68/0.99      inference(unflattening,[status(thm)],[c_494]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2049,plain,
% 1.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.68/0.99      | v2_struct_0(X1)
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.68/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.68/0.99      | sK1 != sK1
% 1.68/0.99      | sK0 != X1 ),
% 1.68/0.99      inference(resolution_lifted,[status(thm)],[c_1672,c_495]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2050,plain,
% 1.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.68/0.99      | v2_struct_0(sK0)
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.68/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.68/0.99      inference(unflattening,[status(thm)],[c_2049]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_24,negated_conjecture,
% 1.68/0.99      ( ~ v2_struct_0(sK0) ),
% 1.68/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2054,plain,
% 1.68/0.99      ( v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.68/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.68/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2050,c_24]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2055,plain,
% 1.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.68/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.68/0.99      inference(renaming,[status(thm)],[c_2054]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_6,plain,
% 1.68/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.68/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.68/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.68/0.99      | v2_struct_0(X2)
% 1.68/0.99      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.68/0.99      | v1_xboole_0(X1)
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | ~ l1_struct_0(X2) ),
% 1.68/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_1207,plain,
% 1.68/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.68/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.68/0.99      | v2_struct_0(X2)
% 1.68/0.99      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.68/0.99      | v1_xboole_0(X1)
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | ~ l1_struct_0(X2)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.68/0.99      | sK1 != X0 ),
% 1.68/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_1208,plain,
% 1.68/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | v2_struct_0(X1)
% 1.68/0.99      | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | v1_xboole_0(sK1)
% 1.68/0.99      | ~ l1_struct_0(X1)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/0.99      inference(unflattening,[status(thm)],[c_1207]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_1212,plain,
% 1.68/0.99      ( v1_xboole_0(X0)
% 1.68/0.99      | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
% 1.68/0.99      | v2_struct_0(X1)
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.68/0.99      | ~ l1_struct_0(X1)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1208,c_21]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_1213,plain,
% 1.68/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | v2_struct_0(X1)
% 1.68/0.99      | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | ~ l1_struct_0(X1)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/0.99      inference(renaming,[status(thm)],[c_1212]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_1733,plain,
% 1.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | v2_struct_0(X1)
% 1.68/0.99      | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | ~ l1_struct_0(X1)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.68/0.99      | sK1 != sK1 ),
% 1.68/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_1213]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2022,plain,
% 1.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | v2_struct_0(X1)
% 1.68/0.99      | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.68/0.99      | sK1 != sK1
% 1.68/0.99      | sK0 != X1 ),
% 1.68/0.99      inference(resolution_lifted,[status(thm)],[c_1733,c_495]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2023,plain,
% 1.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.68/0.99      | v2_struct_0(sK0)
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/0.99      inference(unflattening,[status(thm)],[c_2022]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2027,plain,
% 1.68/0.99      ( ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2023,c_24]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2028,plain,
% 1.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/0.99      inference(renaming,[status(thm)],[c_2027]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_7,plain,
% 1.68/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.68/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.68/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.68/0.99      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.68/0.99      | v2_struct_0(X2)
% 1.68/0.99      | v1_xboole_0(X1)
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | ~ l1_struct_0(X2) ),
% 1.68/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_1171,plain,
% 1.68/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.68/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.68/0.99      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.68/0.99      | v2_struct_0(X2)
% 1.68/0.99      | v1_xboole_0(X1)
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | ~ l1_struct_0(X2)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.68/0.99      | sK1 != X0 ),
% 1.68/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_1172,plain,
% 1.68/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | v4_orders_2(k3_yellow19(X1,X0,sK1))
% 1.68/0.99      | v2_struct_0(X1)
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | v1_xboole_0(sK1)
% 1.68/0.99      | ~ l1_struct_0(X1)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/0.99      inference(unflattening,[status(thm)],[c_1171]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_1176,plain,
% 1.68/0.99      ( v1_xboole_0(X0)
% 1.68/0.99      | v2_struct_0(X1)
% 1.68/0.99      | v4_orders_2(k3_yellow19(X1,X0,sK1))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.68/0.99      | ~ l1_struct_0(X1)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1172,c_21]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_1177,plain,
% 1.68/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | v4_orders_2(k3_yellow19(X1,X0,sK1))
% 1.68/0.99      | v2_struct_0(X1)
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | ~ l1_struct_0(X1)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/0.99      inference(renaming,[status(thm)],[c_1176]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_1762,plain,
% 1.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | v4_orders_2(k3_yellow19(X1,X0,sK1))
% 1.68/0.99      | v2_struct_0(X1)
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | ~ l1_struct_0(X1)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.68/0.99      | sK1 != sK1 ),
% 1.68/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_1177]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_1995,plain,
% 1.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | v4_orders_2(k3_yellow19(X1,X0,sK1))
% 1.68/0.99      | v2_struct_0(X1)
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.68/0.99      | sK1 != sK1
% 1.68/0.99      | sK0 != X1 ),
% 1.68/0.99      inference(resolution_lifted,[status(thm)],[c_1762,c_495]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_1996,plain,
% 1.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.68/0.99      | v2_struct_0(sK0)
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/0.99      inference(unflattening,[status(thm)],[c_1995]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2000,plain,
% 1.68/0.99      ( v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1996,c_24]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2001,plain,
% 1.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.68/0.99      | v1_xboole_0(X0)
% 1.68/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/0.99      inference(renaming,[status(thm)],[c_2000]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_14,negated_conjecture,
% 1.68/0.99      ( ~ r2_waybel_7(sK0,sK1,sK2)
% 1.68/0.99      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
% 1.68/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_176,plain,
% 1.68/0.99      ( ~ r2_waybel_7(sK0,sK1,sK2)
% 1.68/0.99      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
% 1.68/0.99      inference(prop_impl,[status(thm)],[c_14]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_11,plain,
% 1.68/0.99      ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.68/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 1.68/0.99      | ~ l1_waybel_0(X1,X0)
% 1.68/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.68/0.99      | ~ v2_pre_topc(X0)
% 1.68/0.99      | ~ v7_waybel_0(X1)
% 1.68/0.99      | ~ v4_orders_2(X1)
% 1.68/0.99      | v2_struct_0(X0)
% 1.68/0.99      | v2_struct_0(X1)
% 1.68/0.99      | ~ l1_pre_topc(X0) ),
% 1.68/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_23,negated_conjecture,
% 1.68/0.99      ( v2_pre_topc(sK0) ),
% 1.68/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_445,plain,
% 1.68/0.99      ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.68/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 1.68/0.99      | ~ l1_waybel_0(X1,X0)
% 1.68/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.68/0.99      | ~ v7_waybel_0(X1)
% 1.68/0.99      | ~ v4_orders_2(X1)
% 1.68/0.99      | v2_struct_0(X0)
% 1.68/0.99      | v2_struct_0(X1)
% 1.68/0.99      | ~ l1_pre_topc(X0)
% 1.68/0.99      | sK0 != X0 ),
% 1.68/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_446,plain,
% 1.68/1.00      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.68/1.00      | r2_hidden(X1,k10_yellow_6(sK0,X0))
% 1.68/1.00      | ~ l1_waybel_0(X0,sK0)
% 1.68/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.68/1.00      | ~ v7_waybel_0(X0)
% 1.68/1.00      | ~ v4_orders_2(X0)
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | v2_struct_0(sK0)
% 1.68/1.00      | ~ l1_pre_topc(sK0) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_445]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_450,plain,
% 1.68/1.00      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.68/1.00      | r2_hidden(X1,k10_yellow_6(sK0,X0))
% 1.68/1.00      | ~ l1_waybel_0(X0,sK0)
% 1.68/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.68/1.00      | ~ v7_waybel_0(X0)
% 1.68/1.00      | ~ v4_orders_2(X0)
% 1.68/1.00      | v2_struct_0(X0) ),
% 1.68/1.00      inference(global_propositional_subsumption,
% 1.68/1.00                [status(thm)],
% 1.68/1.00                [c_446,c_24,c_22]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_830,plain,
% 1.68/1.00      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.68/1.00      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ l1_waybel_0(X0,sK0)
% 1.68/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.68/1.00      | ~ v7_waybel_0(X0)
% 1.68/1.00      | ~ v4_orders_2(X0)
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0)
% 1.68/1.00      | sK2 != X1 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_176,c_450]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_831,plain,
% 1.68/1.00      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
% 1.68/1.00      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ l1_waybel_0(X0,sK0)
% 1.68/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 1.68/1.00      | ~ v7_waybel_0(X0)
% 1.68/1.00      | ~ v4_orders_2(X0)
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_830]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_16,negated_conjecture,
% 1.68/1.00      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 1.68/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_835,plain,
% 1.68/1.00      ( ~ l1_waybel_0(X0,sK0)
% 1.68/1.00      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
% 1.68/1.00      | ~ v7_waybel_0(X0)
% 1.68/1.00      | ~ v4_orders_2(X0)
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
% 1.68/1.00      inference(global_propositional_subsumption,[status(thm)],[c_831,c_16]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_836,plain,
% 1.68/1.00      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
% 1.68/1.00      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ l1_waybel_0(X0,sK0)
% 1.68/1.00      | ~ v7_waybel_0(X0)
% 1.68/1.00      | ~ v4_orders_2(X0)
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
% 1.68/1.00      inference(renaming,[status(thm)],[c_835]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_5,plain,
% 1.68/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.68/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.68/1.00      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 1.68/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.68/1.00      | v2_struct_0(X2)
% 1.68/1.00      | v1_xboole_0(X1)
% 1.68/1.00      | v1_xboole_0(X0)
% 1.68/1.00      | ~ l1_struct_0(X2) ),
% 1.68/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1243,plain,
% 1.68/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.68/1.00      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 1.68/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.68/1.00      | v2_struct_0(X2)
% 1.68/1.00      | v1_xboole_0(X1)
% 1.68/1.00      | v1_xboole_0(X0)
% 1.68/1.00      | ~ l1_struct_0(X2)
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.68/1.00      | sK1 != X0 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_18]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1244,plain,
% 1.68/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.68/1.00      | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/1.00      | v2_struct_0(X1)
% 1.68/1.00      | v1_xboole_0(X0)
% 1.68/1.00      | v1_xboole_0(sK1)
% 1.68/1.00      | ~ l1_struct_0(X1)
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_1243]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1248,plain,
% 1.68/1.00      ( v1_xboole_0(X0)
% 1.68/1.00      | v2_struct_0(X1)
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/1.00      | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
% 1.68/1.00      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.68/1.00      | ~ l1_struct_0(X1)
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1244,c_21]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1249,plain,
% 1.68/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.68/1.00      | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/1.00      | v2_struct_0(X1)
% 1.68/1.00      | v1_xboole_0(X0)
% 1.68/1.00      | ~ l1_struct_0(X1)
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/1.00      inference(renaming,[status(thm)],[c_1248]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1704,plain,
% 1.68/1.00      ( l1_waybel_0(k3_yellow19(X0,X1,sK1),X0)
% 1.68/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | v1_xboole_0(X1)
% 1.68/1.00      | ~ l1_struct_0(X0)
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.68/1.00      | sK1 != sK1 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_1249]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1862,plain,
% 1.68/1.00      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
% 1.68/1.00      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.68/1.00      | ~ v7_waybel_0(X0)
% 1.68/1.00      | ~ v4_orders_2(X0)
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | v2_struct_0(X2)
% 1.68/1.00      | v1_xboole_0(X1)
% 1.68/1.00      | ~ l1_struct_0(X2)
% 1.68/1.00      | k3_yellow19(X2,X1,sK1) != X0
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0)
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.68/1.00      | sK1 != sK1
% 1.68/1.00      | sK0 != X2 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_836,c_1704]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1863,plain,
% 1.68/1.00      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.68/1.00      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | v2_struct_0(sK0)
% 1.68/1.00      | v1_xboole_0(X0)
% 1.68/1.00      | ~ l1_struct_0(sK0)
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_1862]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_65,plain,
% 1.68/1.00      ( ~ l1_pre_topc(sK0) | l1_struct_0(sK0) ),
% 1.68/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1867,plain,
% 1.68/1.00      ( v1_xboole_0(X0)
% 1.68/1.00      | ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.68/1.00      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/1.00      inference(global_propositional_subsumption,
% 1.68/1.00                [status(thm)],
% 1.68/1.00                [c_1863,c_24,c_22,c_65]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1868,plain,
% 1.68/1.00      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.68/1.00      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | v1_xboole_0(X0)
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/1.00      inference(renaming,[status(thm)],[c_1867]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2087,plain,
% 1.68/1.00      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.68/1.00      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | v1_xboole_0(X0)
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_2001,c_1868]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2102,plain,
% 1.68/1.00      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.68/1.00      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | v1_xboole_0(X0)
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_2028,c_2087]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2119,plain,
% 1.68/1.00      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.68/1.00      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/1.00      | v1_xboole_0(X0)
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.68/1.00      inference(resolution,[status(thm)],[c_2055,c_2102]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_4,plain,
% 1.68/1.00      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 1.68/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1979,plain,
% 1.68/1.00      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK0 != X0 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_495]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1980,plain,
% 1.68/1.00      ( v2_struct_0(sK0) | ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_1979]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_62,plain,
% 1.68/1.00      ( v2_struct_0(sK0)
% 1.68/1.00      | ~ v1_xboole_0(u1_struct_0(sK0))
% 1.68/1.00      | ~ l1_struct_0(sK0) ),
% 1.68/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1982,plain,
% 1.68/1.00      ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 1.68/1.00      inference(global_propositional_subsumption,
% 1.68/1.00                [status(thm)],
% 1.68/1.00                [c_1980,c_24,c_22,c_62,c_65]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2270,plain,
% 1.68/1.00      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.68/1.00      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.68/1.00      | u1_struct_0(sK0) != X0 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_2119,c_1982]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2271,plain,
% 1.68/1.00      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,u1_struct_0(sK0),sK1)),sK2)
% 1.68/1.00      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,u1_struct_0(sK0),sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0)))
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_2270]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2532,plain,
% 1.68/1.00      ( k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,u1_struct_0(sK0),sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0)))
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))
% 1.68/1.00      | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,u1_struct_0(sK0),sK1)),sK2) != iProver_top
% 1.68/1.00      | r2_waybel_7(sK0,sK1,sK2) != iProver_top
% 1.68/1.00      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.68/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
% 1.68/1.00      inference(predicate_to_equality,[status(thm)],[c_2271]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2,plain,
% 1.68/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.68/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1990,plain,
% 1.68/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_495]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1991,plain,
% 1.68/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_1990]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_13,plain,
% 1.68/1.00      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 1.68/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.68/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.68/1.00      | v2_struct_0(X1)
% 1.68/1.00      | v1_xboole_0(X0)
% 1.68/1.00      | ~ l1_struct_0(X1)
% 1.68/1.00      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 1.68/1.00      inference(cnf_transformation,[],[f73]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_361,plain,
% 1.68/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.68/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.68/1.00      | v2_struct_0(X1)
% 1.68/1.00      | v1_xboole_0(X0)
% 1.68/1.00      | ~ l1_struct_0(X1)
% 1.68/1.00      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.68/1.00      | sK1 != X0 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_362,plain,
% 1.68/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.68/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | v1_xboole_0(sK1)
% 1.68/1.00      | ~ l1_struct_0(X0)
% 1.68/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_361]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_366,plain,
% 1.68/1.00      ( v2_struct_0(X0)
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.68/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.68/1.00      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.68/1.00      | ~ l1_struct_0(X0)
% 1.68/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.68/1.00      inference(global_propositional_subsumption,[status(thm)],[c_362,c_21]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_367,plain,
% 1.68/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.68/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | ~ l1_struct_0(X0)
% 1.68/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.68/1.00      inference(renaming,[status(thm)],[c_366]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1314,plain,
% 1.68/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | ~ l1_struct_0(X0)
% 1.68/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.68/1.00      | sK1 != sK1 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_367]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1791,plain,
% 1.68/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | ~ l1_struct_0(X0)
% 1.68/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.68/1.00      | sK1 != sK1 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_1314]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1968,plain,
% 1.68/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.68/1.00      | sK1 != sK1
% 1.68/1.00      | sK0 != X0 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_1791,c_495]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1969,plain,
% 1.68/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 1.68/1.00      | v2_struct_0(sK0)
% 1.68/1.00      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_1968]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_17,negated_conjecture,
% 1.68/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
% 1.68/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_369,plain,
% 1.68/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.68/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 1.68/1.00      | v2_struct_0(sK0)
% 1.68/1.00      | ~ l1_struct_0(sK0)
% 1.68/1.00      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.68/1.00      inference(instantiation,[status(thm)],[c_367]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1971,plain,
% 1.68/1.00      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.68/1.00      inference(global_propositional_subsumption,
% 1.68/1.00                [status(thm)],
% 1.68/1.00                [c_1969,c_24,c_22,c_19,c_18,c_17,c_65,c_369]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2338,plain,
% 1.68/1.00      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
% 1.68/1.00      inference(equality_resolution_simp,[status(thm)],[c_1971]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2603,plain,
% 1.68/1.00      ( k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.68/1.00      | r2_waybel_7(sK0,sK1,sK2) != iProver_top
% 1.68/1.00      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.68/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
% 1.68/1.00      inference(light_normalisation,[status(thm)],[c_2532,c_1991,c_2338]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2604,plain,
% 1.68/1.00      ( r2_waybel_7(sK0,sK1,sK2) != iProver_top
% 1.68/1.00      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.68/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
% 1.68/1.00      inference(equality_resolution_simp,[status(thm)],[c_2603]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2536,plain,
% 1.68/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) = iProver_top ),
% 1.68/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1,plain,
% 1.68/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.68/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2538,plain,
% 1.68/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_0,plain,
% 1.68/1.00      ( k2_subset_1(X0) = X0 ),
% 1.68/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2546,plain,
% 1.68/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.68/1.00      inference(light_normalisation,[status(thm)],[c_2538,c_0]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_15,negated_conjecture,
% 1.68/1.00      ( r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
% 1.68/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_178,plain,
% 1.68/1.00      ( r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
% 1.68/1.00      inference(prop_impl,[status(thm)],[c_15]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_12,plain,
% 1.68/1.00      ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.68/1.00      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 1.68/1.00      | ~ l1_waybel_0(X1,X0)
% 1.68/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.68/1.00      | ~ v2_pre_topc(X0)
% 1.68/1.00      | ~ v7_waybel_0(X1)
% 1.68/1.00      | ~ v4_orders_2(X1)
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | v2_struct_0(X1)
% 1.68/1.00      | ~ l1_pre_topc(X0) ),
% 1.68/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_412,plain,
% 1.68/1.00      ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.68/1.00      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 1.68/1.00      | ~ l1_waybel_0(X1,X0)
% 1.68/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.68/1.00      | ~ v7_waybel_0(X1)
% 1.68/1.00      | ~ v4_orders_2(X1)
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | v2_struct_0(X1)
% 1.68/1.00      | ~ l1_pre_topc(X0)
% 1.68/1.00      | sK0 != X0 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_413,plain,
% 1.68/1.00      ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.68/1.00      | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
% 1.68/1.00      | ~ l1_waybel_0(X0,sK0)
% 1.68/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.68/1.00      | ~ v7_waybel_0(X0)
% 1.68/1.00      | ~ v4_orders_2(X0)
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | v2_struct_0(sK0)
% 1.68/1.00      | ~ l1_pre_topc(sK0) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_412]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_417,plain,
% 1.68/1.00      ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.68/1.00      | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
% 1.68/1.00      | ~ l1_waybel_0(X0,sK0)
% 1.68/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.68/1.00      | ~ v7_waybel_0(X0)
% 1.68/1.00      | ~ v4_orders_2(X0)
% 1.68/1.00      | v2_struct_0(X0) ),
% 1.68/1.00      inference(global_propositional_subsumption,
% 1.68/1.00                [status(thm)],
% 1.68/1.00                [c_413,c_24,c_22]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_797,plain,
% 1.68/1.00      ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.68/1.00      | r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ l1_waybel_0(X0,sK0)
% 1.68/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.68/1.00      | ~ v7_waybel_0(X0)
% 1.68/1.00      | ~ v4_orders_2(X0)
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0)
% 1.68/1.00      | sK2 != X1 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_178,c_417]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_798,plain,
% 1.68/1.00      ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
% 1.68/1.00      | r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ l1_waybel_0(X0,sK0)
% 1.68/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 1.68/1.00      | ~ v7_waybel_0(X0)
% 1.68/1.00      | ~ v4_orders_2(X0)
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_797]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_802,plain,
% 1.68/1.00      ( ~ l1_waybel_0(X0,sK0)
% 1.68/1.00      | r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
% 1.68/1.00      | ~ v7_waybel_0(X0)
% 1.68/1.00      | ~ v4_orders_2(X0)
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
% 1.68/1.00      inference(global_propositional_subsumption,[status(thm)],[c_798,c_16]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_803,plain,
% 1.68/1.00      ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
% 1.68/1.00      | r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ l1_waybel_0(X0,sK0)
% 1.68/1.00      | ~ v7_waybel_0(X0)
% 1.68/1.00      | ~ v4_orders_2(X0)
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
% 1.68/1.00      inference(renaming,[status(thm)],[c_802]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1904,plain,
% 1.68/1.00      ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
% 1.68/1.00      | r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.68/1.00      | ~ v7_waybel_0(X0)
% 1.68/1.00      | ~ v4_orders_2(X0)
% 1.68/1.00      | v2_struct_0(X0)
% 1.68/1.00      | v2_struct_0(X2)
% 1.68/1.00      | v1_xboole_0(X1)
% 1.68/1.00      | ~ l1_struct_0(X2)
% 1.68/1.00      | k3_yellow19(X2,X1,sK1) != X0
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0)
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.68/1.00      | sK1 != sK1
% 1.68/1.00      | sK0 != X2 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_803,c_1704]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1905,plain,
% 1.68/1.00      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.68/1.00      | r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | v2_struct_0(sK0)
% 1.68/1.00      | v1_xboole_0(X0)
% 1.68/1.00      | ~ l1_struct_0(sK0)
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_1904]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1909,plain,
% 1.68/1.00      ( v1_xboole_0(X0)
% 1.68/1.00      | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.68/1.00      | r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/1.00      inference(global_propositional_subsumption,
% 1.68/1.00                [status(thm)],
% 1.68/1.00                [c_1905,c_24,c_22,c_65]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1910,plain,
% 1.68/1.00      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.68/1.00      | r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | v1_xboole_0(X0)
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/1.00      inference(renaming,[status(thm)],[c_1909]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2088,plain,
% 1.68/1.00      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.68/1.00      | r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | v1_xboole_0(X0)
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_2001,c_1910]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2101,plain,
% 1.68/1.00      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.68/1.00      | r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | v1_xboole_0(X0)
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.68/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_2028,c_2088]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2148,plain,
% 1.68/1.00      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.68/1.00      | r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/1.00      | v1_xboole_0(X0)
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.68/1.00      inference(resolution,[status(thm)],[c_2055,c_2101]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2245,plain,
% 1.68/1.00      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.68/1.00      | r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.68/1.00      | u1_struct_0(sK0) != X0 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_2148,c_1982]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2246,plain,
% 1.68/1.00      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,u1_struct_0(sK0),sK1)),sK2)
% 1.68/1.00      | r2_waybel_7(sK0,sK1,sK2)
% 1.68/1.00      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.68/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.68/1.00      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,u1_struct_0(sK0),sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0)))
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_2245]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2533,plain,
% 1.68/1.00      ( k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,u1_struct_0(sK0),sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0)))
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))
% 1.68/1.00      | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,u1_struct_0(sK0),sK1)),sK2) = iProver_top
% 1.68/1.00      | r2_waybel_7(sK0,sK1,sK2) = iProver_top
% 1.68/1.00      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.68/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
% 1.68/1.00      inference(predicate_to_equality,[status(thm)],[c_2246]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2583,plain,
% 1.68/1.00      ( k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.68/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.68/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.68/1.00      | r2_waybel_7(sK0,sK1,sK2) = iProver_top
% 1.68/1.00      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.68/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
% 1.68/1.00      inference(light_normalisation,[status(thm)],[c_2533,c_1991,c_2338]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2584,plain,
% 1.68/1.00      ( r2_waybel_7(sK0,sK1,sK2) = iProver_top
% 1.68/1.00      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.68/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
% 1.68/1.00      inference(equality_resolution_simp,[status(thm)],[c_2583]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2588,plain,
% 1.68/1.00      ( r2_waybel_7(sK0,sK1,sK2) = iProver_top ),
% 1.68/1.00      inference(forward_subsumption_resolution,
% 1.68/1.00                [status(thm)],
% 1.68/1.00                [c_2584,c_2536,c_2546]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2608,plain,
% 1.68/1.00      ( $false ),
% 1.68/1.00      inference(forward_subsumption_resolution,
% 1.68/1.00                [status(thm)],
% 1.68/1.00                [c_2604,c_2536,c_2546,c_2588]) ).
% 1.68/1.00  
% 1.68/1.00  
% 1.68/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.68/1.00  
% 1.68/1.00  ------                               Statistics
% 1.68/1.00  
% 1.68/1.00  ------ General
% 1.68/1.00  
% 1.68/1.00  abstr_ref_over_cycles:                  0
% 1.68/1.00  abstr_ref_under_cycles:                 0
% 1.68/1.00  gc_basic_clause_elim:                   0
% 1.68/1.00  forced_gc_time:                         0
% 1.68/1.00  parsing_time:                           0.008
% 1.68/1.00  unif_index_cands_time:                  0.
% 1.68/1.00  unif_index_add_time:                    0.
% 1.68/1.00  orderings_time:                         0.
% 1.68/1.00  out_proof_time:                         0.015
% 1.68/1.00  total_time:                             0.123
% 1.68/1.00  num_of_symbols:                         57
% 1.68/1.00  num_of_terms:                           1223
% 1.68/1.00  
% 1.68/1.00  ------ Preprocessing
% 1.68/1.00  
% 1.68/1.00  num_of_splits:                          0
% 1.68/1.00  num_of_split_atoms:                     0
% 1.68/1.00  num_of_reused_defs:                     0
% 1.68/1.00  num_eq_ax_congr_red:                    6
% 1.68/1.00  num_of_sem_filtered_clauses:            1
% 1.68/1.00  num_of_subtypes:                        0
% 1.68/1.00  monotx_restored_types:                  0
% 1.68/1.00  sat_num_of_epr_types:                   0
% 1.68/1.00  sat_num_of_non_cyclic_types:            0
% 1.68/1.00  sat_guarded_non_collapsed_types:        0
% 1.68/1.00  num_pure_diseq_elim:                    0
% 1.68/1.00  simp_replaced_by:                       0
% 1.68/1.00  res_preprocessed:                       78
% 1.68/1.00  prep_upred:                             0
% 1.68/1.00  prep_unflattend:                        48
% 1.68/1.00  smt_new_axioms:                         0
% 1.68/1.00  pred_elim_cands:                        2
% 1.68/1.00  pred_elim:                              12
% 1.68/1.00  pred_elim_cl:                           13
% 1.68/1.00  pred_elim_cycles:                       23
% 1.68/1.00  merged_defs:                            2
% 1.68/1.00  merged_defs_ncl:                        0
% 1.68/1.00  bin_hyper_res:                          2
% 1.68/1.00  prep_cycles:                            4
% 1.68/1.00  pred_elim_time:                         0.062
% 1.68/1.00  splitting_time:                         0.
% 1.68/1.00  sem_filter_time:                        0.
% 1.68/1.00  monotx_time:                            0.
% 1.68/1.00  subtype_inf_time:                       0.
% 1.68/1.00  
% 1.68/1.00  ------ Problem properties
% 1.68/1.00  
% 1.68/1.00  clauses:                                10
% 1.68/1.00  conjectures:                            2
% 1.68/1.00  epr:                                    0
% 1.68/1.00  horn:                                   8
% 1.68/1.00  ground:                                 8
% 1.68/1.00  unary:                                  6
% 1.68/1.00  binary:                                 0
% 1.68/1.00  lits:                                   34
% 1.68/1.00  lits_eq:                                15
% 1.68/1.00  fd_pure:                                0
% 1.68/1.00  fd_pseudo:                              0
% 1.68/1.00  fd_cond:                                0
% 1.68/1.00  fd_pseudo_cond:                         0
% 1.68/1.00  ac_symbols:                             0
% 1.68/1.00  
% 1.68/1.00  ------ Propositional Solver
% 1.68/1.00  
% 1.68/1.00  prop_solver_calls:                      21
% 1.68/1.00  prop_fast_solver_calls:                 1198
% 1.68/1.00  smt_solver_calls:                       0
% 1.68/1.00  smt_fast_solver_calls:                  0
% 1.68/1.00  prop_num_of_clauses:                    408
% 1.68/1.00  prop_preprocess_simplified:             1657
% 1.68/1.00  prop_fo_subsumed:                       35
% 1.68/1.00  prop_solver_time:                       0.
% 1.68/1.00  smt_solver_time:                        0.
% 1.68/1.00  smt_fast_solver_time:                   0.
% 1.68/1.00  prop_fast_solver_time:                  0.
% 1.68/1.00  prop_unsat_core_time:                   0.
% 1.68/1.00  
% 1.68/1.00  ------ QBF
% 1.68/1.00  
% 1.68/1.00  qbf_q_res:                              0
% 1.68/1.00  qbf_num_tautologies:                    0
% 1.68/1.00  qbf_prep_cycles:                        0
% 1.68/1.00  
% 1.68/1.00  ------ BMC1
% 1.68/1.00  
% 1.68/1.00  bmc1_current_bound:                     -1
% 1.68/1.00  bmc1_last_solved_bound:                 -1
% 1.68/1.00  bmc1_unsat_core_size:                   -1
% 1.68/1.00  bmc1_unsat_core_parents_size:           -1
% 1.68/1.00  bmc1_merge_next_fun:                    0
% 1.68/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.68/1.00  
% 1.68/1.00  ------ Instantiation
% 1.68/1.00  
% 1.68/1.00  inst_num_of_clauses:                    22
% 1.68/1.00  inst_num_in_passive:                    0
% 1.68/1.00  inst_num_in_active:                     0
% 1.68/1.00  inst_num_in_unprocessed:                22
% 1.68/1.00  inst_num_of_loops:                      0
% 1.68/1.00  inst_num_of_learning_restarts:          0
% 1.68/1.00  inst_num_moves_active_passive:          0
% 1.68/1.00  inst_lit_activity:                      0
% 1.68/1.00  inst_lit_activity_moves:                0
% 1.68/1.00  inst_num_tautologies:                   0
% 1.68/1.00  inst_num_prop_implied:                  0
% 1.68/1.00  inst_num_existing_simplified:           0
% 1.68/1.00  inst_num_eq_res_simplified:             0
% 1.68/1.00  inst_num_child_elim:                    0
% 1.68/1.00  inst_num_of_dismatching_blockings:      0
% 1.68/1.00  inst_num_of_non_proper_insts:           0
% 1.68/1.00  inst_num_of_duplicates:                 0
% 1.68/1.00  inst_inst_num_from_inst_to_res:         0
% 1.68/1.00  inst_dismatching_checking_time:         0.
% 1.68/1.00  
% 1.68/1.00  ------ Resolution
% 1.68/1.00  
% 1.68/1.00  res_num_of_clauses:                     0
% 1.68/1.00  res_num_in_passive:                     0
% 1.68/1.00  res_num_in_active:                      0
% 1.68/1.00  res_num_of_loops:                       82
% 1.68/1.00  res_forward_subset_subsumed:            0
% 1.68/1.00  res_backward_subset_subsumed:           0
% 1.68/1.00  res_forward_subsumed:                   0
% 1.68/1.00  res_backward_subsumed:                  0
% 1.68/1.00  res_forward_subsumption_resolution:     10
% 1.68/1.00  res_backward_subsumption_resolution:    4
% 1.68/1.00  res_clause_to_clause_subsumption:       140
% 1.68/1.00  res_orphan_elimination:                 0
% 1.68/1.00  res_tautology_del:                      6
% 1.68/1.00  res_num_eq_res_simplified:              1
% 1.68/1.00  res_num_sel_changes:                    0
% 1.68/1.00  res_moves_from_active_to_pass:          0
% 1.68/1.00  
% 1.68/1.00  ------ Superposition
% 1.68/1.00  
% 1.68/1.00  sup_time_total:                         0.
% 1.68/1.00  sup_time_generating:                    0.
% 1.68/1.00  sup_time_sim_full:                      0.
% 1.68/1.00  sup_time_sim_immed:                     0.
% 1.68/1.00  
% 1.68/1.00  sup_num_of_clauses:                     0
% 1.68/1.00  sup_num_in_active:                      0
% 1.68/1.00  sup_num_in_passive:                     0
% 1.68/1.00  sup_num_of_loops:                       0
% 1.68/1.00  sup_fw_superposition:                   0
% 1.68/1.00  sup_bw_superposition:                   0
% 1.68/1.00  sup_immediate_simplified:               0
% 1.68/1.00  sup_given_eliminated:                   0
% 1.68/1.00  comparisons_done:                       0
% 1.68/1.00  comparisons_avoided:                    0
% 1.68/1.00  
% 1.68/1.00  ------ Simplifications
% 1.68/1.00  
% 1.68/1.00  
% 1.68/1.00  sim_fw_subset_subsumed:                 0
% 1.68/1.00  sim_bw_subset_subsumed:                 0
% 1.68/1.00  sim_fw_subsumed:                        0
% 1.68/1.00  sim_bw_subsumed:                        1
% 1.68/1.00  sim_fw_subsumption_res:                 5
% 1.68/1.00  sim_bw_subsumption_res:                 1
% 1.68/1.00  sim_tautology_del:                      0
% 1.68/1.00  sim_eq_tautology_del:                   0
% 1.68/1.00  sim_eq_res_simp:                        2
% 1.68/1.00  sim_fw_demodulated:                     0
% 1.68/1.00  sim_bw_demodulated:                     0
% 1.68/1.00  sim_light_normalised:                   6
% 1.68/1.00  sim_joinable_taut:                      0
% 1.68/1.00  sim_joinable_simp:                      0
% 1.68/1.00  sim_ac_normalised:                      0
% 1.68/1.00  sim_smt_subsumption:                    0
% 1.68/1.00  
%------------------------------------------------------------------------------
