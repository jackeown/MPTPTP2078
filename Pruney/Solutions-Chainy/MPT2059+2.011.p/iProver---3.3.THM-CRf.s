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
% DateTime   : Thu Dec  3 12:29:21 EST 2020

% Result     : Theorem 1.43s
% Output     : CNFRefutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  181 (1399 expanded)
%              Number of clauses        :  123 ( 309 expanded)
%              Number of leaves         :   12 ( 382 expanded)
%              Depth                    :   32
%              Number of atoms          : 1204 (14261 expanded)
%              Number of equality atoms :  166 ( 294 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   26 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36,f35,f34])).

fof(f55,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
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

fof(f12,plain,(
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
    inference(pure_predicate_removal,[],[f6])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
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

fof(f13,plain,(
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
    inference(pure_predicate_removal,[],[f4])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
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

fof(f11,plain,(
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
    inference(pure_predicate_removal,[],[f5])).

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
     => ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f31])).

cnf(c_17,negated_conjecture,
    ( v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_16,negated_conjecture,
    ( v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_7,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_18,negated_conjecture,
    ( v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_306,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_307,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X1)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_19,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_311,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(X0))
    | ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ l1_struct_0(X1)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_307,c_19])).

cnf(c_312,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_311])).

cnf(c_1263,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_312])).

cnf(c_1656,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1263])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_478,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_20])).

cnf(c_479,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_2035,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0))
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1656,c_479])).

cnf(c_2036,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_2035])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2040,plain,
    ( v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2036,c_22])).

cnf(c_2041,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_2040])).

cnf(c_4,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1191,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_16])).

cnf(c_1192,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(unflattening,[status(thm)],[c_1191])).

cnf(c_1196,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1192,c_19])).

cnf(c_1197,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(renaming,[status(thm)],[c_1196])).

cnf(c_1717,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1197])).

cnf(c_2008,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1717,c_479])).

cnf(c_2009,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(unflattening,[status(thm)],[c_2008])).

cnf(c_2013,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2009,c_22])).

cnf(c_2014,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(renaming,[status(thm)],[c_2013])).

cnf(c_5,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1155,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_16])).

cnf(c_1156,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v4_orders_2(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(unflattening,[status(thm)],[c_1155])).

cnf(c_1160,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(X1)
    | v4_orders_2(k3_yellow19(X1,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1156,c_19])).

cnf(c_1161,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v4_orders_2(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(renaming,[status(thm)],[c_1160])).

cnf(c_1746,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v4_orders_2(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1161])).

cnf(c_1981,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v4_orders_2(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1746,c_479])).

cnf(c_1982,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(unflattening,[status(thm)],[c_1981])).

cnf(c_1986,plain,
    ( v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1982,c_22])).

cnf(c_1987,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(renaming,[status(thm)],[c_1986])).

cnf(c_12,negated_conjecture,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_166,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f48])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_429,plain,
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
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_430,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_434,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_22,c_20])).

cnf(c_814,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_166,c_434])).

cnf(c_815,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_814])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_819,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_815,c_14])).

cnf(c_820,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(X0,sK0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
    inference(renaming,[status(thm)],[c_819])).

cnf(c_3,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1227,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_1228,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(unflattening,[status(thm)],[c_1227])).

cnf(c_1232,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1228,c_19])).

cnf(c_1233,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(renaming,[status(thm)],[c_1232])).

cnf(c_1688,plain,
    ( l1_waybel_0(k3_yellow19(X0,X1,sK1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v2_struct_0(X0)
    | v1_xboole_0(X1)
    | ~ l1_struct_0(X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1233])).

cnf(c_1846,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | ~ l1_struct_0(X2)
    | k3_yellow19(X2,X1,sK1) != X0
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
    | sK1 != sK1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_820,c_1688])).

cnf(c_1847,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(sK0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(unflattening,[status(thm)],[c_1846])).

cnf(c_63,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1851,plain,
    ( v1_xboole_0(X0)
    | ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1847,c_22,c_20,c_63])).

cnf(c_1852,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(renaming,[status(thm)],[c_1851])).

cnf(c_2074,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1987,c_1852])).

cnf(c_2089,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2014,c_2074])).

cnf(c_2106,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0)) ),
    inference(resolution,[status(thm)],[c_2041,c_2089])).

cnf(c_2,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1963,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_479])).

cnf(c_1964,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_1963])).

cnf(c_60,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1966,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1964,c_22,c_20,c_60,c_63])).

cnf(c_2255,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0))
    | k2_struct_0(sK0) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2106,c_1966])).

cnf(c_2256,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0))
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2255])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_0,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_66,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2258,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0))
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2256,c_20,c_15,c_63,c_66])).

cnf(c_2313,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_2258])).

cnf(c_2332,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) ),
    inference(prop_impl,[status(thm)],[c_2313])).

cnf(c_2333,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2) ),
    inference(renaming,[status(thm)],[c_2332])).

cnf(c_2388,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r2_waybel_7(sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_2333])).

cnf(c_2676,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) != iProver_top
    | r2_waybel_7(sK0,sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2388])).

cnf(c_11,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_345,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | u1_struct_0(k3_yellow_1(k2_struct_0(X1))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_346,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | v2_struct_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_yellow_1(k2_struct_0(X0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_350,plain,
    ( v2_struct_0(X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_yellow_1(k2_struct_0(X0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_346,c_19])).

cnf(c_351,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_yellow_1(k2_struct_0(X0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_350])).

cnf(c_1298,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | k3_yellow_1(k2_struct_0(X0)) != k3_yellow_1(k2_struct_0(sK0))
    | u1_struct_0(k3_yellow_1(k2_struct_0(X0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_351])).

cnf(c_1775,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | k3_yellow_1(k2_struct_0(X0)) != k3_yellow_1(k2_struct_0(sK0))
    | u1_struct_0(k3_yellow_1(k2_struct_0(X0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1298])).

cnf(c_1952,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | k3_yellow_1(k2_struct_0(X0)) != k3_yellow_1(k2_struct_0(sK0))
    | u1_struct_0(k3_yellow_1(k2_struct_0(X0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))
    | sK1 != sK1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1775,c_479])).

cnf(c_1953,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0))
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_1952])).

cnf(c_353,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_1955,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1953,c_22,c_20,c_17,c_16,c_15,c_63,c_353])).

cnf(c_2320,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_1955])).

cnf(c_2386,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
    inference(subtyping,[status(esa)],[c_2320])).

cnf(c_2689,plain,
    ( r2_waybel_7(sK0,sK1,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2676,c_2386])).

cnf(c_13,negated_conjecture,
    ( r2_waybel_7(sK0,sK1,sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_168,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_10,plain,
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
    inference(cnf_transformation,[],[f47])).

cnf(c_396,plain,
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
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_397,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_401,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_22,c_20])).

cnf(c_781,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_168,c_401])).

cnf(c_782,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_781])).

cnf(c_786,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | r2_waybel_7(sK0,sK1,sK2)
    | r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_782,c_14])).

cnf(c_787,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(X0,sK0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
    inference(renaming,[status(thm)],[c_786])).

cnf(c_1888,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | ~ l1_struct_0(X2)
    | k3_yellow19(X2,X1,sK1) != X0
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0)
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
    | sK1 != sK1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_787,c_1688])).

cnf(c_1889,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(sK0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(unflattening,[status(thm)],[c_1888])).

cnf(c_1893,plain,
    ( v1_xboole_0(X0)
    | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1889,c_22,c_20,c_63])).

cnf(c_1894,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(renaming,[status(thm)],[c_1893])).

cnf(c_2075,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1987,c_1894])).

cnf(c_2088,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2014,c_2075])).

cnf(c_2135,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0)) ),
    inference(resolution,[status(thm)],[c_2041,c_2088])).

cnf(c_2232,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0))
    | k2_struct_0(sK0) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2135,c_1966])).

cnf(c_2233,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0))
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2232])).

cnf(c_2235,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0))
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2233,c_20,c_15,c_63,c_66])).

cnf(c_2315,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_2235])).

cnf(c_2334,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) ),
    inference(prop_impl,[status(thm)],[c_2315])).

cnf(c_2335,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2) ),
    inference(renaming,[status(thm)],[c_2334])).

cnf(c_2387,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r2_waybel_7(sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_2335])).

cnf(c_2677,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) = iProver_top
    | r2_waybel_7(sK0,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2387])).

cnf(c_2686,plain,
    ( r2_waybel_7(sK0,sK1,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2677,c_2386])).

cnf(c_2691,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2689,c_2686])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.43/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.43/0.98  
% 1.43/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.43/0.98  
% 1.43/0.98  ------  iProver source info
% 1.43/0.98  
% 1.43/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.43/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.43/0.98  git: non_committed_changes: false
% 1.43/0.98  git: last_make_outside_of_git: false
% 1.43/0.98  
% 1.43/0.98  ------ 
% 1.43/0.98  
% 1.43/0.98  ------ Input Options
% 1.43/0.98  
% 1.43/0.98  --out_options                           all
% 1.43/0.98  --tptp_safe_out                         true
% 1.43/0.98  --problem_path                          ""
% 1.43/0.98  --include_path                          ""
% 1.43/0.98  --clausifier                            res/vclausify_rel
% 1.43/0.98  --clausifier_options                    --mode clausify
% 1.43/0.98  --stdin                                 false
% 1.43/0.98  --stats_out                             all
% 1.43/0.98  
% 1.43/0.98  ------ General Options
% 1.43/0.98  
% 1.43/0.98  --fof                                   false
% 1.43/0.98  --time_out_real                         305.
% 1.43/0.98  --time_out_virtual                      -1.
% 1.43/0.98  --symbol_type_check                     false
% 1.43/0.98  --clausify_out                          false
% 1.43/0.98  --sig_cnt_out                           false
% 1.43/0.98  --trig_cnt_out                          false
% 1.43/0.98  --trig_cnt_out_tolerance                1.
% 1.43/0.98  --trig_cnt_out_sk_spl                   false
% 1.43/0.98  --abstr_cl_out                          false
% 1.43/0.98  
% 1.43/0.98  ------ Global Options
% 1.43/0.98  
% 1.43/0.98  --schedule                              default
% 1.43/0.98  --add_important_lit                     false
% 1.43/0.98  --prop_solver_per_cl                    1000
% 1.43/0.98  --min_unsat_core                        false
% 1.43/0.98  --soft_assumptions                      false
% 1.43/0.98  --soft_lemma_size                       3
% 1.43/0.98  --prop_impl_unit_size                   0
% 1.43/0.98  --prop_impl_unit                        []
% 1.43/0.98  --share_sel_clauses                     true
% 1.43/0.98  --reset_solvers                         false
% 1.43/0.98  --bc_imp_inh                            [conj_cone]
% 1.43/0.98  --conj_cone_tolerance                   3.
% 1.43/0.98  --extra_neg_conj                        none
% 1.43/0.98  --large_theory_mode                     true
% 1.43/0.98  --prolific_symb_bound                   200
% 1.43/0.98  --lt_threshold                          2000
% 1.43/0.98  --clause_weak_htbl                      true
% 1.43/0.98  --gc_record_bc_elim                     false
% 1.43/0.98  
% 1.43/0.98  ------ Preprocessing Options
% 1.43/0.98  
% 1.43/0.98  --preprocessing_flag                    true
% 1.43/0.98  --time_out_prep_mult                    0.1
% 1.43/0.98  --splitting_mode                        input
% 1.43/0.98  --splitting_grd                         true
% 1.43/0.98  --splitting_cvd                         false
% 1.43/0.98  --splitting_cvd_svl                     false
% 1.43/0.98  --splitting_nvd                         32
% 1.43/0.98  --sub_typing                            true
% 1.43/0.98  --prep_gs_sim                           true
% 1.43/0.98  --prep_unflatten                        true
% 1.43/0.98  --prep_res_sim                          true
% 1.43/0.98  --prep_upred                            true
% 1.43/0.98  --prep_sem_filter                       exhaustive
% 1.43/0.98  --prep_sem_filter_out                   false
% 1.43/0.98  --pred_elim                             true
% 1.43/0.98  --res_sim_input                         true
% 1.43/0.98  --eq_ax_congr_red                       true
% 1.43/0.98  --pure_diseq_elim                       true
% 1.43/0.98  --brand_transform                       false
% 1.43/0.98  --non_eq_to_eq                          false
% 1.43/0.98  --prep_def_merge                        true
% 1.43/0.98  --prep_def_merge_prop_impl              false
% 1.43/0.98  --prep_def_merge_mbd                    true
% 1.43/0.98  --prep_def_merge_tr_red                 false
% 1.43/0.98  --prep_def_merge_tr_cl                  false
% 1.43/0.98  --smt_preprocessing                     true
% 1.43/0.98  --smt_ac_axioms                         fast
% 1.43/0.98  --preprocessed_out                      false
% 1.43/0.98  --preprocessed_stats                    false
% 1.43/0.98  
% 1.43/0.98  ------ Abstraction refinement Options
% 1.43/0.98  
% 1.43/0.98  --abstr_ref                             []
% 1.43/0.98  --abstr_ref_prep                        false
% 1.43/0.98  --abstr_ref_until_sat                   false
% 1.43/0.98  --abstr_ref_sig_restrict                funpre
% 1.43/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.43/0.98  --abstr_ref_under                       []
% 1.43/0.98  
% 1.43/0.98  ------ SAT Options
% 1.43/0.98  
% 1.43/0.98  --sat_mode                              false
% 1.43/0.98  --sat_fm_restart_options                ""
% 1.43/0.98  --sat_gr_def                            false
% 1.43/0.98  --sat_epr_types                         true
% 1.43/0.98  --sat_non_cyclic_types                  false
% 1.43/0.98  --sat_finite_models                     false
% 1.43/0.98  --sat_fm_lemmas                         false
% 1.43/0.98  --sat_fm_prep                           false
% 1.43/0.98  --sat_fm_uc_incr                        true
% 1.43/0.98  --sat_out_model                         small
% 1.43/0.98  --sat_out_clauses                       false
% 1.43/0.98  
% 1.43/0.98  ------ QBF Options
% 1.43/0.98  
% 1.43/0.98  --qbf_mode                              false
% 1.43/0.98  --qbf_elim_univ                         false
% 1.43/0.98  --qbf_dom_inst                          none
% 1.43/0.98  --qbf_dom_pre_inst                      false
% 1.43/0.98  --qbf_sk_in                             false
% 1.43/0.98  --qbf_pred_elim                         true
% 1.43/0.98  --qbf_split                             512
% 1.43/0.98  
% 1.43/0.98  ------ BMC1 Options
% 1.43/0.98  
% 1.43/0.98  --bmc1_incremental                      false
% 1.43/0.98  --bmc1_axioms                           reachable_all
% 1.43/0.98  --bmc1_min_bound                        0
% 1.43/0.98  --bmc1_max_bound                        -1
% 1.43/0.98  --bmc1_max_bound_default                -1
% 1.43/0.98  --bmc1_symbol_reachability              true
% 1.43/0.98  --bmc1_property_lemmas                  false
% 1.43/0.98  --bmc1_k_induction                      false
% 1.43/0.98  --bmc1_non_equiv_states                 false
% 1.43/0.98  --bmc1_deadlock                         false
% 1.43/0.98  --bmc1_ucm                              false
% 1.43/0.98  --bmc1_add_unsat_core                   none
% 1.43/0.98  --bmc1_unsat_core_children              false
% 1.43/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.43/0.98  --bmc1_out_stat                         full
% 1.43/0.98  --bmc1_ground_init                      false
% 1.43/0.98  --bmc1_pre_inst_next_state              false
% 1.43/0.98  --bmc1_pre_inst_state                   false
% 1.43/0.98  --bmc1_pre_inst_reach_state             false
% 1.43/0.98  --bmc1_out_unsat_core                   false
% 1.43/0.98  --bmc1_aig_witness_out                  false
% 1.43/0.98  --bmc1_verbose                          false
% 1.43/0.98  --bmc1_dump_clauses_tptp                false
% 1.43/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.43/0.98  --bmc1_dump_file                        -
% 1.43/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.43/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.43/0.98  --bmc1_ucm_extend_mode                  1
% 1.43/0.98  --bmc1_ucm_init_mode                    2
% 1.43/0.98  --bmc1_ucm_cone_mode                    none
% 1.43/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.43/0.98  --bmc1_ucm_relax_model                  4
% 1.43/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.43/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.43/0.98  --bmc1_ucm_layered_model                none
% 1.43/0.98  --bmc1_ucm_max_lemma_size               10
% 1.43/0.98  
% 1.43/0.98  ------ AIG Options
% 1.43/0.98  
% 1.43/0.98  --aig_mode                              false
% 1.43/0.98  
% 1.43/0.98  ------ Instantiation Options
% 1.43/0.98  
% 1.43/0.98  --instantiation_flag                    true
% 1.43/0.98  --inst_sos_flag                         false
% 1.43/0.98  --inst_sos_phase                        true
% 1.43/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.43/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.43/0.98  --inst_lit_sel_side                     num_symb
% 1.43/0.98  --inst_solver_per_active                1400
% 1.43/0.98  --inst_solver_calls_frac                1.
% 1.43/0.98  --inst_passive_queue_type               priority_queues
% 1.43/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.43/0.98  --inst_passive_queues_freq              [25;2]
% 1.43/0.98  --inst_dismatching                      true
% 1.43/0.98  --inst_eager_unprocessed_to_passive     true
% 1.43/0.98  --inst_prop_sim_given                   true
% 1.43/0.98  --inst_prop_sim_new                     false
% 1.43/0.98  --inst_subs_new                         false
% 1.43/0.98  --inst_eq_res_simp                      false
% 1.43/0.98  --inst_subs_given                       false
% 1.43/0.98  --inst_orphan_elimination               true
% 1.43/0.98  --inst_learning_loop_flag               true
% 1.43/0.98  --inst_learning_start                   3000
% 1.43/0.98  --inst_learning_factor                  2
% 1.43/0.98  --inst_start_prop_sim_after_learn       3
% 1.43/0.98  --inst_sel_renew                        solver
% 1.43/0.98  --inst_lit_activity_flag                true
% 1.43/0.98  --inst_restr_to_given                   false
% 1.43/0.98  --inst_activity_threshold               500
% 1.43/0.98  --inst_out_proof                        true
% 1.43/0.98  
% 1.43/0.98  ------ Resolution Options
% 1.43/0.98  
% 1.43/0.98  --resolution_flag                       true
% 1.43/0.98  --res_lit_sel                           adaptive
% 1.43/0.98  --res_lit_sel_side                      none
% 1.43/0.98  --res_ordering                          kbo
% 1.43/0.98  --res_to_prop_solver                    active
% 1.43/0.98  --res_prop_simpl_new                    false
% 1.43/0.98  --res_prop_simpl_given                  true
% 1.43/0.98  --res_passive_queue_type                priority_queues
% 1.43/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.43/0.98  --res_passive_queues_freq               [15;5]
% 1.43/0.98  --res_forward_subs                      full
% 1.43/0.98  --res_backward_subs                     full
% 1.43/0.98  --res_forward_subs_resolution           true
% 1.43/0.98  --res_backward_subs_resolution          true
% 1.43/0.98  --res_orphan_elimination                true
% 1.43/0.98  --res_time_limit                        2.
% 1.43/0.98  --res_out_proof                         true
% 1.43/0.98  
% 1.43/0.98  ------ Superposition Options
% 1.43/0.98  
% 1.43/0.98  --superposition_flag                    true
% 1.43/0.98  --sup_passive_queue_type                priority_queues
% 1.43/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.43/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.43/0.98  --demod_completeness_check              fast
% 1.43/0.98  --demod_use_ground                      true
% 1.43/0.98  --sup_to_prop_solver                    passive
% 1.43/0.98  --sup_prop_simpl_new                    true
% 1.43/0.98  --sup_prop_simpl_given                  true
% 1.43/0.98  --sup_fun_splitting                     false
% 1.43/0.98  --sup_smt_interval                      50000
% 1.43/0.98  
% 1.43/0.98  ------ Superposition Simplification Setup
% 1.43/0.98  
% 1.43/0.98  --sup_indices_passive                   []
% 1.43/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.43/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/0.98  --sup_full_bw                           [BwDemod]
% 1.43/0.98  --sup_immed_triv                        [TrivRules]
% 1.43/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.43/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/0.98  --sup_immed_bw_main                     []
% 1.43/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.43/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.43/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.43/0.98  
% 1.43/0.98  ------ Combination Options
% 1.43/0.98  
% 1.43/0.98  --comb_res_mult                         3
% 1.43/0.98  --comb_sup_mult                         2
% 1.43/0.98  --comb_inst_mult                        10
% 1.43/0.98  
% 1.43/0.98  ------ Debug Options
% 1.43/0.98  
% 1.43/0.98  --dbg_backtrace                         false
% 1.43/0.98  --dbg_dump_prop_clauses                 false
% 1.43/0.98  --dbg_dump_prop_clauses_file            -
% 1.43/0.98  --dbg_out_stat                          false
% 1.43/0.98  ------ Parsing...
% 1.43/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.43/0.98  
% 1.43/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 12 0s  sf_e  pe_s  pe_e 
% 1.43/0.98  
% 1.43/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.43/0.98  
% 1.43/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.43/0.98  ------ Proving...
% 1.43/0.98  ------ Problem Properties 
% 1.43/0.98  
% 1.43/0.98  
% 1.43/0.98  clauses                                 8
% 1.43/0.98  conjectures                             2
% 1.43/0.98  EPR                                     0
% 1.43/0.98  Horn                                    6
% 1.43/0.98  unary                                   4
% 1.43/0.98  binary                                  2
% 1.43/0.98  lits                                    22
% 1.43/0.98  lits eq                                 7
% 1.43/0.98  fd_pure                                 0
% 1.43/0.98  fd_pseudo                               0
% 1.43/0.98  fd_cond                                 0
% 1.43/0.98  fd_pseudo_cond                          0
% 1.43/0.98  AC symbols                              0
% 1.43/0.98  
% 1.43/0.98  ------ Schedule dynamic 5 is on 
% 1.43/0.98  
% 1.43/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.43/0.98  
% 1.43/0.98  
% 1.43/0.98  ------ 
% 1.43/0.98  Current options:
% 1.43/0.98  ------ 
% 1.43/0.98  
% 1.43/0.98  ------ Input Options
% 1.43/0.98  
% 1.43/0.98  --out_options                           all
% 1.43/0.98  --tptp_safe_out                         true
% 1.43/0.98  --problem_path                          ""
% 1.43/0.98  --include_path                          ""
% 1.43/0.98  --clausifier                            res/vclausify_rel
% 1.43/0.98  --clausifier_options                    --mode clausify
% 1.43/0.98  --stdin                                 false
% 1.43/0.98  --stats_out                             all
% 1.43/0.98  
% 1.43/0.98  ------ General Options
% 1.43/0.98  
% 1.43/0.98  --fof                                   false
% 1.43/0.98  --time_out_real                         305.
% 1.43/0.98  --time_out_virtual                      -1.
% 1.43/0.98  --symbol_type_check                     false
% 1.43/0.98  --clausify_out                          false
% 1.43/0.98  --sig_cnt_out                           false
% 1.43/0.98  --trig_cnt_out                          false
% 1.43/0.98  --trig_cnt_out_tolerance                1.
% 1.43/0.98  --trig_cnt_out_sk_spl                   false
% 1.43/0.98  --abstr_cl_out                          false
% 1.43/0.98  
% 1.43/0.98  ------ Global Options
% 1.43/0.98  
% 1.43/0.98  --schedule                              default
% 1.43/0.98  --add_important_lit                     false
% 1.43/0.98  --prop_solver_per_cl                    1000
% 1.43/0.98  --min_unsat_core                        false
% 1.43/0.98  --soft_assumptions                      false
% 1.43/0.98  --soft_lemma_size                       3
% 1.43/0.98  --prop_impl_unit_size                   0
% 1.43/0.98  --prop_impl_unit                        []
% 1.43/0.98  --share_sel_clauses                     true
% 1.43/0.98  --reset_solvers                         false
% 1.43/0.98  --bc_imp_inh                            [conj_cone]
% 1.43/0.98  --conj_cone_tolerance                   3.
% 1.43/0.98  --extra_neg_conj                        none
% 1.43/0.98  --large_theory_mode                     true
% 1.43/0.98  --prolific_symb_bound                   200
% 1.43/0.98  --lt_threshold                          2000
% 1.43/0.98  --clause_weak_htbl                      true
% 1.43/0.98  --gc_record_bc_elim                     false
% 1.43/0.98  
% 1.43/0.98  ------ Preprocessing Options
% 1.43/0.98  
% 1.43/0.98  --preprocessing_flag                    true
% 1.43/0.98  --time_out_prep_mult                    0.1
% 1.43/0.98  --splitting_mode                        input
% 1.43/0.98  --splitting_grd                         true
% 1.43/0.98  --splitting_cvd                         false
% 1.43/0.98  --splitting_cvd_svl                     false
% 1.43/0.98  --splitting_nvd                         32
% 1.43/0.98  --sub_typing                            true
% 1.43/0.98  --prep_gs_sim                           true
% 1.43/0.98  --prep_unflatten                        true
% 1.43/0.98  --prep_res_sim                          true
% 1.43/0.98  --prep_upred                            true
% 1.43/0.98  --prep_sem_filter                       exhaustive
% 1.43/0.98  --prep_sem_filter_out                   false
% 1.43/0.98  --pred_elim                             true
% 1.43/0.98  --res_sim_input                         true
% 1.43/0.98  --eq_ax_congr_red                       true
% 1.43/0.98  --pure_diseq_elim                       true
% 1.43/0.98  --brand_transform                       false
% 1.43/0.98  --non_eq_to_eq                          false
% 1.43/0.98  --prep_def_merge                        true
% 1.43/0.98  --prep_def_merge_prop_impl              false
% 1.43/0.98  --prep_def_merge_mbd                    true
% 1.43/0.98  --prep_def_merge_tr_red                 false
% 1.43/0.98  --prep_def_merge_tr_cl                  false
% 1.43/0.98  --smt_preprocessing                     true
% 1.43/0.98  --smt_ac_axioms                         fast
% 1.43/0.98  --preprocessed_out                      false
% 1.43/0.98  --preprocessed_stats                    false
% 1.43/0.98  
% 1.43/0.98  ------ Abstraction refinement Options
% 1.43/0.98  
% 1.43/0.98  --abstr_ref                             []
% 1.43/0.98  --abstr_ref_prep                        false
% 1.43/0.98  --abstr_ref_until_sat                   false
% 1.43/0.98  --abstr_ref_sig_restrict                funpre
% 1.43/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.43/0.98  --abstr_ref_under                       []
% 1.43/0.98  
% 1.43/0.98  ------ SAT Options
% 1.43/0.98  
% 1.43/0.98  --sat_mode                              false
% 1.43/0.98  --sat_fm_restart_options                ""
% 1.43/0.98  --sat_gr_def                            false
% 1.43/0.98  --sat_epr_types                         true
% 1.43/0.98  --sat_non_cyclic_types                  false
% 1.43/0.98  --sat_finite_models                     false
% 1.43/0.98  --sat_fm_lemmas                         false
% 1.43/0.98  --sat_fm_prep                           false
% 1.43/0.98  --sat_fm_uc_incr                        true
% 1.43/0.98  --sat_out_model                         small
% 1.43/0.98  --sat_out_clauses                       false
% 1.43/0.98  
% 1.43/0.98  ------ QBF Options
% 1.43/0.98  
% 1.43/0.98  --qbf_mode                              false
% 1.43/0.98  --qbf_elim_univ                         false
% 1.43/0.98  --qbf_dom_inst                          none
% 1.43/0.98  --qbf_dom_pre_inst                      false
% 1.43/0.98  --qbf_sk_in                             false
% 1.43/0.98  --qbf_pred_elim                         true
% 1.43/0.98  --qbf_split                             512
% 1.43/0.98  
% 1.43/0.98  ------ BMC1 Options
% 1.43/0.98  
% 1.43/0.98  --bmc1_incremental                      false
% 1.43/0.98  --bmc1_axioms                           reachable_all
% 1.43/0.98  --bmc1_min_bound                        0
% 1.43/0.98  --bmc1_max_bound                        -1
% 1.43/0.98  --bmc1_max_bound_default                -1
% 1.43/0.98  --bmc1_symbol_reachability              true
% 1.43/0.98  --bmc1_property_lemmas                  false
% 1.43/0.98  --bmc1_k_induction                      false
% 1.43/0.98  --bmc1_non_equiv_states                 false
% 1.43/0.98  --bmc1_deadlock                         false
% 1.43/0.98  --bmc1_ucm                              false
% 1.43/0.98  --bmc1_add_unsat_core                   none
% 1.43/0.98  --bmc1_unsat_core_children              false
% 1.43/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.43/0.98  --bmc1_out_stat                         full
% 1.43/0.98  --bmc1_ground_init                      false
% 1.43/0.98  --bmc1_pre_inst_next_state              false
% 1.43/0.98  --bmc1_pre_inst_state                   false
% 1.43/0.98  --bmc1_pre_inst_reach_state             false
% 1.43/0.98  --bmc1_out_unsat_core                   false
% 1.43/0.98  --bmc1_aig_witness_out                  false
% 1.43/0.98  --bmc1_verbose                          false
% 1.43/0.98  --bmc1_dump_clauses_tptp                false
% 1.43/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.43/0.98  --bmc1_dump_file                        -
% 1.43/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.43/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.43/0.98  --bmc1_ucm_extend_mode                  1
% 1.43/0.98  --bmc1_ucm_init_mode                    2
% 1.43/0.98  --bmc1_ucm_cone_mode                    none
% 1.43/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.43/0.98  --bmc1_ucm_relax_model                  4
% 1.43/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.43/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.43/0.98  --bmc1_ucm_layered_model                none
% 1.43/0.98  --bmc1_ucm_max_lemma_size               10
% 1.43/0.98  
% 1.43/0.98  ------ AIG Options
% 1.43/0.98  
% 1.43/0.98  --aig_mode                              false
% 1.43/0.98  
% 1.43/0.98  ------ Instantiation Options
% 1.43/0.98  
% 1.43/0.98  --instantiation_flag                    true
% 1.43/0.98  --inst_sos_flag                         false
% 1.43/0.98  --inst_sos_phase                        true
% 1.43/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.43/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.43/0.98  --inst_lit_sel_side                     none
% 1.43/0.98  --inst_solver_per_active                1400
% 1.43/0.98  --inst_solver_calls_frac                1.
% 1.43/0.98  --inst_passive_queue_type               priority_queues
% 1.43/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.43/0.98  --inst_passive_queues_freq              [25;2]
% 1.43/0.98  --inst_dismatching                      true
% 1.43/0.98  --inst_eager_unprocessed_to_passive     true
% 1.43/0.98  --inst_prop_sim_given                   true
% 1.43/0.98  --inst_prop_sim_new                     false
% 1.43/0.98  --inst_subs_new                         false
% 1.43/0.98  --inst_eq_res_simp                      false
% 1.43/0.98  --inst_subs_given                       false
% 1.43/0.98  --inst_orphan_elimination               true
% 1.43/0.98  --inst_learning_loop_flag               true
% 1.43/0.98  --inst_learning_start                   3000
% 1.43/0.98  --inst_learning_factor                  2
% 1.43/0.98  --inst_start_prop_sim_after_learn       3
% 1.43/0.98  --inst_sel_renew                        solver
% 1.43/0.98  --inst_lit_activity_flag                true
% 1.43/0.98  --inst_restr_to_given                   false
% 1.43/0.98  --inst_activity_threshold               500
% 1.43/0.98  --inst_out_proof                        true
% 1.43/0.98  
% 1.43/0.98  ------ Resolution Options
% 1.43/0.98  
% 1.43/0.98  --resolution_flag                       false
% 1.43/0.98  --res_lit_sel                           adaptive
% 1.43/0.98  --res_lit_sel_side                      none
% 1.43/0.98  --res_ordering                          kbo
% 1.43/0.98  --res_to_prop_solver                    active
% 1.43/0.98  --res_prop_simpl_new                    false
% 1.43/0.98  --res_prop_simpl_given                  true
% 1.43/0.98  --res_passive_queue_type                priority_queues
% 1.43/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.43/0.98  --res_passive_queues_freq               [15;5]
% 1.43/0.98  --res_forward_subs                      full
% 1.43/0.98  --res_backward_subs                     full
% 1.43/0.98  --res_forward_subs_resolution           true
% 1.43/0.98  --res_backward_subs_resolution          true
% 1.43/0.98  --res_orphan_elimination                true
% 1.43/0.98  --res_time_limit                        2.
% 1.43/0.98  --res_out_proof                         true
% 1.43/0.98  
% 1.43/0.98  ------ Superposition Options
% 1.43/0.98  
% 1.43/0.98  --superposition_flag                    true
% 1.43/0.98  --sup_passive_queue_type                priority_queues
% 1.43/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.43/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.43/0.98  --demod_completeness_check              fast
% 1.43/0.98  --demod_use_ground                      true
% 1.43/0.98  --sup_to_prop_solver                    passive
% 1.43/0.98  --sup_prop_simpl_new                    true
% 1.43/0.98  --sup_prop_simpl_given                  true
% 1.43/0.98  --sup_fun_splitting                     false
% 1.43/0.98  --sup_smt_interval                      50000
% 1.43/0.98  
% 1.43/0.98  ------ Superposition Simplification Setup
% 1.43/0.98  
% 1.43/0.98  --sup_indices_passive                   []
% 1.43/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.43/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/0.98  --sup_full_bw                           [BwDemod]
% 1.43/0.98  --sup_immed_triv                        [TrivRules]
% 1.43/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.43/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/0.98  --sup_immed_bw_main                     []
% 1.43/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.43/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.43/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.43/0.98  
% 1.43/0.98  ------ Combination Options
% 1.43/0.98  
% 1.43/0.98  --comb_res_mult                         3
% 1.43/0.98  --comb_sup_mult                         2
% 1.43/0.98  --comb_inst_mult                        10
% 1.43/0.98  
% 1.43/0.98  ------ Debug Options
% 1.43/0.98  
% 1.43/0.98  --dbg_backtrace                         false
% 1.43/0.98  --dbg_dump_prop_clauses                 false
% 1.43/0.98  --dbg_dump_prop_clauses_file            -
% 1.43/0.98  --dbg_out_stat                          false
% 1.43/0.98  
% 1.43/0.98  
% 1.43/0.98  
% 1.43/0.98  
% 1.43/0.98  ------ Proving...
% 1.43/0.98  
% 1.43/0.98  
% 1.43/0.98  % SZS status Theorem for theBenchmark.p
% 1.43/0.98  
% 1.43/0.98   Resolution empty clause
% 1.43/0.98  
% 1.43/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.43/0.98  
% 1.43/0.98  fof(f9,conjecture,(
% 1.43/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 1.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/0.98  
% 1.43/0.98  fof(f10,negated_conjecture,(
% 1.43/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 1.43/0.98    inference(negated_conjecture,[],[f9])).
% 1.43/0.98  
% 1.43/0.98  fof(f29,plain,(
% 1.43/0.98    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.43/0.98    inference(ennf_transformation,[],[f10])).
% 1.43/0.98  
% 1.43/0.98  fof(f30,plain,(
% 1.43/0.98    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.43/0.98    inference(flattening,[],[f29])).
% 1.43/0.98  
% 1.43/0.98  fof(f32,plain,(
% 1.43/0.98    ? [X0] : (? [X1] : (? [X2] : (((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.43/0.98    inference(nnf_transformation,[],[f30])).
% 1.43/0.98  
% 1.43/0.98  fof(f33,plain,(
% 1.43/0.98    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.43/0.98    inference(flattening,[],[f32])).
% 1.43/0.98  
% 1.43/0.98  fof(f36,plain,(
% 1.43/0.98    ( ! [X0,X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r2_waybel_7(X0,X1,sK2) | ~r2_hidden(sK2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,sK2) | r2_hidden(sK2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.43/0.98    introduced(choice_axiom,[])).
% 1.43/0.98  
% 1.43/0.98  fof(f35,plain,(
% 1.43/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r2_waybel_7(X0,sK1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)))) & (r2_waybel_7(X0,sK1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK1))) )),
% 1.43/0.98    introduced(choice_axiom,[])).
% 1.43/0.98  
% 1.43/0.98  fof(f34,plain,(
% 1.43/0.98    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_waybel_7(sK0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & (r2_waybel_7(sK0,X1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.43/0.98    introduced(choice_axiom,[])).
% 1.43/0.98  
% 1.43/0.98  fof(f37,plain,(
% 1.43/0.98    (((~r2_waybel_7(sK0,sK1,sK2) | ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.43/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36,f35,f34])).
% 1.43/0.98  
% 1.43/0.98  fof(f55,plain,(
% 1.43/0.98    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.43/0.98    inference(cnf_transformation,[],[f37])).
% 1.43/0.98  
% 1.43/0.98  fof(f56,plain,(
% 1.43/0.98    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.43/0.98    inference(cnf_transformation,[],[f37])).
% 1.43/0.98  
% 1.43/0.98  fof(f6,axiom,(
% 1.43/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/0.98  
% 1.43/0.98  fof(f12,plain,(
% 1.43/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.43/0.98    inference(pure_predicate_removal,[],[f6])).
% 1.43/0.98  
% 1.43/0.98  fof(f23,plain,(
% 1.43/0.98    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.43/0.98    inference(ennf_transformation,[],[f12])).
% 1.43/0.98  
% 1.43/0.98  fof(f24,plain,(
% 1.43/0.98    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.43/0.98    inference(flattening,[],[f23])).
% 1.43/0.98  
% 1.43/0.98  fof(f46,plain,(
% 1.43/0.98    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.43/0.98    inference(cnf_transformation,[],[f24])).
% 1.43/0.98  
% 1.43/0.98  fof(f54,plain,(
% 1.43/0.98    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 1.43/0.98    inference(cnf_transformation,[],[f37])).
% 1.43/0.98  
% 1.43/0.98  fof(f53,plain,(
% 1.43/0.98    ~v1_xboole_0(sK1)),
% 1.43/0.98    inference(cnf_transformation,[],[f37])).
% 1.43/0.98  
% 1.43/0.98  fof(f2,axiom,(
% 1.43/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/0.98  
% 1.43/0.98  fof(f16,plain,(
% 1.43/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.43/0.98    inference(ennf_transformation,[],[f2])).
% 1.43/0.98  
% 1.43/0.98  fof(f39,plain,(
% 1.43/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.43/0.98    inference(cnf_transformation,[],[f16])).
% 1.43/0.98  
% 1.43/0.98  fof(f52,plain,(
% 1.43/0.98    l1_pre_topc(sK0)),
% 1.43/0.98    inference(cnf_transformation,[],[f37])).
% 1.43/0.98  
% 1.43/0.98  fof(f50,plain,(
% 1.43/0.98    ~v2_struct_0(sK0)),
% 1.43/0.98    inference(cnf_transformation,[],[f37])).
% 1.43/0.98  
% 1.43/0.98  fof(f4,axiom,(
% 1.43/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/0.98  
% 1.43/0.98  fof(f13,plain,(
% 1.43/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.43/0.98    inference(pure_predicate_removal,[],[f4])).
% 1.43/0.98  
% 1.43/0.98  fof(f19,plain,(
% 1.43/0.98    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.43/0.98    inference(ennf_transformation,[],[f13])).
% 1.43/0.98  
% 1.43/0.98  fof(f20,plain,(
% 1.43/0.98    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.43/0.98    inference(flattening,[],[f19])).
% 1.43/0.98  
% 1.43/0.98  fof(f41,plain,(
% 1.43/0.98    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.43/0.98    inference(cnf_transformation,[],[f20])).
% 1.43/0.98  
% 1.43/0.98  fof(f5,axiom,(
% 1.43/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/0.98  
% 1.43/0.98  fof(f11,plain,(
% 1.43/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.43/0.98    inference(pure_predicate_removal,[],[f5])).
% 1.43/0.98  
% 1.43/0.98  fof(f14,plain,(
% 1.43/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.43/0.98    inference(pure_predicate_removal,[],[f11])).
% 1.43/0.98  
% 1.43/0.98  fof(f21,plain,(
% 1.43/0.98    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.43/0.98    inference(ennf_transformation,[],[f14])).
% 1.43/0.98  
% 1.43/0.98  fof(f22,plain,(
% 1.43/0.98    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.43/0.98    inference(flattening,[],[f21])).
% 1.43/0.98  
% 1.43/0.98  fof(f44,plain,(
% 1.43/0.98    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.43/0.98    inference(cnf_transformation,[],[f22])).
% 1.43/0.98  
% 1.43/0.98  fof(f60,plain,(
% 1.43/0.98    ~r2_waybel_7(sK0,sK1,sK2) | ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 1.43/0.98    inference(cnf_transformation,[],[f37])).
% 1.43/0.98  
% 1.43/0.98  fof(f7,axiom,(
% 1.43/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 1.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/0.98  
% 1.43/0.98  fof(f25,plain,(
% 1.43/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.43/0.98    inference(ennf_transformation,[],[f7])).
% 1.43/0.98  
% 1.43/0.98  fof(f26,plain,(
% 1.43/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.43/0.98    inference(flattening,[],[f25])).
% 1.43/0.98  
% 1.43/0.98  fof(f31,plain,(
% 1.43/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.43/0.98    inference(nnf_transformation,[],[f26])).
% 1.43/0.98  
% 1.43/0.98  fof(f48,plain,(
% 1.43/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.43/0.98    inference(cnf_transformation,[],[f31])).
% 1.43/0.98  
% 1.43/0.98  fof(f51,plain,(
% 1.43/0.98    v2_pre_topc(sK0)),
% 1.43/0.98    inference(cnf_transformation,[],[f37])).
% 1.43/0.98  
% 1.43/0.98  fof(f58,plain,(
% 1.43/0.98    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.43/0.98    inference(cnf_transformation,[],[f37])).
% 1.43/0.98  
% 1.43/0.98  fof(f42,plain,(
% 1.43/0.98    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.43/0.98    inference(cnf_transformation,[],[f20])).
% 1.43/0.98  
% 1.43/0.98  fof(f3,axiom,(
% 1.43/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/0.98  
% 1.43/0.98  fof(f17,plain,(
% 1.43/0.98    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.43/0.98    inference(ennf_transformation,[],[f3])).
% 1.43/0.98  
% 1.43/0.98  fof(f18,plain,(
% 1.43/0.98    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.43/0.98    inference(flattening,[],[f17])).
% 1.43/0.98  
% 1.43/0.98  fof(f40,plain,(
% 1.43/0.98    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.43/0.98    inference(cnf_transformation,[],[f18])).
% 1.43/0.98  
% 1.43/0.98  fof(f57,plain,(
% 1.43/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 1.43/0.98    inference(cnf_transformation,[],[f37])).
% 1.43/0.98  
% 1.43/0.98  fof(f1,axiom,(
% 1.43/0.98    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/0.98  
% 1.43/0.98  fof(f15,plain,(
% 1.43/0.98    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.43/0.98    inference(ennf_transformation,[],[f1])).
% 1.43/0.98  
% 1.43/0.98  fof(f38,plain,(
% 1.43/0.98    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 1.43/0.98    inference(cnf_transformation,[],[f15])).
% 1.43/0.98  
% 1.43/0.98  fof(f8,axiom,(
% 1.43/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.43/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/0.98  
% 1.43/0.98  fof(f27,plain,(
% 1.43/0.98    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.43/0.98    inference(ennf_transformation,[],[f8])).
% 1.43/0.98  
% 1.43/0.98  fof(f28,plain,(
% 1.43/0.98    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.43/0.98    inference(flattening,[],[f27])).
% 1.43/0.98  
% 1.43/0.98  fof(f49,plain,(
% 1.43/0.98    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.43/0.98    inference(cnf_transformation,[],[f28])).
% 1.43/0.98  
% 1.43/0.98  fof(f59,plain,(
% 1.43/0.98    r2_waybel_7(sK0,sK1,sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 1.43/0.98    inference(cnf_transformation,[],[f37])).
% 1.43/0.98  
% 1.43/0.98  fof(f47,plain,(
% 1.43/0.98    ( ! [X2,X0,X1] : (r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.43/0.98    inference(cnf_transformation,[],[f31])).
% 1.43/0.98  
% 1.43/0.98  cnf(c_17,negated_conjecture,
% 1.43/0.98      ( v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
% 1.43/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_16,negated_conjecture,
% 1.43/0.98      ( v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
% 1.43/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_7,plain,
% 1.43/0.98      ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
% 1.43/0.98      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
% 1.43/0.98      | ~ v13_waybel_0(X0,k3_yellow_1(X1))
% 1.43/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.43/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
% 1.43/0.98      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.43/0.98      | v2_struct_0(X2)
% 1.43/0.98      | v1_xboole_0(X1)
% 1.43/0.98      | v1_xboole_0(X0)
% 1.43/0.98      | ~ l1_struct_0(X2) ),
% 1.43/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_18,negated_conjecture,
% 1.43/0.98      ( v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
% 1.43/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_306,plain,
% 1.43/0.98      ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
% 1.43/0.98      | ~ v13_waybel_0(X0,k3_yellow_1(X1))
% 1.43/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.43/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
% 1.43/0.98      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.43/0.98      | v2_struct_0(X2)
% 1.43/0.98      | v1_xboole_0(X1)
% 1.43/0.98      | v1_xboole_0(X0)
% 1.43/0.98      | ~ l1_struct_0(X2)
% 1.43/0.98      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X1))
% 1.43/0.98      | sK1 != X0 ),
% 1.43/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_307,plain,
% 1.43/0.98      ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
% 1.43/0.98      | ~ v13_waybel_0(sK1,k3_yellow_1(X0))
% 1.43/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.98      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.43/0.98      | v2_struct_0(X1)
% 1.43/0.98      | v1_xboole_0(X0)
% 1.43/0.98      | v1_xboole_0(sK1)
% 1.43/0.98      | ~ l1_struct_0(X1)
% 1.43/0.98      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0)) ),
% 1.43/0.98      inference(unflattening,[status(thm)],[c_306]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_19,negated_conjecture,
% 1.43/0.98      ( ~ v1_xboole_0(sK1) ),
% 1.43/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_311,plain,
% 1.43/0.98      ( v1_xboole_0(X0)
% 1.43/0.98      | v2_struct_0(X1)
% 1.43/0.98      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.43/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.98      | ~ v13_waybel_0(sK1,k3_yellow_1(X0))
% 1.43/0.98      | ~ v2_waybel_0(sK1,k3_yellow_1(X0))
% 1.43/0.98      | ~ l1_struct_0(X1)
% 1.43/0.98      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0)) ),
% 1.43/0.98      inference(global_propositional_subsumption,[status(thm)],[c_307,c_19]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_312,plain,
% 1.43/0.98      ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
% 1.43/0.98      | ~ v13_waybel_0(sK1,k3_yellow_1(X0))
% 1.43/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.98      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.43/0.98      | v2_struct_0(X1)
% 1.43/0.98      | v1_xboole_0(X0)
% 1.43/0.98      | ~ l1_struct_0(X1)
% 1.43/0.98      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0)) ),
% 1.43/0.98      inference(renaming,[status(thm)],[c_311]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1263,plain,
% 1.43/0.98      ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
% 1.43/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.98      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.43/0.98      | v2_struct_0(X1)
% 1.43/0.98      | v1_xboole_0(X0)
% 1.43/0.98      | ~ l1_struct_0(X1)
% 1.43/0.98      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
% 1.43/0.98      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0))
% 1.43/0.98      | sK1 != sK1 ),
% 1.43/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_312]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1656,plain,
% 1.43/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.98      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.43/0.98      | v2_struct_0(X1)
% 1.43/0.98      | v1_xboole_0(X0)
% 1.43/0.98      | ~ l1_struct_0(X1)
% 1.43/0.98      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
% 1.43/0.98      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0))
% 1.43/0.98      | sK1 != sK1 ),
% 1.43/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_1263]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1,plain,
% 1.43/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.43/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_20,negated_conjecture,
% 1.43/0.99      ( l1_pre_topc(sK0) ),
% 1.43/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_478,plain,
% 1.43/0.99      ( l1_struct_0(X0) | sK0 != X0 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_20]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_479,plain,
% 1.43/0.99      ( l1_struct_0(sK0) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_478]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2035,plain,
% 1.43/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0))
% 1.43/0.99      | sK1 != sK1
% 1.43/0.99      | sK0 != X1 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_1656,c_479]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2036,plain,
% 1.43/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v2_struct_0(sK0)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0)) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_2035]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_22,negated_conjecture,
% 1.43/0.99      ( ~ v2_struct_0(sK0) ),
% 1.43/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2040,plain,
% 1.43/0.99      ( v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0)) ),
% 1.43/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2036,c_22]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2041,plain,
% 1.43/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0)) ),
% 1.43/0.99      inference(renaming,[status(thm)],[c_2040]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_4,plain,
% 1.43/0.99      ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
% 1.43/0.99      | ~ v13_waybel_0(X0,k3_yellow_1(X1))
% 1.43/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
% 1.43/0.99      | v2_struct_0(X2)
% 1.43/0.99      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.43/0.99      | v1_xboole_0(X1)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | ~ l1_struct_0(X2) ),
% 1.43/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1191,plain,
% 1.43/0.99      ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
% 1.43/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
% 1.43/0.99      | v2_struct_0(X2)
% 1.43/0.99      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.43/0.99      | v1_xboole_0(X1)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | ~ l1_struct_0(X2)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
% 1.43/0.99      | sK1 != X0 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_16]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1192,plain,
% 1.43/0.99      ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | v1_xboole_0(sK1)
% 1.43/0.99      | ~ l1_struct_0(X1)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_1191]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1196,plain,
% 1.43/0.99      ( v1_xboole_0(X0)
% 1.43/0.99      | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | ~ v2_waybel_0(sK1,k3_yellow_1(X0))
% 1.43/0.99      | ~ l1_struct_0(X1)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1192,c_19]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1197,plain,
% 1.43/0.99      ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | ~ l1_struct_0(X1)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(renaming,[status(thm)],[c_1196]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1717,plain,
% 1.43/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | ~ l1_struct_0(X1)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
% 1.43/0.99      | sK1 != sK1 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_1197]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2008,plain,
% 1.43/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
% 1.43/0.99      | sK1 != sK1
% 1.43/0.99      | sK0 != X1 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_1717,c_479]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2009,plain,
% 1.43/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v2_struct_0(sK0)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_2008]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2013,plain,
% 1.43/0.99      ( ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2009,c_22]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2014,plain,
% 1.43/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(renaming,[status(thm)],[c_2013]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_5,plain,
% 1.43/0.99      ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
% 1.43/0.99      | ~ v13_waybel_0(X0,k3_yellow_1(X1))
% 1.43/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
% 1.43/0.99      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.43/0.99      | v2_struct_0(X2)
% 1.43/0.99      | v1_xboole_0(X1)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | ~ l1_struct_0(X2) ),
% 1.43/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1155,plain,
% 1.43/0.99      ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
% 1.43/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
% 1.43/0.99      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.43/0.99      | v2_struct_0(X2)
% 1.43/0.99      | v1_xboole_0(X1)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | ~ l1_struct_0(X2)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
% 1.43/0.99      | sK1 != X0 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_16]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1156,plain,
% 1.43/0.99      ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | v4_orders_2(k3_yellow19(X1,X0,sK1))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | v1_xboole_0(sK1)
% 1.43/0.99      | ~ l1_struct_0(X1)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_1155]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1160,plain,
% 1.43/0.99      ( v1_xboole_0(X0)
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | v4_orders_2(k3_yellow19(X1,X0,sK1))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | ~ v2_waybel_0(sK1,k3_yellow_1(X0))
% 1.43/0.99      | ~ l1_struct_0(X1)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1156,c_19]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1161,plain,
% 1.43/0.99      ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | v4_orders_2(k3_yellow19(X1,X0,sK1))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | ~ l1_struct_0(X1)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(renaming,[status(thm)],[c_1160]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1746,plain,
% 1.43/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | v4_orders_2(k3_yellow19(X1,X0,sK1))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | ~ l1_struct_0(X1)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
% 1.43/0.99      | sK1 != sK1 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_1161]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1981,plain,
% 1.43/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | v4_orders_2(k3_yellow19(X1,X0,sK1))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
% 1.43/0.99      | sK1 != sK1
% 1.43/0.99      | sK0 != X1 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_1746,c_479]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1982,plain,
% 1.43/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v2_struct_0(sK0)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_1981]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1986,plain,
% 1.43/0.99      ( v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1982,c_22]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1987,plain,
% 1.43/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(renaming,[status(thm)],[c_1986]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_12,negated_conjecture,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
% 1.43/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_166,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
% 1.43/0.99      inference(prop_impl,[status(thm)],[c_12]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_9,plain,
% 1.43/0.99      ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.43/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 1.43/0.99      | ~ l1_waybel_0(X1,X0)
% 1.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.43/0.99      | ~ v2_pre_topc(X0)
% 1.43/0.99      | ~ v7_waybel_0(X1)
% 1.43/0.99      | ~ v4_orders_2(X1)
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ l1_pre_topc(X0) ),
% 1.43/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_21,negated_conjecture,
% 1.43/0.99      ( v2_pre_topc(sK0) ),
% 1.43/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_429,plain,
% 1.43/0.99      ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.43/0.99      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 1.43/0.99      | ~ l1_waybel_0(X1,X0)
% 1.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.43/0.99      | ~ v7_waybel_0(X1)
% 1.43/0.99      | ~ v4_orders_2(X1)
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ l1_pre_topc(X0)
% 1.43/0.99      | sK0 != X0 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_430,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.43/0.99      | r2_hidden(X1,k10_yellow_6(sK0,X0))
% 1.43/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.43/0.99      | ~ v7_waybel_0(X0)
% 1.43/0.99      | ~ v4_orders_2(X0)
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | v2_struct_0(sK0)
% 1.43/0.99      | ~ l1_pre_topc(sK0) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_429]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_434,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.43/0.99      | r2_hidden(X1,k10_yellow_6(sK0,X0))
% 1.43/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.43/0.99      | ~ v7_waybel_0(X0)
% 1.43/0.99      | ~ v4_orders_2(X0)
% 1.43/0.99      | v2_struct_0(X0) ),
% 1.43/0.99      inference(global_propositional_subsumption,
% 1.43/0.99                [status(thm)],
% 1.43/0.99                [c_430,c_22,c_20]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_814,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.43/0.99      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.43/0.99      | ~ v7_waybel_0(X0)
% 1.43/0.99      | ~ v4_orders_2(X0)
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0)
% 1.43/0.99      | sK2 != X1 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_166,c_434]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_815,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
% 1.43/0.99      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.43/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 1.43/0.99      | ~ v7_waybel_0(X0)
% 1.43/0.99      | ~ v4_orders_2(X0)
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_814]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_14,negated_conjecture,
% 1.43/0.99      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 1.43/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_819,plain,
% 1.43/0.99      ( ~ l1_waybel_0(X0,sK0)
% 1.43/0.99      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
% 1.43/0.99      | ~ v7_waybel_0(X0)
% 1.43/0.99      | ~ v4_orders_2(X0)
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
% 1.43/0.99      inference(global_propositional_subsumption,[status(thm)],[c_815,c_14]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_820,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
% 1.43/0.99      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.43/0.99      | ~ v7_waybel_0(X0)
% 1.43/0.99      | ~ v4_orders_2(X0)
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
% 1.43/0.99      inference(renaming,[status(thm)],[c_819]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_3,plain,
% 1.43/0.99      ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
% 1.43/0.99      | ~ v13_waybel_0(X0,k3_yellow_1(X1))
% 1.43/0.99      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 1.43/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
% 1.43/0.99      | v2_struct_0(X2)
% 1.43/0.99      | v1_xboole_0(X1)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | ~ l1_struct_0(X2) ),
% 1.43/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1227,plain,
% 1.43/0.99      ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
% 1.43/0.99      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 1.43/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
% 1.43/0.99      | v2_struct_0(X2)
% 1.43/0.99      | v1_xboole_0(X1)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | ~ l1_struct_0(X2)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
% 1.43/0.99      | sK1 != X0 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_16]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1228,plain,
% 1.43/0.99      ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
% 1.43/0.99      | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | v1_xboole_0(sK1)
% 1.43/0.99      | ~ l1_struct_0(X1)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_1227]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1232,plain,
% 1.43/0.99      ( v1_xboole_0(X0)
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
% 1.43/0.99      | ~ v2_waybel_0(sK1,k3_yellow_1(X0))
% 1.43/0.99      | ~ l1_struct_0(X1)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1228,c_19]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1233,plain,
% 1.43/0.99      ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
% 1.43/0.99      | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | ~ l1_struct_0(X1)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(renaming,[status(thm)],[c_1232]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1688,plain,
% 1.43/0.99      ( l1_waybel_0(k3_yellow19(X0,X1,sK1),X0)
% 1.43/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | v1_xboole_0(X1)
% 1.43/0.99      | ~ l1_struct_0(X0)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
% 1.43/0.99      | sK1 != sK1 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_1233]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1846,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
% 1.43/0.99      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
% 1.43/0.99      | ~ v7_waybel_0(X0)
% 1.43/0.99      | ~ v4_orders_2(X0)
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | v2_struct_0(X2)
% 1.43/0.99      | v1_xboole_0(X1)
% 1.43/0.99      | ~ l1_struct_0(X2)
% 1.43/0.99      | k3_yellow19(X2,X1,sK1) != X0
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
% 1.43/0.99      | sK1 != sK1
% 1.43/0.99      | sK0 != X2 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_820,c_1688]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1847,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.43/0.99      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v2_struct_0(sK0)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | ~ l1_struct_0(sK0)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_1846]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_63,plain,
% 1.43/0.99      ( ~ l1_pre_topc(sK0) | l1_struct_0(sK0) ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1851,plain,
% 1.43/0.99      ( v1_xboole_0(X0)
% 1.43/0.99      | ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.43/0.99      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(global_propositional_subsumption,
% 1.43/0.99                [status(thm)],
% 1.43/0.99                [c_1847,c_22,c_20,c_63]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1852,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.43/0.99      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(renaming,[status(thm)],[c_1851]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2074,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.43/0.99      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_1987,c_1852]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2089,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.43/0.99      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_2014,c_2074]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2106,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.43/0.99      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0)) ),
% 1.43/0.99      inference(resolution,[status(thm)],[c_2041,c_2089]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2,plain,
% 1.43/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 1.43/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1963,plain,
% 1.43/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK0 != X0 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_479]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1964,plain,
% 1.43/0.99      ( v2_struct_0(sK0) | ~ v1_xboole_0(k2_struct_0(sK0)) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_1963]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_60,plain,
% 1.43/0.99      ( v2_struct_0(sK0)
% 1.43/0.99      | ~ v1_xboole_0(k2_struct_0(sK0))
% 1.43/0.99      | ~ l1_struct_0(sK0) ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1966,plain,
% 1.43/0.99      ( ~ v1_xboole_0(k2_struct_0(sK0)) ),
% 1.43/0.99      inference(global_propositional_subsumption,
% 1.43/0.99                [status(thm)],
% 1.43/0.99                [c_1964,c_22,c_20,c_60,c_63]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2255,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.43/0.99      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0))
% 1.43/0.99      | k2_struct_0(sK0) != X0 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_2106,c_1966]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2256,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.43/0.99      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0))
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_2255]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_15,negated_conjecture,
% 1.43/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
% 1.43/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_0,plain,
% 1.43/0.99      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.43/0.99      | ~ l1_struct_0(X0) ),
% 1.43/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_66,plain,
% 1.43/0.99      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ l1_struct_0(sK0) ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2258,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.43/0.99      | ~ r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0))
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
% 1.43/0.99      inference(global_propositional_subsumption,
% 1.43/0.99                [status(thm)],
% 1.43/0.99                [c_2256,c_20,c_15,c_63,c_66]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2313,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.43/0.99      | ~ r2_waybel_7(sK0,sK1,sK2) ),
% 1.43/0.99      inference(equality_resolution_simp,[status(thm)],[c_2258]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2332,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) ),
% 1.43/0.99      inference(prop_impl,[status(thm)],[c_2313]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2333,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.43/0.99      | ~ r2_waybel_7(sK0,sK1,sK2) ),
% 1.43/0.99      inference(renaming,[status(thm)],[c_2332]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2388,plain,
% 1.43/0.99      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.43/0.99      | ~ r2_waybel_7(sK0,sK1,sK2) ),
% 1.43/0.99      inference(subtyping,[status(esa)],[c_2333]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2676,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) != iProver_top
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2) != iProver_top ),
% 1.43/0.99      inference(predicate_to_equality,[status(thm)],[c_2388]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_11,plain,
% 1.43/0.99      ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
% 1.43/0.99      | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
% 1.43/0.99      | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | ~ l1_struct_0(X1)
% 1.43/0.99      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 1.43/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_345,plain,
% 1.43/0.99      ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
% 1.43/0.99      | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | ~ l1_struct_0(X1)
% 1.43/0.99      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(X1))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))
% 1.43/0.99      | sK1 != X0 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_346,plain,
% 1.43/0.99      ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
% 1.43/0.99      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | v1_xboole_0(sK1)
% 1.43/0.99      | ~ l1_struct_0(X0)
% 1.43/0.99      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(X0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_345]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_350,plain,
% 1.43/0.99      ( v2_struct_0(X0)
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
% 1.43/0.99      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
% 1.43/0.99      | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
% 1.43/0.99      | ~ l1_struct_0(X0)
% 1.43/0.99      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(X0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
% 1.43/0.99      inference(global_propositional_subsumption,[status(thm)],[c_346,c_19]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_351,plain,
% 1.43/0.99      ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
% 1.43/0.99      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | ~ l1_struct_0(X0)
% 1.43/0.99      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(X0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
% 1.43/0.99      inference(renaming,[status(thm)],[c_350]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1298,plain,
% 1.43/0.99      ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | ~ l1_struct_0(X0)
% 1.43/0.99      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.43/0.99      | k3_yellow_1(k2_struct_0(X0)) != k3_yellow_1(k2_struct_0(sK0))
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(X0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))
% 1.43/0.99      | sK1 != sK1 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_351]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1775,plain,
% 1.43/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | ~ l1_struct_0(X0)
% 1.43/0.99      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.43/0.99      | k3_yellow_1(k2_struct_0(X0)) != k3_yellow_1(k2_struct_0(sK0))
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(X0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))
% 1.43/0.99      | sK1 != sK1 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_1298]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1952,plain,
% 1.43/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.43/0.99      | k3_yellow_1(k2_struct_0(X0)) != k3_yellow_1(k2_struct_0(sK0))
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(X0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))
% 1.43/0.99      | sK1 != sK1
% 1.43/0.99      | sK0 != X0 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_1775,c_479]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1953,plain,
% 1.43/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
% 1.43/0.99      | v2_struct_0(sK0)
% 1.43/0.99      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0))
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_1952]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_353,plain,
% 1.43/0.99      ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
% 1.43/0.99      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
% 1.43/0.99      | v2_struct_0(sK0)
% 1.43/0.99      | ~ l1_struct_0(sK0)
% 1.43/0.99      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
% 1.43/0.99      inference(instantiation,[status(thm)],[c_351]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1955,plain,
% 1.43/0.99      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
% 1.43/0.99      inference(global_propositional_subsumption,
% 1.43/0.99                [status(thm)],
% 1.43/0.99                [c_1953,c_22,c_20,c_17,c_16,c_15,c_63,c_353]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2320,plain,
% 1.43/0.99      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
% 1.43/0.99      inference(equality_resolution_simp,[status(thm)],[c_1955]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2386,plain,
% 1.43/0.99      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
% 1.43/0.99      inference(subtyping,[status(esa)],[c_2320]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2689,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,sK1,sK2) != iProver_top ),
% 1.43/0.99      inference(light_normalisation,[status(thm)],[c_2676,c_2386]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_13,negated_conjecture,
% 1.43/0.99      ( r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
% 1.43/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_168,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
% 1.43/0.99      inference(prop_impl,[status(thm)],[c_13]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_10,plain,
% 1.43/0.99      ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.43/0.99      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 1.43/0.99      | ~ l1_waybel_0(X1,X0)
% 1.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.43/0.99      | ~ v2_pre_topc(X0)
% 1.43/0.99      | ~ v7_waybel_0(X1)
% 1.43/0.99      | ~ v4_orders_2(X1)
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ l1_pre_topc(X0) ),
% 1.43/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_396,plain,
% 1.43/0.99      ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.43/0.99      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 1.43/0.99      | ~ l1_waybel_0(X1,X0)
% 1.43/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.43/0.99      | ~ v7_waybel_0(X1)
% 1.43/0.99      | ~ v4_orders_2(X1)
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | v2_struct_0(X1)
% 1.43/0.99      | ~ l1_pre_topc(X0)
% 1.43/0.99      | sK0 != X0 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_397,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.43/0.99      | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
% 1.43/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.43/0.99      | ~ v7_waybel_0(X0)
% 1.43/0.99      | ~ v4_orders_2(X0)
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | v2_struct_0(sK0)
% 1.43/0.99      | ~ l1_pre_topc(sK0) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_396]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_401,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.43/0.99      | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
% 1.43/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.43/0.99      | ~ v7_waybel_0(X0)
% 1.43/0.99      | ~ v4_orders_2(X0)
% 1.43/0.99      | v2_struct_0(X0) ),
% 1.43/0.99      inference(global_propositional_subsumption,
% 1.43/0.99                [status(thm)],
% 1.43/0.99                [c_397,c_22,c_20]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_781,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.43/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.43/0.99      | ~ v7_waybel_0(X0)
% 1.43/0.99      | ~ v4_orders_2(X0)
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0)
% 1.43/0.99      | sK2 != X1 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_168,c_401]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_782,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.43/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 1.43/0.99      | ~ v7_waybel_0(X0)
% 1.43/0.99      | ~ v4_orders_2(X0)
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_781]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_786,plain,
% 1.43/0.99      ( ~ l1_waybel_0(X0,sK0)
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
% 1.43/0.99      | ~ v7_waybel_0(X0)
% 1.43/0.99      | ~ v4_orders_2(X0)
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
% 1.43/0.99      inference(global_propositional_subsumption,[status(thm)],[c_782,c_14]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_787,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.43/0.99      | ~ v7_waybel_0(X0)
% 1.43/0.99      | ~ v4_orders_2(X0)
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0) ),
% 1.43/0.99      inference(renaming,[status(thm)],[c_786]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1888,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
% 1.43/0.99      | ~ v7_waybel_0(X0)
% 1.43/0.99      | ~ v4_orders_2(X0)
% 1.43/0.99      | v2_struct_0(X0)
% 1.43/0.99      | v2_struct_0(X2)
% 1.43/0.99      | v1_xboole_0(X1)
% 1.43/0.99      | ~ l1_struct_0(X2)
% 1.43/0.99      | k3_yellow19(X2,X1,sK1) != X0
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,X0)
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
% 1.43/0.99      | sK1 != sK1
% 1.43/0.99      | sK0 != X2 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_787,c_1688]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1889,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v2_struct_0(sK0)
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | ~ l1_struct_0(sK0)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_1888]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1893,plain,
% 1.43/0.99      ( v1_xboole_0(X0)
% 1.43/0.99      | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(global_propositional_subsumption,
% 1.43/0.99                [status(thm)],
% 1.43/0.99                [c_1889,c_22,c_20,c_63]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_1894,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(renaming,[status(thm)],[c_1893]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2075,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_1987,c_1894]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2088,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0) ),
% 1.43/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_2014,c_2075]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2135,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | v1_xboole_0(X0)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0)) ),
% 1.43/0.99      inference(resolution,[status(thm)],[c_2041,c_2088]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2232,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)),sK2)
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0))
% 1.43/0.99      | k2_struct_0(sK0) != X0 ),
% 1.43/0.99      inference(resolution_lifted,[status(thm)],[c_2135,c_1966]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2233,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.43/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0))
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
% 1.43/0.99      inference(unflattening,[status(thm)],[c_2232]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2235,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.43/0.99      | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0))
% 1.43/0.99      | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
% 1.43/0.99      inference(global_propositional_subsumption,
% 1.43/0.99                [status(thm)],
% 1.43/0.99                [c_2233,c_20,c_15,c_63,c_66]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2315,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2) ),
% 1.43/0.99      inference(equality_resolution_simp,[status(thm)],[c_2235]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2334,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,sK1,sK2)
% 1.43/0.99      | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) ),
% 1.43/0.99      inference(prop_impl,[status(thm)],[c_2315]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2335,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2) ),
% 1.43/0.99      inference(renaming,[status(thm)],[c_2334]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2387,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2) ),
% 1.43/0.99      inference(subtyping,[status(esa)],[c_2335]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2677,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) = iProver_top
% 1.43/0.99      | r2_waybel_7(sK0,sK1,sK2) = iProver_top ),
% 1.43/0.99      inference(predicate_to_equality,[status(thm)],[c_2387]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2686,plain,
% 1.43/0.99      ( r2_waybel_7(sK0,sK1,sK2) = iProver_top ),
% 1.43/0.99      inference(light_normalisation,[status(thm)],[c_2677,c_2386]) ).
% 1.43/0.99  
% 1.43/0.99  cnf(c_2691,plain,
% 1.43/0.99      ( $false ),
% 1.43/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2689,c_2686]) ).
% 1.43/0.99  
% 1.43/0.99  
% 1.43/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.43/0.99  
% 1.43/0.99  ------                               Statistics
% 1.43/0.99  
% 1.43/0.99  ------ General
% 1.43/0.99  
% 1.43/0.99  abstr_ref_over_cycles:                  0
% 1.43/0.99  abstr_ref_under_cycles:                 0
% 1.43/0.99  gc_basic_clause_elim:                   0
% 1.43/0.99  forced_gc_time:                         0
% 1.43/0.99  parsing_time:                           0.012
% 1.43/0.99  unif_index_cands_time:                  0.
% 1.43/0.99  unif_index_add_time:                    0.
% 1.43/0.99  orderings_time:                         0.
% 1.43/0.99  out_proof_time:                         0.016
% 1.43/0.99  total_time:                             0.125
% 1.43/0.99  num_of_symbols:                         57
% 1.43/0.99  num_of_terms:                           1623
% 1.43/0.99  
% 1.43/0.99  ------ Preprocessing
% 1.43/0.99  
% 1.43/0.99  num_of_splits:                          0
% 1.43/0.99  num_of_split_atoms:                     0
% 1.43/0.99  num_of_reused_defs:                     0
% 1.43/0.99  num_eq_ax_congr_red:                    3
% 1.43/0.99  num_of_sem_filtered_clauses:            1
% 1.43/0.99  num_of_subtypes:                        5
% 1.43/0.99  monotx_restored_types:                  0
% 1.43/0.99  sat_num_of_epr_types:                   0
% 1.43/0.99  sat_num_of_non_cyclic_types:            0
% 1.43/0.99  sat_guarded_non_collapsed_types:        0
% 1.43/0.99  num_pure_diseq_elim:                    0
% 1.43/0.99  simp_replaced_by:                       0
% 1.43/0.99  res_preprocessed:                       82
% 1.43/0.99  prep_upred:                             0
% 1.43/0.99  prep_unflattend:                        48
% 1.43/0.99  smt_new_axioms:                         0
% 1.43/0.99  pred_elim_cands:                        2
% 1.43/0.99  pred_elim:                              12
% 1.43/0.99  pred_elim_cl:                           13
% 1.43/0.99  pred_elim_cycles:                       23
% 1.43/0.99  merged_defs:                            8
% 1.43/0.99  merged_defs_ncl:                        0
% 1.43/0.99  bin_hyper_res:                          8
% 1.43/0.99  prep_cycles:                            4
% 1.43/0.99  pred_elim_time:                         0.059
% 1.43/0.99  splitting_time:                         0.
% 1.43/0.99  sem_filter_time:                        0.
% 1.43/0.99  monotx_time:                            0.
% 1.43/0.99  subtype_inf_time:                       0.
% 1.43/0.99  
% 1.43/0.99  ------ Problem properties
% 1.43/0.99  
% 1.43/0.99  clauses:                                8
% 1.43/0.99  conjectures:                            2
% 1.43/0.99  epr:                                    0
% 1.43/0.99  horn:                                   6
% 1.43/0.99  ground:                                 8
% 1.43/0.99  unary:                                  4
% 1.43/0.99  binary:                                 2
% 1.43/0.99  lits:                                   22
% 1.43/0.99  lits_eq:                                7
% 1.43/0.99  fd_pure:                                0
% 1.43/0.99  fd_pseudo:                              0
% 1.43/0.99  fd_cond:                                0
% 1.43/0.99  fd_pseudo_cond:                         0
% 1.43/0.99  ac_symbols:                             0
% 1.43/0.99  
% 1.43/0.99  ------ Propositional Solver
% 1.43/0.99  
% 1.43/0.99  prop_solver_calls:                      21
% 1.43/0.99  prop_fast_solver_calls:                 1176
% 1.43/0.99  smt_solver_calls:                       0
% 1.43/0.99  smt_fast_solver_calls:                  0
% 1.43/0.99  prop_num_of_clauses:                    425
% 1.43/0.99  prop_preprocess_simplified:             1679
% 1.43/0.99  prop_fo_subsumed:                       39
% 1.43/0.99  prop_solver_time:                       0.
% 1.43/0.99  smt_solver_time:                        0.
% 1.43/0.99  smt_fast_solver_time:                   0.
% 1.43/0.99  prop_fast_solver_time:                  0.
% 1.43/0.99  prop_unsat_core_time:                   0.
% 1.43/0.99  
% 1.43/0.99  ------ QBF
% 1.43/0.99  
% 1.43/0.99  qbf_q_res:                              0
% 1.43/0.99  qbf_num_tautologies:                    0
% 1.43/0.99  qbf_prep_cycles:                        0
% 1.43/0.99  
% 1.43/0.99  ------ BMC1
% 1.43/0.99  
% 1.43/0.99  bmc1_current_bound:                     -1
% 1.43/0.99  bmc1_last_solved_bound:                 -1
% 1.43/0.99  bmc1_unsat_core_size:                   -1
% 1.43/0.99  bmc1_unsat_core_parents_size:           -1
% 1.43/0.99  bmc1_merge_next_fun:                    0
% 1.43/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.43/0.99  
% 1.43/0.99  ------ Instantiation
% 1.43/0.99  
% 1.43/0.99  inst_num_of_clauses:                    26
% 1.43/0.99  inst_num_in_passive:                    0
% 1.43/0.99  inst_num_in_active:                     0
% 1.43/0.99  inst_num_in_unprocessed:                26
% 1.43/0.99  inst_num_of_loops:                      0
% 1.43/0.99  inst_num_of_learning_restarts:          0
% 1.43/0.99  inst_num_moves_active_passive:          0
% 1.43/0.99  inst_lit_activity:                      0
% 1.43/0.99  inst_lit_activity_moves:                0
% 1.43/0.99  inst_num_tautologies:                   0
% 1.43/0.99  inst_num_prop_implied:                  0
% 1.43/0.99  inst_num_existing_simplified:           0
% 1.43/0.99  inst_num_eq_res_simplified:             0
% 1.43/0.99  inst_num_child_elim:                    0
% 1.43/0.99  inst_num_of_dismatching_blockings:      0
% 1.43/0.99  inst_num_of_non_proper_insts:           0
% 1.43/0.99  inst_num_of_duplicates:                 0
% 1.43/0.99  inst_inst_num_from_inst_to_res:         0
% 1.43/0.99  inst_dismatching_checking_time:         0.
% 1.43/0.99  
% 1.43/0.99  ------ Resolution
% 1.43/0.99  
% 1.43/0.99  res_num_of_clauses:                     0
% 1.43/0.99  res_num_in_passive:                     0
% 1.43/0.99  res_num_in_active:                      0
% 1.43/0.99  res_num_of_loops:                       86
% 1.43/0.99  res_forward_subset_subsumed:            0
% 1.43/0.99  res_backward_subset_subsumed:           0
% 1.43/0.99  res_forward_subsumed:                   0
% 1.43/0.99  res_backward_subsumed:                  0
% 1.43/0.99  res_forward_subsumption_resolution:     10
% 1.43/0.99  res_backward_subsumption_resolution:    4
% 1.43/0.99  res_clause_to_clause_subsumption:       106
% 1.43/0.99  res_orphan_elimination:                 0
% 1.43/0.99  res_tautology_del:                      18
% 1.43/0.99  res_num_eq_res_simplified:              3
% 1.43/0.99  res_num_sel_changes:                    0
% 1.43/0.99  res_moves_from_active_to_pass:          0
% 1.43/0.99  
% 1.43/0.99  ------ Superposition
% 1.43/0.99  
% 1.43/0.99  sup_time_total:                         0.
% 1.43/0.99  sup_time_generating:                    0.
% 1.43/0.99  sup_time_sim_full:                      0.
% 1.43/0.99  sup_time_sim_immed:                     0.
% 1.43/0.99  
% 1.43/0.99  sup_num_of_clauses:                     0
% 1.43/0.99  sup_num_in_active:                      0
% 1.43/0.99  sup_num_in_passive:                     0
% 1.43/0.99  sup_num_of_loops:                       0
% 1.43/0.99  sup_fw_superposition:                   0
% 1.43/0.99  sup_bw_superposition:                   0
% 1.43/0.99  sup_immediate_simplified:               0
% 1.43/0.99  sup_given_eliminated:                   0
% 1.43/0.99  comparisons_done:                       0
% 1.43/0.99  comparisons_avoided:                    0
% 1.43/0.99  
% 1.43/0.99  ------ Simplifications
% 1.43/0.99  
% 1.43/0.99  
% 1.43/0.99  sim_fw_subset_subsumed:                 0
% 1.43/0.99  sim_bw_subset_subsumed:                 0
% 1.43/0.99  sim_fw_subsumed:                        0
% 1.43/0.99  sim_bw_subsumed:                        0
% 1.43/0.99  sim_fw_subsumption_res:                 1
% 1.43/0.99  sim_bw_subsumption_res:                 0
% 1.43/0.99  sim_tautology_del:                      0
% 1.43/0.99  sim_eq_tautology_del:                   0
% 1.43/0.99  sim_eq_res_simp:                        0
% 1.43/0.99  sim_fw_demodulated:                     0
% 1.43/0.99  sim_bw_demodulated:                     0
% 1.43/0.99  sim_light_normalised:                   2
% 1.43/0.99  sim_joinable_taut:                      0
% 1.43/0.99  sim_joinable_simp:                      0
% 1.43/0.99  sim_ac_normalised:                      0
% 1.43/0.99  sim_smt_subsumption:                    0
% 1.43/0.99  
%------------------------------------------------------------------------------
