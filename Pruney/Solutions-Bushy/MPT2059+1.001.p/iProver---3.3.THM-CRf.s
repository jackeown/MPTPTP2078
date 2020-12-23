%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2059+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:06 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  183 (1401 expanded)
%              Number of clauses        :  125 ( 311 expanded)
%              Number of leaves         :   12 ( 382 expanded)
%              Depth                    :   33
%              Number of atoms          : 1218 (14275 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(pure_predicate_removal,[],[f2])).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f39,plain,(
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
    inference(cnf_transformation,[],[f17])).

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
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(pure_predicate_removal,[],[f4])).

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

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f20])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

cnf(c_3,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_478,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_20])).

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

cnf(c_2,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f39])).

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
    inference(resolution_lifted,[status(thm)],[c_2,c_16])).

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

cnf(c_4,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f43])).

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
    inference(resolution_lifted,[status(thm)],[c_4,c_16])).

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
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
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
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_430,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_434,plain,
    ( v2_struct_0(X0)
    | ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_22,c_20])).

cnf(c_435,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_434])).

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
    inference(resolution_lifted,[status(thm)],[c_166,c_435])).

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

cnf(c_1,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f40])).

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
    inference(resolution_lifted,[status(thm)],[c_1,c_16])).

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

cnf(c_59,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

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
    inference(global_propositional_subsumption,[status(thm)],[c_1847,c_22,c_20,c_59])).

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

cnf(c_6,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1963,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_479])).

cnf(c_1964,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_1963])).

cnf(c_50,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1966,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1964,c_22,c_20,c_50,c_59])).

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
    inference(global_propositional_subsumption,[status(thm)],[c_2256,c_20,c_15,c_59,c_66])).

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
    inference(global_propositional_subsumption,[status(thm)],[c_1953,c_22,c_20,c_17,c_16,c_15,c_59,c_353])).

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
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_396,plain,
    ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_397,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_401,plain,
    ( v2_struct_0(X0)
    | r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_22,c_20])).

cnf(c_402,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_401])).

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
    inference(resolution_lifted,[status(thm)],[c_168,c_402])).

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
    inference(global_propositional_subsumption,[status(thm)],[c_1889,c_22,c_20,c_59])).

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
    inference(global_propositional_subsumption,[status(thm)],[c_2233,c_20,c_15,c_59,c_66])).

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
