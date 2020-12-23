%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 681 expanded)
%              Number of leaves         :   14 ( 212 expanded)
%              Depth                    :   45
%              Number of atoms          : 1005 (7749 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :   21 (   9 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(subsumption_resolution,[],[f201,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f38,f37,f36])).

fof(f36,plain,
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
    ( ? [X1] :
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
   => ( ? [X2] :
          ( ( ~ r2_waybel_7(sK0,sK1,X2)
            | ~ r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
          & ( r2_waybel_7(sK0,sK1,X2)
            | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ( ~ r2_waybel_7(sK0,sK1,X2)
          | ~ r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
        & ( r2_waybel_7(sK0,sK1,X2)
          | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r2_waybel_7(sK0,sK1,sK2)
        | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
      & ( r2_waybel_7(sK0,sK1,sK2)
        | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow19)).

fof(f201,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f200,f76])).

fof(f76,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f56,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f200,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f199,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

% (1302)Refutation not found, incomplete strategy% (1302)------------------------------
% (1302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1302)Termination reason: Refutation not found, incomplete strategy

% (1302)Memory used [KB]: 10874
% (1302)Time elapsed: 0.109 s
% (1302)------------------------------
% (1302)------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f199,plain,(
    v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f198,f76])).

fof(f198,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f197,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f197,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f194,f57])).

fof(f57,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f194,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),u1_struct_0(sK0))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(resolution,[],[f193,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f193,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f192,f44])).

fof(f192,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f191,f76])).

fof(f191,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f185,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f95,f47])).

fof(f47,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f94,f49])).

fof(f49,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f91,f50])).

fof(f50,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f67,f51])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).

fof(f185,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f184,f44])).

fof(f184,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f183,f76])).

fof(f183,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f171,f102])).

fof(f102,plain,(
    ! [X0] :
      ( v4_orders_2(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f101,f47])).

fof(f101,plain,(
    ! [X0] :
      ( v4_orders_2(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f100,f49])).

fof(f100,plain,(
    ! [X0] :
      ( v4_orders_2(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f97,f50])).

fof(f97,plain,(
    ! [X0] :
      ( v4_orders_2(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f68,f51])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f171,plain,
    ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f170,f44])).

fof(f170,plain,
    ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f169,f76])).

fof(f169,plain,
    ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,
    ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f163,f109])).

fof(f109,plain,(
    ! [X0] :
      ( v7_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f108,f47])).

fof(f108,plain,(
    ! [X0] :
      ( v7_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f107,f48])).

fof(f48,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f107,plain,(
    ! [X0] :
      ( v7_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f106,f49])).

fof(f106,plain,(
    ! [X0] :
      ( v7_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f103,f50])).

fof(f103,plain,(
    ! [X0] :
      ( v7_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f72,f51])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).

fof(f163,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f162,f44])).

fof(f162,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f161,f76])).

fof(f161,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f160,f47])).

fof(f160,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f159,f49])).

fof(f159,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f158,f50])).

fof(f158,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f157,f51])).

fof(f157,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f156,f70])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(f156,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f155,f135])).

fof(f135,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f134,f47])).

fof(f134,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f133,f48])).

fof(f133,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f132,f49])).

fof(f132,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f131,f50])).

fof(f131,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f130,f51])).

fof(f130,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f129,f44])).

fof(f129,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f128,f45])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f128,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f127,f46])).

fof(f127,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f126,f52])).

fof(f52,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f126,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ r2_waybel_7(sK0,sK1,sK2) ),
    inference(resolution,[],[f114,f54])).

fof(f54,plain,
    ( ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ r2_waybel_7(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
      | ~ r2_waybel_7(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(k3_yellow19(X0,k2_struct_0(X0),X1),X0)
      | ~ v7_waybel_0(k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ v4_orders_2(k3_yellow19(X0,k2_struct_0(X0),X1))
      | v2_struct_0(k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f113,f56])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_7(X0,X1,X2)
      | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(k3_yellow19(X0,k2_struct_0(X0),X1),X0)
      | ~ v7_waybel_0(k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ v4_orders_2(k3_yellow19(X0,k2_struct_0(X0),X1))
      | v2_struct_0(k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_7(X0,X1,X2)
      | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(k3_yellow19(X0,k2_struct_0(X0),X1),X0)
      | ~ v7_waybel_0(k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ v4_orders_2(k3_yellow19(X0,k2_struct_0(X0),X1))
      | v2_struct_0(k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f59,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow19)).

fof(f155,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f154,f47])).

fof(f154,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f153,f48])).

fof(f153,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f152,f49])).

fof(f152,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f151,f50])).

fof(f151,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f150,f51])).

fof(f150,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f149,f44])).

fof(f149,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f148,f45])).

fof(f148,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f147,f46])).

fof(f147,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f146,f52])).

fof(f146,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | r2_waybel_7(sK0,sK1,sK2) ),
    inference(resolution,[],[f115,f53])).

fof(f53,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | r2_waybel_7(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f115,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k10_yellow_6(X3,k3_yellow19(X3,k2_struct_0(X3),X4)))
      | r2_waybel_7(X3,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4),X3)
      | ~ v7_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ v4_orders_2(k3_yellow19(X3,k2_struct_0(X3),X4))
      | v2_struct_0(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X3)))))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X3)))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X3)))
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X3))))
      | v1_xboole_0(X4) ) ),
    inference(subsumption_resolution,[],[f112,f56])).

fof(f112,plain,(
    ! [X4,X5,X3] :
      ( r2_waybel_7(X3,X4,X5)
      | ~ r2_hidden(X5,k10_yellow_6(X3,k3_yellow19(X3,k2_struct_0(X3),X4)))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4),X3)
      | ~ v7_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ v4_orders_2(k3_yellow19(X3,k2_struct_0(X3),X4))
      | v2_struct_0(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X3)))))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X3)))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X3)))
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X3))))
      | v1_xboole_0(X4)
      | ~ l1_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X4,X5,X3] :
      ( r2_waybel_7(X3,X4,X5)
      | ~ r2_hidden(X5,k10_yellow_6(X3,k3_yellow19(X3,k2_struct_0(X3),X4)))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4),X3)
      | ~ v7_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ v4_orders_2(k3_yellow19(X3,k2_struct_0(X3),X4))
      | v2_struct_0(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X3)))))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X3)))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X3)))
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X3))))
      | v1_xboole_0(X4)
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f58,f61])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:50:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (1286)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (1286)Refutation not found, incomplete strategy% (1286)------------------------------
% 0.22/0.52  % (1286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1286)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1286)Memory used [KB]: 10746
% 0.22/0.52  % (1286)Time elapsed: 0.094 s
% 0.22/0.52  % (1286)------------------------------
% 0.22/0.52  % (1286)------------------------------
% 0.22/0.52  % (1283)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (1302)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.53  % (1294)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (1279)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (1275)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (1283)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f202,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f201,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ~v2_struct_0(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    (((~r2_waybel_7(sK0,sK1,sK2) | ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f38,f37,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_waybel_7(sK0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & (r2_waybel_7(sK0,X1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ? [X1] : (? [X2] : ((~r2_waybel_7(sK0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & (r2_waybel_7(sK0,X1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r2_waybel_7(sK0,sK1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ? [X2] : ((~r2_waybel_7(sK0,sK1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(X2,u1_struct_0(sK0))) => ((~r2_waybel_7(sK0,sK1,sK2) | ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 0.22/0.54    inference(negated_conjecture,[],[f12])).
% 0.22/0.54  fof(f12,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow19)).
% 0.22/0.54  fof(f201,plain,(
% 0.22/0.54    v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f200,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    l1_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f56,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    l1_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f199,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  % (1302)Refutation not found, incomplete strategy% (1302)------------------------------
% 0.22/0.54  % (1302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1302)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1302)Memory used [KB]: 10874
% 0.22/0.54  % (1302)Time elapsed: 0.109 s
% 0.22/0.54  % (1302)------------------------------
% 0.22/0.54  % (1302)------------------------------
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.22/0.54  fof(f199,plain,(
% 0.22/0.54    v1_xboole_0(k2_struct_0(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f198,f76])).
% 0.22/0.54  fof(f198,plain,(
% 0.22/0.54    v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f197,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f197,plain,(
% 0.22/0.54    ~r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0)),
% 0.22/0.54    inference(superposition,[],[f194,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.54  fof(f194,plain,(
% 0.22/0.54    ~r1_tarski(k2_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(k2_struct_0(sK0))),
% 0.22/0.54    inference(resolution,[],[f193,f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f193,plain,(
% 0.22/0.54    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f192,f44])).
% 0.22/0.54  fof(f192,plain,(
% 0.22/0.54    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f191,f76])).
% 0.22/0.54  fof(f191,plain,(
% 0.22/0.54    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f186])).
% 0.22/0.54  fof(f186,plain,(
% 0.22/0.54    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f185,f96])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ( ! [X0] : (~v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f95,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ~v1_xboole_0(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X0] : (~v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f94,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ( ! [X0] : (~v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f91,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X0] : (~v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(resolution,[],[f67,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f184,f44])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f183,f76])).
% 0.22/0.54  fof(f183,plain,(
% 0.22/0.54    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f178])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f171,f102])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ( ! [X0] : (v4_orders_2(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f101,f47])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ( ! [X0] : (v4_orders_2(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f100,f49])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ( ! [X0] : (v4_orders_2(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f97,f50])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X0] : (v4_orders_2(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(resolution,[],[f68,f51])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | v4_orders_2(k3_yellow19(X0,X1,X2)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f170,f44])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f169,f76])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f164])).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f163,f109])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    ( ! [X0] : (v7_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f108,f47])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    ( ! [X0] : (v7_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f107,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    ( ! [X0] : (v7_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f106,f49])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    ( ! [X0] : (v7_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f103,f50])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    ( ! [X0] : (v7_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(resolution,[],[f72,f51])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).
% 0.22/0.54  fof(f163,plain,(
% 0.22/0.54    ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f162,f44])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f161,f76])).
% 0.22/0.54  fof(f161,plain,(
% 0.22/0.54    ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f160,f47])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f159,f49])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f158,f50])).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f157,f51])).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f156,f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.22/0.54    inference(subsumption_resolution,[],[f155,f135])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~r2_waybel_7(sK0,sK1,sK2) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.22/0.54    inference(subsumption_resolution,[],[f134,f47])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    ~r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f133,f48])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    ~r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f132,f49])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    ~r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f131,f50])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    ~r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f130,f51])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    ~r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f129,f44])).
% 0.22/0.54  fof(f129,plain,(
% 0.22/0.54    ~r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f128,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    v2_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    ~r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f127,f46])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    ~r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f126,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    ~r2_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f125])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    ~r2_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~r2_waybel_7(sK0,sK1,sK2)),
% 0.22/0.54    inference(resolution,[],[f114,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | ~r2_waybel_7(sK0,sK1,sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) | ~r2_waybel_7(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(k3_yellow19(X0,k2_struct_0(X0),X1),X0) | ~v7_waybel_0(k3_yellow19(X0,k2_struct_0(X0),X1)) | ~v4_orders_2(k3_yellow19(X0,k2_struct_0(X0),X1)) | v2_struct_0(k3_yellow19(X0,k2_struct_0(X0),X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f113,f56])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(k3_yellow19(X0,k2_struct_0(X0),X1),X0) | ~v7_waybel_0(k3_yellow19(X0,k2_struct_0(X0),X1)) | ~v4_orders_2(k3_yellow19(X0,k2_struct_0(X0),X1)) | v2_struct_0(k3_yellow19(X0,k2_struct_0(X0),X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f110])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(k3_yellow19(X0,k2_struct_0(X0),X1),X0) | ~v7_waybel_0(k3_yellow19(X0,k2_struct_0(X0),X1)) | ~v4_orders_2(k3_yellow19(X0,k2_struct_0(X0),X1)) | v2_struct_0(k3_yellow19(X0,k2_struct_0(X0),X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(superposition,[],[f59,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow19)).
% 0.22/0.55  fof(f155,plain,(
% 0.22/0.55    r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.22/0.55    inference(subsumption_resolution,[],[f154,f47])).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v1_xboole_0(sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f153,f48])).
% 0.22/0.55  fof(f153,plain,(
% 0.22/0.55    r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f152,f49])).
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f151,f50])).
% 0.22/0.55  fof(f151,plain,(
% 0.22/0.55    r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f150,f51])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f149,f44])).
% 0.22/0.55  fof(f149,plain,(
% 0.22/0.55    r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f148,f45])).
% 0.22/0.55  fof(f148,plain,(
% 0.22/0.55    r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f147,f46])).
% 0.22/0.55  fof(f147,plain,(
% 0.22/0.55    r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f146,f52])).
% 0.22/0.55  fof(f146,plain,(
% 0.22/0.55    r2_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1)),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f143])).
% 0.22/0.55  fof(f143,plain,(
% 0.22/0.55    r2_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | r2_waybel_7(sK0,sK1,sK2)),
% 0.22/0.55    inference(resolution,[],[f115,f53])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | r2_waybel_7(sK0,sK1,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f39])).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    ( ! [X4,X5,X3] : (~r2_hidden(X5,k10_yellow_6(X3,k3_yellow19(X3,k2_struct_0(X3),X4))) | r2_waybel_7(X3,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4),X3) | ~v7_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4)) | ~v4_orders_2(k3_yellow19(X3,k2_struct_0(X3),X4)) | v2_struct_0(k3_yellow19(X3,k2_struct_0(X3),X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X3))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X3))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X3))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X3)))) | v1_xboole_0(X4)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f112,f56])).
% 0.22/0.55  fof(f112,plain,(
% 0.22/0.55    ( ! [X4,X5,X3] : (r2_waybel_7(X3,X4,X5) | ~r2_hidden(X5,k10_yellow_6(X3,k3_yellow19(X3,k2_struct_0(X3),X4))) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4),X3) | ~v7_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4)) | ~v4_orders_2(k3_yellow19(X3,k2_struct_0(X3),X4)) | v2_struct_0(k3_yellow19(X3,k2_struct_0(X3),X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X3))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X3))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X3))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X3)))) | v1_xboole_0(X4) | ~l1_struct_0(X3)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f111])).
% 0.22/0.55  fof(f111,plain,(
% 0.22/0.55    ( ! [X4,X5,X3] : (r2_waybel_7(X3,X4,X5) | ~r2_hidden(X5,k10_yellow_6(X3,k3_yellow19(X3,k2_struct_0(X3),X4))) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4),X3) | ~v7_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4)) | ~v4_orders_2(k3_yellow19(X3,k2_struct_0(X3),X4)) | v2_struct_0(k3_yellow19(X3,k2_struct_0(X3),X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X3))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X3))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X3))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X3)))) | v1_xboole_0(X4) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.22/0.55    inference(superposition,[],[f58,f61])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f40])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (1283)------------------------------
% 0.22/0.55  % (1283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (1283)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (1283)Memory used [KB]: 1918
% 0.22/0.55  % (1283)Time elapsed: 0.117 s
% 0.22/0.55  % (1283)------------------------------
% 0.22/0.55  % (1283)------------------------------
% 0.22/0.55  % (1273)Success in time 0.183 s
%------------------------------------------------------------------------------
