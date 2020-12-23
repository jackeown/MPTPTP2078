%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2046+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:39 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 137 expanded)
%              Number of leaves         :    7 (  43 expanded)
%              Depth                    :   18
%              Number of atoms          :  200 ( 676 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10478,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10477,f4929])).

fof(f4929,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f4733])).

fof(f4733,plain,
    ( ~ r2_waybel_7(sK9,k1_yellow19(sK9,sK10),sK10)
    & m1_subset_1(sK10,u1_struct_0(sK9))
    & l1_pre_topc(sK9)
    & v2_pre_topc(sK9)
    & ~ v2_struct_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f4521,f4732,f4731])).

fof(f4731,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_waybel_7(X0,k1_yellow19(X0,X1),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r2_waybel_7(sK9,k1_yellow19(sK9,X1),X1)
          & m1_subset_1(X1,u1_struct_0(sK9)) )
      & l1_pre_topc(sK9)
      & v2_pre_topc(sK9)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f4732,plain,
    ( ? [X1] :
        ( ~ r2_waybel_7(sK9,k1_yellow19(sK9,X1),X1)
        & m1_subset_1(X1,u1_struct_0(sK9)) )
   => ( ~ r2_waybel_7(sK9,k1_yellow19(sK9,sK10),sK10)
      & m1_subset_1(sK10,u1_struct_0(sK9)) ) ),
    introduced(choice_axiom,[])).

fof(f4521,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_waybel_7(X0,k1_yellow19(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4520])).

fof(f4520,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_waybel_7(X0,k1_yellow19(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4496])).

fof(f4496,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r2_waybel_7(X0,k1_yellow19(X0,X1),X1) ) ) ),
    inference(negated_conjecture,[],[f4495])).

fof(f4495,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_waybel_7(X0,k1_yellow19(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_yellow19)).

fof(f10477,plain,(
    v2_struct_0(sK9) ),
    inference(subsumption_resolution,[],[f10476,f4930])).

fof(f4930,plain,(
    v2_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f4733])).

fof(f10476,plain,
    ( ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9) ),
    inference(subsumption_resolution,[],[f10475,f4931])).

fof(f4931,plain,(
    l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f4733])).

fof(f10475,plain,
    ( ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9) ),
    inference(subsumption_resolution,[],[f10465,f4932])).

fof(f4932,plain,(
    m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f4733])).

fof(f10465,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9) ),
    inference(resolution,[],[f10459,f4955])).

fof(f4955,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4531])).

fof(f4531,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4530])).

fof(f4530,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4489])).

fof(f4489,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_yellow19)).

fof(f10459,plain,(
    ~ v13_waybel_0(k1_yellow19(sK9,sK10),k3_yellow_1(k2_struct_0(sK9))) ),
    inference(subsumption_resolution,[],[f10448,f4932])).

fof(f10448,plain,
    ( ~ v13_waybel_0(k1_yellow19(sK9,sK10),k3_yellow_1(k2_struct_0(sK9)))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(resolution,[],[f5948,f5438])).

fof(f5438,plain,(
    ! [X18] :
      ( m1_subset_1(k1_yellow19(sK9,X18),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK9)))))
      | ~ m1_subset_1(X18,u1_struct_0(sK9)) ) ),
    inference(global_subsumption,[],[f4931,f4930,f5301])).

fof(f5301,plain,(
    ! [X18] :
      ( m1_subset_1(k1_yellow19(sK9,X18),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK9)))))
      | ~ m1_subset_1(X18,u1_struct_0(sK9))
      | ~ l1_pre_topc(sK9)
      | ~ v2_pre_topc(sK9) ) ),
    inference(resolution,[],[f4929,f4956])).

fof(f4956,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4533])).

fof(f4533,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4532])).

fof(f4532,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4488])).

fof(f4488,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow19)).

fof(f5948,plain,
    ( ~ m1_subset_1(k1_yellow19(sK9,sK10),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK9)))))
    | ~ v13_waybel_0(k1_yellow19(sK9,sK10),k3_yellow_1(k2_struct_0(sK9))) ),
    inference(subsumption_resolution,[],[f5947,f4929])).

fof(f5947,plain,
    ( ~ m1_subset_1(k1_yellow19(sK9,sK10),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK9)))))
    | ~ v13_waybel_0(k1_yellow19(sK9,sK10),k3_yellow_1(k2_struct_0(sK9)))
    | v2_struct_0(sK9) ),
    inference(subsumption_resolution,[],[f5946,f4930])).

fof(f5946,plain,
    ( ~ m1_subset_1(k1_yellow19(sK9,sK10),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK9)))))
    | ~ v13_waybel_0(k1_yellow19(sK9,sK10),k3_yellow_1(k2_struct_0(sK9)))
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9) ),
    inference(subsumption_resolution,[],[f5945,f4931])).

fof(f5945,plain,
    ( ~ m1_subset_1(k1_yellow19(sK9,sK10),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK9)))))
    | ~ v13_waybel_0(k1_yellow19(sK9,sK10),k3_yellow_1(k2_struct_0(sK9)))
    | ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9) ),
    inference(subsumption_resolution,[],[f5944,f4932])).

fof(f5944,plain,
    ( ~ m1_subset_1(k1_yellow19(sK9,sK10),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK9)))))
    | ~ v13_waybel_0(k1_yellow19(sK9,sK10),k3_yellow_1(k2_struct_0(sK9)))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9) ),
    inference(subsumption_resolution,[],[f5939,f5269])).

fof(f5269,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f5142])).

fof(f5142,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4857])).

fof(f4857,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f4856])).

fof(f4856,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f5939,plain,
    ( ~ r1_tarski(k1_yellow19(sK9,sK10),k1_yellow19(sK9,sK10))
    | ~ m1_subset_1(k1_yellow19(sK9,sK10),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK9)))))
    | ~ v13_waybel_0(k1_yellow19(sK9,sK10),k3_yellow_1(k2_struct_0(sK9)))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9) ),
    inference(resolution,[],[f4933,f4951])).

fof(f4951,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X2,X1)
      | ~ r1_tarski(k1_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4744])).

fof(f4744,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_waybel_7(X0,X2,X1)
                  | ~ r1_tarski(k1_yellow19(X0,X1),X2) )
                & ( r1_tarski(k1_yellow19(X0,X1),X2)
                  | ~ r2_waybel_7(X0,X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4529])).

fof(f4529,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4528])).

fof(f4528,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4494])).

fof(f4494,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow19)).

fof(f4933,plain,(
    ~ r2_waybel_7(sK9,k1_yellow19(sK9,sK10),sK10) ),
    inference(cnf_transformation,[],[f4733])).
%------------------------------------------------------------------------------
