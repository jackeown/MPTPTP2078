%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2065+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:07 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  137 (3049 expanded)
%              Number of leaves         :    8 ( 540 expanded)
%              Depth                    :   71
%              Number of atoms          :  780 (26076 expanded)
%              Number of equality atoms :   29 ( 332 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(subsumption_resolution,[],[f209,f168])).

fof(f168,plain,(
    ~ r2_hidden(sK3,sK1) ),
    inference(resolution,[],[f165,f26])).

fof(f26,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r3_waybel_9(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r3_waybel_9(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( ( l1_waybel_0(X2,X0)
                    & v7_waybel_0(X2)
                    & v4_orders_2(X2)
                    & ~ v2_struct_0(X2) )
                 => ( r1_waybel_0(X0,X2,X1)
                   => ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r3_waybel_9(X0,X2,X3)
                         => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( r1_waybel_0(X0,X2,X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r3_waybel_9(X0,X2,X3)
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow19)).

fof(f165,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f163,f32])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f163,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f160])).

fof(f160,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f72,f146])).

fof(f146,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f145,f32])).

fof(f145,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f135,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(resolution,[],[f35,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f135,plain,
    ( v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f134,f35])).

% (12320)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (12324)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f134,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f131,f32])).

fof(f131,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f130,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f130,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f129,f32])).

fof(f129,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f122,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_pre_topc(sK0,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(resolution,[],[f68,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f68,plain,(
    ! [X1] :
      ( r1_tarski(X1,k2_pre_topc(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f122,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f121,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f121,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),X0)
      | v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = k2_pre_topc(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f119,f32])).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(sK1,sK0)
      | ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = k2_pre_topc(sK0,sK1) ) ),
    inference(resolution,[],[f118,f71])).

fof(f118,plain,(
    ! [X0] :
      ( r1_tarski(k2_pre_topc(sK0,sK1),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(sK1,sK0)
      | ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),X0) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),sK1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(sK1,sK0)
      | r1_tarski(k2_pre_topc(sK0,sK1),sK1)
      | r1_tarski(k2_pre_topc(sK0,sK1),sK1) ) ),
    inference(resolution,[],[f115,f51])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X1,sK1),k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(sK5(X1,sK1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(sK1,sK0)
      | r1_tarski(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f114,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(X1,sK1),X0)
      | ~ r2_hidden(sK5(X1,sK1),k2_pre_topc(sK0,sK1))
      | v4_pre_topc(sK1,sK0)
      | r1_tarski(X1,sK1)
      | ~ m1_subset_1(sK5(X1,sK1),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f113,f32])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(X1,sK1),X0)
      | ~ r2_hidden(sK5(X1,sK1),k2_pre_topc(sK0,sK1))
      | v4_pre_topc(sK1,sK0)
      | r1_tarski(X1,sK1)
      | ~ m1_subset_1(sK5(X1,sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(X1,sK1),X0)
      | ~ r2_hidden(sK5(X1,sK1),k2_pre_topc(sK0,sK1))
      | v4_pre_topc(sK1,sK0)
      | ~ r2_hidden(sK5(X1,sK1),X0)
      | r1_tarski(X1,sK1)
      | ~ m1_subset_1(sK5(X1,sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(condensation,[],[f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(X1,sK1),X0)
      | ~ r2_hidden(sK5(X1,sK1),k2_pre_topc(sK0,sK1))
      | v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(X1,sK1),X2)
      | r1_tarski(X1,sK1)
      | ~ m1_subset_1(sK5(X1,sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(X1,sK1),X0)
      | ~ r2_hidden(sK5(X1,sK1),k2_pre_topc(sK0,sK1))
      | v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(X1,sK1),X2)
      | r1_tarski(X1,sK1)
      | ~ m1_subset_1(sK5(X1,sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(X1,sK1),k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f109,f78])).

fof(f78,plain,(
    ! [X6,X7] :
      ( r3_waybel_9(sK0,sK4(sK0,X6,X7),X7)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X7,k2_pre_topc(sK0,X6)) ) ),
    inference(subsumption_resolution,[],[f66,f35])).

fof(f66,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | r3_waybel_9(sK0,sK4(sK0,X6,X7),X7)
      | ~ r2_hidden(X7,k2_pre_topc(sK0,X6)) ) ),
    inference(subsumption_resolution,[],[f61,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X6,X7] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | r3_waybel_9(sK0,sK4(sK0,X6,X7),X7)
      | ~ r2_hidden(X7,k2_pre_topc(sK0,X6)) ) ),
    inference(resolution,[],[f34,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_waybel_9(X0,sK4(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow19)).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_waybel_9(sK0,sK4(sK0,sK1,X0),sK5(X2,sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(X2,sK1),X3)
      | r1_tarski(X2,sK1) ) ),
    inference(resolution,[],[f103,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X2,sK1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X0),X2)
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f102,f55])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X1),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f101,f55])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X1),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f100,f33])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X1),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f99,f32])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X1),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f98,f35])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X1),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f97,f34])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X1),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X1),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f95,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK4(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK4(sK0,sK1,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X0),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f94,f55])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK4(sK0,sK1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X0),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f93,f33])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK4(sK0,sK1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X0),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f92,f32])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK4(sK0,sK1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X0),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f91,f35])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK4(sK0,sK1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X0),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f90,f34])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK4(sK0,sK1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X0),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK4(sK0,sK1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X0),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f88,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(sK4(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(sK4(sK0,sK1,X0))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK4(sK0,sK1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X0),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f87,f55])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v4_orders_2(sK4(sK0,sK1,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK4(sK0,sK1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X0),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f86,f32])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v4_orders_2(sK4(sK0,sK1,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK4(sK0,sK1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X0),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v4_orders_2(sK4(sK0,sK1,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK4(sK0,sK1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X0),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f84,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v7_waybel_0(sK4(sK0,X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f63,f35])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v7_waybel_0(sK4(sK0,X0,X1))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f58,f33])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v7_waybel_0(sK4(sK0,X0,X1))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f34,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v7_waybel_0(sK4(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(sK4(sK0,sK1,X1))
      | ~ r2_hidden(X1,X0)
      | ~ v4_orders_2(sK4(sK0,sK1,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK4(sK0,sK1,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X1),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f83,f55])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,X0)
      | ~ v4_orders_2(sK4(sK0,sK1,X1))
      | ~ v7_waybel_0(sK4(sK0,sK1,X1))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK4(sK0,sK1,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X1),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f82,f32])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,X0)
      | ~ v4_orders_2(sK4(sK0,sK1,X1))
      | ~ v7_waybel_0(sK4(sK0,sK1,X1))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK4(sK0,sK1,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X1),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,X0)
      | ~ v4_orders_2(sK4(sK0,sK1,X1))
      | ~ v7_waybel_0(sK4(sK0,sK1,X1))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK4(sK0,sK1,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X1),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f80,f75])).

fof(f75,plain,(
    ! [X2,X3] :
      ( l1_waybel_0(sK4(sK0,X2,X3),sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X3,k2_pre_topc(sK0,X2)) ) ),
    inference(subsumption_resolution,[],[f64,f35])).

fof(f64,plain,(
    ! [X2,X3] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | l1_waybel_0(sK4(sK0,X2,X3),sK0)
      | ~ r2_hidden(X3,k2_pre_topc(sK0,X2)) ) ),
    inference(subsumption_resolution,[],[f59,f33])).

fof(f59,plain,(
    ! [X2,X3] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | l1_waybel_0(sK4(sK0,X2,X3),sK0)
      | ~ r2_hidden(X3,k2_pre_topc(sK0,X2)) ) ),
    inference(resolution,[],[f34,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | l1_waybel_0(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ v4_orders_2(sK4(sK0,sK1,X0))
      | ~ v7_waybel_0(sK4(sK0,sK1,X0))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK4(sK0,sK1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X0),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f79,f32])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ v4_orders_2(sK4(sK0,sK1,X0))
      | ~ v7_waybel_0(sK4(sK0,sK1,X0))
      | ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
      | v2_struct_0(sK4(sK0,sK1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X0),X2)
      | r2_hidden(X2,sK1)
      | v4_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f77,f23])).

fof(f23,plain,(
    ! [X2,X3] :
      ( ~ r1_waybel_0(sK0,X2,sK1)
      | ~ v4_orders_2(X2)
      | ~ v7_waybel_0(X2)
      | ~ l1_waybel_0(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X2,X3)
      | r2_hidden(X3,sK1)
      | v4_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(sK0,sK4(sK0,X0,X1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f76,f55])).

fof(f76,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_waybel_0(sK0,sK4(sK0,X4,X5),X4)
      | ~ r2_hidden(X5,k2_pre_topc(sK0,X4)) ) ),
    inference(subsumption_resolution,[],[f65,f35])).

fof(f65,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r1_waybel_0(sK0,sK4(sK0,X4,X5),X4)
      | ~ r2_hidden(X5,k2_pre_topc(sK0,X4)) ) ),
    inference(subsumption_resolution,[],[f60,f33])).

fof(f60,plain,(
    ! [X4,X5] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r1_waybel_0(sK0,sK4(sK0,X4,X5),X4)
      | ~ r2_hidden(X5,k2_pre_topc(sK0,X4)) ) ),
    inference(resolution,[],[f34,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_waybel_0(X0,sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,(
    ! [X8] :
      ( k2_pre_topc(sK0,X8) != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X8,sK0) ) ),
    inference(subsumption_resolution,[],[f62,f35])).

fof(f62,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k2_pre_topc(sK0,X8) != X8
      | v4_pre_topc(X8,sK0) ) ),
    inference(resolution,[],[f34,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f209,plain,(
    r2_hidden(sK3,sK1) ),
    inference(forward_demodulation,[],[f208,f146])).

fof(f208,plain,(
    r2_hidden(sK3,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f207,f32])).

fof(f207,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f206,f173])).

fof(f173,plain,(
    r1_waybel_0(sK0,sK2,sK1) ),
    inference(resolution,[],[f165,f31])).

fof(f31,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_waybel_0(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f206,plain,(
    ! [X0] :
      ( ~ r1_waybel_0(sK0,sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK3,k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f205,f166])).

fof(f166,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(resolution,[],[f165,f24])).

fof(f24,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f205,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ r1_waybel_0(sK0,sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK3,k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f204,f167])).

fof(f167,plain,(
    r3_waybel_9(sK0,sK2,sK3) ),
    inference(resolution,[],[f165,f25])).

fof(f25,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r3_waybel_9(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f204,plain,(
    ! [X0,X1] :
      ( ~ r3_waybel_9(sK0,sK2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_waybel_0(sK0,sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f203,f34])).

fof(f203,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | ~ r1_waybel_0(sK0,sK2,X0)
      | ~ r3_waybel_9(sK0,sK2,X1)
      | r2_hidden(X1,k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f202,f33])).

fof(f202,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ r1_waybel_0(sK0,sK2,X0)
      | ~ r3_waybel_9(sK0,sK2,X1)
      | r2_hidden(X1,k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f201,f35])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ r1_waybel_0(sK0,sK2,X0)
      | ~ r3_waybel_9(sK0,sK2,X1)
      | r2_hidden(X1,k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f177,f172])).

fof(f172,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(resolution,[],[f165,f30])).

fof(f30,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | l1_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ r1_waybel_0(X0,sK2,X1)
      | ~ r3_waybel_9(X0,sK2,X2)
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f176,f170])).

fof(f170,plain,(
    v4_orders_2(sK2) ),
    inference(resolution,[],[f165,f28])).

fof(f28,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_orders_2(sK2)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK2,X0)
      | ~ r1_waybel_0(X0,sK2,X1)
      | ~ r3_waybel_9(X0,sK2,X2)
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f175,f169])).

fof(f169,plain,(
    ~ v2_struct_0(sK2) ),
    inference(resolution,[],[f165,f27])).

fof(f27,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK2,X0)
      | ~ r1_waybel_0(X0,sK2,X1)
      | ~ r3_waybel_9(X0,sK2,X2)
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(resolution,[],[f171,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v7_waybel_0(X3)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X3,X0)
      | ~ r1_waybel_0(X0,X3,X1)
      | ~ r3_waybel_9(X0,X3,X2)
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f171,plain,(
    v7_waybel_0(sK2) ),
    inference(resolution,[],[f165,f29])).

fof(f29,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f12])).

%------------------------------------------------------------------------------
