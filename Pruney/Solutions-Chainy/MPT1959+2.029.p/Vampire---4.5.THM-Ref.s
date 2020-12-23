%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  103 (1021 expanded)
%              Number of leaves         :   11 ( 163 expanded)
%              Depth                    :   32
%              Number of atoms          :  387 (7743 expanded)
%              Number of equality atoms :   53 ( 275 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(subsumption_resolution,[],[f176,f156])).

fof(f156,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f41,f153])).

fof(f153,plain,(
    sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f152,f41])).

fof(f152,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f149,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f149,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f148,f103])).

fof(f103,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f84,f38])).

fof(f38,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f84,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f41,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f148,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f147,f41])).

fof(f147,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f146,f40])).

fof(f40,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f146,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k3_yellow_0(sK0),X0)
      | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0)
      | sK1 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f145,f85])).

fof(f85,plain,
    ( m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f41,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f145,plain,(
    ! [X0] :
      ( sK1 = u1_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ r2_hidden(k3_yellow_0(sK0),X0)
      | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0)
      | ~ v13_waybel_0(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f144,f47])).

fof(f47,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f144,plain,(
    ! [X0] :
      ( sK1 = u1_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ r2_hidden(k3_yellow_0(sK0),X0)
      | ~ l1_orders_2(sK0)
      | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0)
      | ~ v13_waybel_0(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f143,f74])).

fof(f74,plain,(
    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f47,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f143,plain,(
    ! [X0] :
      ( sK1 = u1_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ r2_hidden(k3_yellow_0(sK0),X0)
      | ~ l1_orders_2(sK0)
      | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0)
      | ~ v13_waybel_0(X0,sK0) ) ),
    inference(resolution,[],[f134,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ l1_orders_2(X0)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f134,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK2(u1_struct_0(sK0),sK1))
    | sK1 = u1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK2(u1_struct_0(sK0),sK1))
    | sK1 = u1_struct_0(sK0)
    | sK1 = u1_struct_0(sK0) ),
    inference(superposition,[],[f129,f120])).

fof(f120,plain,
    ( sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f119,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f119,plain,
    ( sK1 = u1_struct_0(sK0)
    | v2_struct_0(sK0)
    | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f118,f47])).

fof(f118,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f117,f45])).

fof(f45,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f117,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f116,f44])).

fof(f44,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f116,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f109,f43])).

fof(f43,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f109,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f85,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

% (16967)Refutation not found, incomplete strategy% (16967)------------------------------
% (16967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16967)Termination reason: Refutation not found, incomplete strategy

% (16967)Memory used [KB]: 10746
% (16967)Time elapsed: 0.101 s
% (16967)------------------------------
% (16967)------------------------------
% (16979)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).

fof(f129,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f115,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK0,X0)
      | r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f78,f75])).

fof(f75,plain,(
    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f47,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

% (16991)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f78,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f77,f47])).

fof(f77,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | ~ r1_yellow_0(sK0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f76,f67])).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f76,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ l1_orders_2(sK0)
      | ~ r1_yellow_0(sK0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0)) ) ),
    inference(resolution,[],[f73,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X2)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

fof(f73,plain,(
    r1_yellow_0(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f72,f47])).

fof(f72,plain,
    ( ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f71,f42])).

fof(f71,plain,
    ( v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f70,f45])).

fof(f70,plain,
    ( ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f46,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f46,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f115,plain,
    ( r1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f114,f42])).

fof(f114,plain,
    ( sK1 = u1_struct_0(sK0)
    | v2_struct_0(sK0)
    | r1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f113,f47])).

fof(f113,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | r1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f112,f45])).

fof(f112,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | r1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f111,f44])).

fof(f111,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | r1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f108,f43])).

fof(f108,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | r1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f85,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f176,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f173,f69])).

fof(f69,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f173,plain,(
    v1_subset_1(sK1,sK1) ),
    inference(resolution,[],[f165,f154])).

fof(f154,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,sK1) ),
    inference(backward_demodulation,[],[f37,f153])).

fof(f37,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f165,plain,(
    r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(forward_demodulation,[],[f164,f153])).

fof(f164,plain,(
    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f160,f39])).

fof(f39,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f160,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f89,f153])).

fof(f89,plain,
    ( r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f74,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:15:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (16971)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.48  % (16970)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.48  % (16977)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.49  % (16971)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (16978)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (16967)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (16968)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (16976)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.49  % (16969)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (16975)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f177,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f176,f156])).
% 0.20/0.50  fof(f156,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.50    inference(backward_demodulation,[],[f41,f153])).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f152,f41])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f150])).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f149,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(flattening,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f148,f103])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    r2_hidden(k3_yellow_0(sK0),sK1) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f84,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ~v1_subset_1(sK1,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f15])).
% 0.20/0.50  fof(f15,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.50    inference(negated_conjecture,[],[f14])).
% 0.20/0.50  fof(f14,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    v1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f41,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f147,f41])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f146,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    v13_waybel_0(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    ( ! [X0] : (~v13_waybel_0(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(k3_yellow_0(sK0),X0) | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0) | sK1 = u1_struct_0(sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f145,f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f41,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK2(X0,X1),X0) | X0 = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    ( ! [X0] : (sK1 = u1_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),X0) | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0) | ~v13_waybel_0(X0,sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f144,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    l1_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    ( ! [X0] : (sK1 = u1_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),X0) | ~l1_orders_2(sK0) | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0) | ~v13_waybel_0(X0,sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f143,f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.20/0.50    inference(resolution,[],[f47,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    ( ! [X0] : (sK1 = u1_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),X0) | ~l1_orders_2(sK0) | r2_hidden(sK2(u1_struct_0(sK0),sK1),X0) | ~v13_waybel_0(X0,sK0)) )),
% 0.20/0.50    inference(resolution,[],[f134,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~l1_orders_2(X0) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.50    inference(flattening,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    r1_orders_2(sK0,k3_yellow_0(sK0),sK2(u1_struct_0(sK0),sK1)) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f133])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    r1_orders_2(sK0,k3_yellow_0(sK0),sK2(u1_struct_0(sK0),sK1)) | sK1 = u1_struct_0(sK0) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(superposition,[],[f129,f120])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f119,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    sK1 = u1_struct_0(sK0) | v2_struct_0(sK0) | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f118,f47])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    sK1 = u1_struct_0(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f117,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    v5_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    sK1 = u1_struct_0(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f116,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    v4_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    sK1 = u1_struct_0(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f109,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    v3_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    sK1 = u1_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))),
% 0.20/0.50    inference(resolution,[],[f85,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  % (16967)Refutation not found, incomplete strategy% (16967)------------------------------
% 0.20/0.50  % (16967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16967)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16967)Memory used [KB]: 10746
% 0.20/0.50  % (16967)Time elapsed: 0.101 s
% 0.20/0.50  % (16967)------------------------------
% 0.20/0.50  % (16967)------------------------------
% 0.20/0.50  % (16979)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f115,f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f78,f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.50    inference(resolution,[],[f47,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  % (16991)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f77,f47])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_orders_2(sK0) | ~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f76,f67])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~l1_orders_2(sK0) | ~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0))) )),
% 0.20/0.50    inference(resolution,[],[f73,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0) | ~r1_yellow_0(X0,X2) | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 0.20/0.50    inference(flattening,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    r1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f72,f47])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f71,f42])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    v2_struct_0(sK0) | ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f70,f45])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.50    inference(resolution,[],[f46,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | r1_yellow_0(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    v1_yellow_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    r1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) | sK1 = u1_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f114,f42])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    sK1 = u1_struct_0(sK0) | v2_struct_0(sK0) | r1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f113,f47])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    sK1 = u1_struct_0(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | r1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f112,f45])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    sK1 = u1_struct_0(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | r1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f111,f44])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    sK1 = u1_struct_0(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | r1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f108,f43])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    sK1 = u1_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | r1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))),
% 0.20/0.50    inference(resolution,[],[f85,f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_yellow_0(X0,k5_waybel_0(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f176,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.50    inference(resolution,[],[f173,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.20/0.50    inference(equality_resolution,[],[f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f173,plain,(
% 0.20/0.50    v1_subset_1(sK1,sK1)),
% 0.20/0.50    inference(resolution,[],[f165,f154])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,sK1)),
% 0.20/0.50    inference(backward_demodulation,[],[f37,f153])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.20/0.50    inference(forward_demodulation,[],[f164,f153])).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f160,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ~v1_xboole_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    v1_xboole_0(sK1) | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.20/0.50    inference(backward_demodulation,[],[f89,f153])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.50    inference(resolution,[],[f74,f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (16971)------------------------------
% 0.20/0.50  % (16971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16971)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (16971)Memory used [KB]: 6140
% 0.20/0.50  % (16971)Time elapsed: 0.100 s
% 0.20/0.50  % (16971)------------------------------
% 0.20/0.50  % (16971)------------------------------
% 0.20/0.50  % (16988)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (16965)Success in time 0.15 s
%------------------------------------------------------------------------------
