%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 266 expanded)
%              Number of leaves         :    8 (  50 expanded)
%              Depth                    :   20
%              Number of atoms          :  245 (1844 expanded)
%              Number of equality atoms :   22 (  62 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f215,plain,(
    $false ),
    inference(subsumption_resolution,[],[f214,f38])).

fof(f38,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f214,plain,(
    ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f210,f206])).

fof(f206,plain,(
    ~ m1_subset_1(k3_yellow_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f205,f29])).

fof(f29,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f205,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(k3_yellow_0(sK0),sK1) ),
    inference(resolution,[],[f186,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f186,plain,(
    ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f153,f64])).

fof(f64,plain,(
    ! [X1] : ~ v1_subset_1(X1,X1) ),
    inference(subsumption_resolution,[],[f57,f62])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f49,f61])).

fof(f61,plain,(
    ! [X0] : sK4(X0) = X0 ),
    inference(subsumption_resolution,[],[f60,f50])).

fof(f50,plain,(
    ! [X0] : ~ v1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f60,plain,(
    ! [X0] :
      ( sK4(X0) = X0
      | v1_subset_1(sK4(X0),X0) ) ),
    inference(resolution,[],[f55,f49])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f153,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(backward_demodulation,[],[f27,f152])).

fof(f152,plain,(
    sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f151,f38])).

fof(f151,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f150,f39])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f150,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f149,f67])).

fof(f67,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f53,f32])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f149,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f148,f66])).

fof(f66,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f59,f28])).

fof(f28,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f55,f32])).

fof(f148,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f141,f87])).

fof(f87,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f86,f38])).

fof(f86,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,k3_yellow_0(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f85,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f85,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,k3_yellow_0(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f84,f36])).

fof(f36,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,k3_yellow_0(sK0),X0) ) ),
    inference(resolution,[],[f48,f37])).

fof(f37,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,k3_yellow_0(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f141,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,X0,sK5(u1_struct_0(sK0),sK1))
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK1 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f136,f69])).

fof(f69,plain,
    ( ~ r2_hidden(sK5(u1_struct_0(sK0),sK1),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f54,f32])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK5(X0,X1),X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1)
      | ~ r1_orders_2(sK0,X0,sK5(u1_struct_0(sK0),sK1))
      | r2_hidden(sK5(u1_struct_0(sK0),sK1),sK1)
      | sK1 = u1_struct_0(sK0) ) ),
    inference(resolution,[],[f135,f67])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1)
      | ~ r1_orders_2(sK0,X0,X1)
      | r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f133,f31])).

fof(f31,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1)
      | ~ r1_orders_2(sK0,X0,X1)
      | r2_hidden(X1,sK1)
      | ~ v13_waybel_0(sK1,sK0) ) ),
    inference(resolution,[],[f132,f32])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | ~ r1_orders_2(sK0,X1,X2)
      | r2_hidden(X2,X0)
      | ~ v13_waybel_0(X0,sK0) ) ),
    inference(resolution,[],[f44,f38])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f27,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f210,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ l1_orders_2(sK0) ),
    inference(superposition,[],[f39,f152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:43:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (28195)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.45  % (28195)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f215,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(subsumption_resolution,[],[f214,f38])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    l1_orders_2(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,negated_conjecture,(
% 0.22/0.45    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.22/0.45    inference(negated_conjecture,[],[f10])).
% 0.22/0.45  fof(f10,conjecture,(
% 0.22/0.45    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.22/0.45  fof(f214,plain,(
% 0.22/0.45    ~l1_orders_2(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f210,f206])).
% 0.22/0.45  fof(f206,plain,(
% 0.22/0.45    ~m1_subset_1(k3_yellow_0(sK0),sK1)),
% 0.22/0.45    inference(subsumption_resolution,[],[f205,f29])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ~v1_xboole_0(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f205,plain,(
% 0.22/0.45    v1_xboole_0(sK1) | ~m1_subset_1(k3_yellow_0(sK0),sK1)),
% 0.22/0.45    inference(resolution,[],[f186,f52])).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.45    inference(flattening,[],[f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.45  fof(f186,plain,(
% 0.22/0.45    ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.22/0.45    inference(subsumption_resolution,[],[f153,f64])).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    ( ! [X1] : (~v1_subset_1(X1,X1)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f57,f62])).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.45    inference(backward_demodulation,[],[f49,f61])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    ( ! [X0] : (sK4(X0) = X0) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f60,f50])).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_subset_1(sK4(X0),X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    ( ! [X0] : (sK4(X0) = X0 | v1_subset_1(sK4(X0),X0)) )),
% 0.22/0.45    inference(resolution,[],[f55,f49])).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f26])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,axiom,(
% 0.22/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    ( ! [X0] : (m1_subset_1(sK4(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f2])).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.22/0.45    inference(equality_resolution,[],[f56])).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f26])).
% 0.22/0.45  fof(f153,plain,(
% 0.22/0.45    v1_subset_1(sK1,sK1) | ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.22/0.45    inference(backward_demodulation,[],[f27,f152])).
% 0.22/0.45  fof(f152,plain,(
% 0.22/0.45    sK1 = u1_struct_0(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f151,f38])).
% 0.22/0.45  fof(f151,plain,(
% 0.22/0.45    sK1 = u1_struct_0(sK0) | ~l1_orders_2(sK0)),
% 0.22/0.45    inference(resolution,[],[f150,f39])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 0.22/0.45  fof(f150,plain,(
% 0.22/0.45    ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f149,f67])).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    m1_subset_1(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 0.22/0.45    inference(resolution,[],[f53,f32])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK5(X0,X1),X0) | X0 = X1) )),
% 0.22/0.45    inference(cnf_transformation,[],[f25])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.45    inference(flattening,[],[f24])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).
% 0.22/0.45  fof(f149,plain,(
% 0.22/0.45    ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.22/0.45    inference(subsumption_resolution,[],[f148,f66])).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    r2_hidden(k3_yellow_0(sK0),sK1) | sK1 = u1_struct_0(sK0)),
% 0.22/0.45    inference(resolution,[],[f59,f28])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ~v1_subset_1(sK1,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    v1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 0.22/0.45    inference(resolution,[],[f55,f32])).
% 0.22/0.45  fof(f148,plain,(
% 0.22/0.45    ~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK5(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.22/0.45    inference(resolution,[],[f141,f87])).
% 0.22/0.45  fof(f87,plain,(
% 0.22/0.45    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f86,f38])).
% 0.22/0.45  fof(f86,plain,(
% 0.22/0.45    ( ! [X0] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k3_yellow_0(sK0),X0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f85,f33])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ~v2_struct_0(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f85,plain,(
% 0.22/0.45    ( ! [X0] : (v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k3_yellow_0(sK0),X0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f84,f36])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    v5_orders_2(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f84,plain,(
% 0.22/0.45    ( ! [X0] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k3_yellow_0(sK0),X0)) )),
% 0.22/0.45    inference(resolution,[],[f48,f37])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    v1_yellow_0(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,k3_yellow_0(X0),X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).
% 0.22/0.45  fof(f141,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_orders_2(sK0,X0,sK5(u1_struct_0(sK0),sK1)) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f136,f69])).
% 0.22/0.45  fof(f69,plain,(
% 0.22/0.45    ~r2_hidden(sK5(u1_struct_0(sK0),sK1),sK1) | sK1 = u1_struct_0(sK0)),
% 0.22/0.45    inference(resolution,[],[f54,f32])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(sK5(X0,X1),X1) | X0 = X1) )),
% 0.22/0.45    inference(cnf_transformation,[],[f25])).
% 0.22/0.45  fof(f136,plain,(
% 0.22/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~r1_orders_2(sK0,X0,sK5(u1_struct_0(sK0),sK1)) | r2_hidden(sK5(u1_struct_0(sK0),sK1),sK1) | sK1 = u1_struct_0(sK0)) )),
% 0.22/0.45    inference(resolution,[],[f135,f67])).
% 0.22/0.46  fof(f135,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1)) )),
% 0.22/0.46    inference(subsumption_resolution,[],[f133,f31])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    v13_waybel_0(sK1,sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f13])).
% 0.22/0.46  fof(f133,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1) | ~v13_waybel_0(sK1,sK0)) )),
% 0.22/0.46    inference(resolution,[],[f132,f32])).
% 0.22/0.46  fof(f132,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | ~r1_orders_2(sK0,X1,X2) | r2_hidden(X2,X0) | ~v13_waybel_0(X0,sK0)) )),
% 0.22/0.46    inference(resolution,[],[f44,f38])).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~r1_orders_2(X0,X2,X3) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.46    inference(flattening,[],[f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,axiom,(
% 0.22/0.46    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    v1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.22/0.46    inference(cnf_transformation,[],[f13])).
% 0.22/0.46  fof(f210,plain,(
% 0.22/0.46    m1_subset_1(k3_yellow_0(sK0),sK1) | ~l1_orders_2(sK0)),
% 0.22/0.46    inference(superposition,[],[f39,f152])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (28195)------------------------------
% 0.22/0.46  % (28195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (28195)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (28195)Memory used [KB]: 1791
% 0.22/0.46  % (28195)Time elapsed: 0.010 s
% 0.22/0.46  % (28195)------------------------------
% 0.22/0.46  % (28195)------------------------------
% 0.22/0.46  % (28175)Success in time 0.092 s
%------------------------------------------------------------------------------
