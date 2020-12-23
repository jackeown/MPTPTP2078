%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  114 (1217 expanded)
%              Number of leaves         :   12 ( 195 expanded)
%              Depth                    :   33
%              Number of atoms          :  403 (9243 expanded)
%              Number of equality atoms :   46 ( 223 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f294,plain,(
    $false ),
    inference(subsumption_resolution,[],[f293,f262])).

fof(f262,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f43,f259])).

fof(f259,plain,(
    sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f258,f43])).

fof(f258,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f256])).

fof(f256,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f250,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f250,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f249])).

fof(f249,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1)
    | sK1 = u1_struct_0(sK0)
    | sK1 = u1_struct_0(sK0) ),
    inference(superposition,[],[f239,f143])).

fof(f143,plain,
    ( sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f142,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(pure_predicate_removal,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f142,plain,
    ( sK1 = u1_struct_0(sK0)
    | v2_struct_0(sK0)
    | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f141,f49])).

fof(f49,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f141,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f140,f47])).

fof(f47,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f140,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f139,f46])).

fof(f46,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f139,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f132,f45])).

fof(f45,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f132,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f95,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f95,plain,
    ( m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f43,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f239,plain,(
    ! [X0] :
      ( r2_hidden(k1_yellow_0(sK0,X0),sK1)
      | sK1 = u1_struct_0(sK0) ) ),
    inference(resolution,[],[f238,f112])).

fof(f112,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f94,f40])).

fof(f40,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f94,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f43,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f238,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | r2_hidden(k1_yellow_0(sK0,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f237,f43])).

fof(f237,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | r2_hidden(k1_yellow_0(sK0,X0),sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f171,f42])).

fof(f42,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X0,sK0)
      | ~ r2_hidden(k3_yellow_0(sK0),X0)
      | r2_hidden(k1_yellow_0(sK0,X1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f170,f49])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k3_yellow_0(sK0),X0)
      | ~ l1_orders_2(sK0)
      | r2_hidden(k1_yellow_0(sK0,X1),X0)
      | ~ v13_waybel_0(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f169,f82])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f49,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_yellow_0(sK0,X1),u1_struct_0(sK0))
      | ~ r2_hidden(k3_yellow_0(sK0),X0)
      | ~ l1_orders_2(sK0)
      | r2_hidden(k1_yellow_0(sK0,X1),X0)
      | ~ v13_waybel_0(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f166,f83])).

fof(f83,plain,(
    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f49,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(k1_yellow_0(sK0,X1),u1_struct_0(sK0))
      | ~ r2_hidden(k3_yellow_0(sK0),X0)
      | ~ l1_orders_2(sK0)
      | r2_hidden(k1_yellow_0(sK0,X1),X0)
      | ~ v13_waybel_0(X0,sK0) ) ),
    inference(resolution,[],[f163,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ l1_orders_2(X0)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f163,plain,(
    ! [X0] : r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0)) ),
    inference(forward_demodulation,[],[f160,f126])).

fof(f126,plain,(
    ! [X1] : k1_yellow_0(sK0,X1) = k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X1))) ),
    inference(subsumption_resolution,[],[f125,f44])).

fof(f125,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | k1_yellow_0(sK0,X1) = k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X1))) ) ),
    inference(subsumption_resolution,[],[f124,f49])).

fof(f124,plain,(
    ! [X1] :
      ( ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_yellow_0(sK0,X1) = k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X1))) ) ),
    inference(subsumption_resolution,[],[f123,f47])).

fof(f123,plain,(
    ! [X1] :
      ( ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_yellow_0(sK0,X1) = k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X1))) ) ),
    inference(subsumption_resolution,[],[f122,f46])).

fof(f122,plain,(
    ! [X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_yellow_0(sK0,X1) = k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X1))) ) ),
    inference(subsumption_resolution,[],[f114,f45])).

fof(f114,plain,(
    ! [X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_yellow_0(sK0,X1) = k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X1))) ) ),
    inference(resolution,[],[f82,f69])).

fof(f160,plain,(
    ! [X0] : r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0)))) ),
    inference(resolution,[],[f88,f121])).

fof(f121,plain,(
    ! [X0] : r1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0))) ),
    inference(subsumption_resolution,[],[f120,f44])).

fof(f120,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | r1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f119,f49])).

fof(f119,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | r1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f118,f47])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | r1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f117,f46])).

fof(f117,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | r1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f113,f45])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | r1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0))) ) ),
    inference(resolution,[],[f82,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK0,X0)
      | r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f87,f84])).

fof(f84,plain,(
    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f49,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f87,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(sK0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f86,f49])).

fof(f86,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | ~ r1_yellow_0(sK0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f85,f74])).

fof(f74,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f85,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ l1_orders_2(sK0)
      | ~ r1_yellow_0(sK0,X0)
      | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0)) ) ),
    inference(resolution,[],[f81,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X2)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

fof(f81,plain,(
    r1_yellow_0(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f80,f49])).

fof(f80,plain,
    ( ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f79,f44])).

fof(f79,plain,
    ( v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f78,f47])).

fof(f78,plain,
    ( ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | r1_yellow_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f48,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f48,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f293,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f289,f75])).

fof(f75,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f289,plain,(
    v1_subset_1(sK1,sK1) ),
    inference(resolution,[],[f276,f260])).

fof(f260,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,sK1) ),
    inference(backward_demodulation,[],[f39,f259])).

fof(f39,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f276,plain,(
    r2_hidden(k3_yellow_0(sK0),sK1) ),
    inference(forward_demodulation,[],[f275,f259])).

fof(f275,plain,(
    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f268,f41])).

fof(f41,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f268,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f101,f259])).

fof(f101,plain,
    ( r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f83,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (1211)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % (1195)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (1198)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (1202)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (1198)Refutation not found, incomplete strategy% (1198)------------------------------
% 0.20/0.50  % (1198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1198)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1198)Memory used [KB]: 1663
% 0.20/0.50  % (1198)Time elapsed: 0.084 s
% 0.20/0.50  % (1198)------------------------------
% 0.20/0.50  % (1198)------------------------------
% 0.20/0.50  % (1212)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (1209)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (1204)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (1192)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (1196)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (1194)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (1199)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (1205)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (1203)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (1191)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (1197)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.53  % (1208)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.53  % (1200)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.53  % (1197)Refutation not found, incomplete strategy% (1197)------------------------------
% 0.20/0.53  % (1197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (1197)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (1197)Memory used [KB]: 10618
% 0.20/0.53  % (1197)Time elapsed: 0.118 s
% 0.20/0.53  % (1197)------------------------------
% 0.20/0.53  % (1197)------------------------------
% 0.20/0.53  % (1196)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f294,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f293,f262])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.53    inference(backward_demodulation,[],[f43,f259])).
% 0.20/0.53  fof(f259,plain,(
% 0.20/0.53    sK1 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f258,f43])).
% 0.20/0.53  fof(f258,plain,(
% 0.20/0.53    sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f256])).
% 0.20/0.53  fof(f256,plain,(
% 0.20/0.53    sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f250,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(flattening,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).
% 0.20/0.53  fof(f250,plain,(
% 0.20/0.53    r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1) | sK1 = u1_struct_0(sK0)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f249])).
% 0.20/0.53  fof(f249,plain,(
% 0.20/0.53    r2_hidden(sK2(u1_struct_0(sK0),sK1),sK1) | sK1 = u1_struct_0(sK0) | sK1 = u1_struct_0(sK0)),
% 0.20/0.53    inference(superposition,[],[f239,f143])).
% 0.20/0.53  fof(f143,plain,(
% 0.20/0.53    sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1))) | sK1 = u1_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f142,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ~v2_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.53    inference(pure_predicate_removal,[],[f16])).
% 0.20/0.53  fof(f16,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.53    inference(negated_conjecture,[],[f15])).
% 0.20/0.53  fof(f15,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    sK1 = u1_struct_0(sK0) | v2_struct_0(sK0) | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f141,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    l1_orders_2(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    sK1 = u1_struct_0(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f140,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    v5_orders_2(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    sK1 = u1_struct_0(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f139,f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    v4_orders_2(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    sK1 = u1_struct_0(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f132,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    v3_orders_2(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    sK1 = u1_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | sK2(u1_struct_0(sK0),sK1) = k1_yellow_0(sK0,k5_waybel_0(sK0,sK2(u1_struct_0(sK0),sK1)))),
% 0.20/0.53    inference(resolution,[],[f95,f69])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1 & r1_yellow_0(X0,k5_waybel_0(X0,X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    m1_subset_1(sK2(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f43,f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK2(X0,X1),X0) | X0 = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f239,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(k1_yellow_0(sK0,X0),sK1) | sK1 = u1_struct_0(sK0)) )),
% 0.20/0.53    inference(resolution,[],[f238,f112])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    r2_hidden(k3_yellow_0(sK0),sK1) | sK1 = u1_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f94,f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ~v1_subset_1(sK1,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    v1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f43,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.53  fof(f238,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(k1_yellow_0(sK0,X0),sK1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f237,f43])).
% 0.20/0.53  fof(f237,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(k1_yellow_0(sK0,X0),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.53    inference(resolution,[],[f171,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    v13_waybel_0(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v13_waybel_0(X0,sK0) | ~r2_hidden(k3_yellow_0(sK0),X0) | r2_hidden(k1_yellow_0(sK0,X1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f170,f49])).
% 0.20/0.53  fof(f170,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(k3_yellow_0(sK0),X0) | ~l1_orders_2(sK0) | r2_hidden(k1_yellow_0(sK0,X1),X0) | ~v13_waybel_0(X0,sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f169,f82])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))) )),
% 0.20/0.53    inference(resolution,[],[f49,f59])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_orders_2(X0) | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_yellow_0(sK0,X1),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),X0) | ~l1_orders_2(sK0) | r2_hidden(k1_yellow_0(sK0,X1),X0) | ~v13_waybel_0(X0,sK0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f166,f83])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.20/0.53    inference(resolution,[],[f49,f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 0.20/0.53  fof(f166,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k1_yellow_0(sK0,X1),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),X0) | ~l1_orders_2(sK0) | r2_hidden(k1_yellow_0(sK0,X1),X0) | ~v13_waybel_0(X0,sK0)) )),
% 0.20/0.53    inference(resolution,[],[f163,f64])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~l1_orders_2(X0) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(flattening,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0))) )),
% 0.20/0.53    inference(forward_demodulation,[],[f160,f126])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    ( ! [X1] : (k1_yellow_0(sK0,X1) = k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X1)))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f125,f44])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    ( ! [X1] : (v2_struct_0(sK0) | k1_yellow_0(sK0,X1) = k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X1)))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f124,f49])).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    ( ! [X1] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | k1_yellow_0(sK0,X1) = k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X1)))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f123,f47])).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    ( ! [X1] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | k1_yellow_0(sK0,X1) = k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X1)))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f122,f46])).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    ( ! [X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | k1_yellow_0(sK0,X1) = k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X1)))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f114,f45])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    ( ! [X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | k1_yellow_0(sK0,X1) = k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X1)))) )),
% 0.20/0.53    inference(resolution,[],[f82,f69])).
% 0.20/0.53  fof(f160,plain,(
% 0.20/0.53    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0))))) )),
% 0.20/0.53    inference(resolution,[],[f88,f121])).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    ( ! [X0] : (r1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0)))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f120,f44])).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    ( ! [X0] : (v2_struct_0(sK0) | r1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0)))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f119,f49])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | r1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0)))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f118,f47])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    ( ! [X0] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | r1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0)))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f117,f46])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | r1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0)))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f113,f45])).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | r1_yellow_0(sK0,k5_waybel_0(sK0,k1_yellow_0(sK0,X0)))) )),
% 0.20/0.53    inference(resolution,[],[f82,f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_yellow_0(X0,k5_waybel_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k3_yellow_0(sK0),k1_yellow_0(sK0,X0))) )),
% 0.20/0.53    inference(forward_demodulation,[],[f87,f84])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f49,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f86,f49])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_orders_2(sK0) | ~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f85,f74])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~l1_orders_2(sK0) | ~r1_yellow_0(sK0,X0) | r1_orders_2(sK0,k1_yellow_0(sK0,k1_xboole_0),k1_yellow_0(sK0,X0))) )),
% 0.20/0.53    inference(resolution,[],[f81,f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0) | ~r1_yellow_0(X0,X2) | r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | ~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(flattening,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0] : (! [X1,X2] : (r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) | (~r1_yellow_0(X0,X2) | ~r1_yellow_0(X0,X1) | ~r1_tarski(X1,X2))) | ~l1_orders_2(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : ((r1_yellow_0(X0,X2) & r1_yellow_0(X0,X1) & r1_tarski(X1,X2)) => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    r1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f80,f49])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f79,f44])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    v2_struct_0(sK0) | ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f78,f47])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~l1_orders_2(sK0) | r1_yellow_0(sK0,k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f48,f67])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | r1_yellow_0(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 0.20/0.53    inference(pure_predicate_removal,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    v1_yellow_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f293,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.53    inference(resolution,[],[f289,f75])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f289,plain,(
% 0.20/0.53    v1_subset_1(sK1,sK1)),
% 0.20/0.53    inference(resolution,[],[f276,f260])).
% 0.20/0.53  fof(f260,plain,(
% 0.20/0.53    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,sK1)),
% 0.20/0.53    inference(backward_demodulation,[],[f39,f259])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f276,plain,(
% 0.20/0.53    r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.20/0.53    inference(forward_demodulation,[],[f275,f259])).
% 0.20/0.53  fof(f275,plain,(
% 0.20/0.53    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.20/0.53    inference(subsumption_resolution,[],[f268,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ~v1_xboole_0(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f268,plain,(
% 0.20/0.53    v1_xboole_0(sK1) | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.20/0.53    inference(backward_demodulation,[],[f101,f259])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.53    inference(resolution,[],[f83,f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (1196)------------------------------
% 0.20/0.53  % (1196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (1196)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (1196)Memory used [KB]: 6268
% 0.20/0.53  % (1196)Time elapsed: 0.072 s
% 0.20/0.53  % (1196)------------------------------
% 0.20/0.53  % (1196)------------------------------
% 0.20/0.53  % (1190)Success in time 0.173 s
%------------------------------------------------------------------------------
