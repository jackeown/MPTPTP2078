%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1670+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:18 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 527 expanded)
%              Number of leaves         :   17 ( 125 expanded)
%              Depth                    :   13
%              Number of atoms          :  363 (2095 expanded)
%              Number of equality atoms :   38 (  66 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f177,f263])).

fof(f263,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f105,f242,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f242,plain,
    ( r2_hidden(sK2(sK1,k11_waybel_0(sK0,sK1)),k11_waybel_0(sK0,sK1))
    | spl5_2 ),
    inference(forward_demodulation,[],[f241,f208])).

fof(f208,plain,
    ( sK2(sK1,k11_waybel_0(sK0,sK1)) = k1_yellow_0(sK0,k1_tarski(sK2(sK1,k11_waybel_0(sK0,sK1))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f200,f202])).

fof(f202,plain,
    ( k1_tarski(sK2(sK1,k11_waybel_0(sK0,sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1,k11_waybel_0(sK0,sK1)))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f183,f185,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f185,plain,
    ( m1_subset_1(sK2(sK1,k11_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f43,f178,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f178,plain,
    ( r2_hidden(sK2(sK1,k11_waybel_0(sK0,sK1)),sK1)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f105,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k12_waybel_0(X0,X1))
            | ~ r1_tarski(X1,k11_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k12_waybel_0(X0,X1))
            | ~ r1_tarski(X1,k11_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r1_tarski(X1,k12_waybel_0(X0,X1))
              & r1_tarski(X1,k11_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r1_tarski(X1,k12_waybel_0(X0,X1))
            & r1_tarski(X1,k11_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_waybel_0)).

fof(f183,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f43,f178,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f200,plain,
    ( sK2(sK1,k11_waybel_0(sK0,sK1)) = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK1,k11_waybel_0(sK0,sK1))))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f45,f46,f47,f44,f185,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_0)).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f241,plain,
    ( r2_hidden(k1_yellow_0(sK0,k1_tarski(sK2(sK1,k11_waybel_0(sK0,sK1)))),k11_waybel_0(sK0,sK1))
    | spl5_2 ),
    inference(forward_demodulation,[],[f234,f94])).

fof(f94,plain,(
    k11_waybel_0(sK0,sK1) = a_2_2_waybel_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f44,f47,f43,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k11_waybel_0(X0,X1) = a_2_2_waybel_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k11_waybel_0(X0,X1) = a_2_2_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k11_waybel_0(X0,X1) = a_2_2_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k11_waybel_0(X0,X1) = a_2_2_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d27_waybel_0)).

fof(f234,plain,
    ( r2_hidden(k1_yellow_0(sK0,k1_tarski(sK2(sK1,k11_waybel_0(sK0,sK1)))),a_2_2_waybel_0(sK0,sK1))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f44,f47,f43,f210,f70,f196,f77])).

fof(f77,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v1_finset_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ r1_yellow_0(X1,X3)
      | r2_hidden(k1_yellow_0(X1,X3),a_2_2_waybel_0(X1,X2)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v1_finset_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | k1_yellow_0(X1,X3) != X0
      | ~ r1_yellow_0(X1,X3)
      | r2_hidden(X0,a_2_2_waybel_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_waybel_0(X1,X2))
      <=> ? [X3] :
            ( r1_yellow_0(X1,X3)
            & k1_yellow_0(X1,X3) = X0
            & m1_subset_1(X3,k1_zfmisc_1(X2))
            & v1_finset_1(X3) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_waybel_0(X1,X2))
      <=> ? [X3] :
            ( r1_yellow_0(X1,X3)
            & k1_yellow_0(X1,X3) = X0
            & m1_subset_1(X3,k1_zfmisc_1(X2))
            & v1_finset_1(X3) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_2_waybel_0(X1,X2))
      <=> ? [X3] :
            ( r1_yellow_0(X1,X3)
            & k1_yellow_0(X1,X3) = X0
            & m1_subset_1(X3,k1_zfmisc_1(X2))
            & v1_finset_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_waybel_0)).

fof(f196,plain,
    ( m1_subset_1(k1_tarski(sK2(sK1,k11_waybel_0(sK0,sK1))),k1_zfmisc_1(sK1))
    | spl5_2 ),
    inference(backward_demodulation,[],[f193,f192])).

fof(f192,plain,
    ( k1_tarski(sK2(sK1,k11_waybel_0(sK0,sK1))) = k6_domain_1(sK1,sK2(sK1,k11_waybel_0(sK0,sK1)))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f182,f184,f63])).

fof(f184,plain,
    ( m1_subset_1(sK2(sK1,k11_waybel_0(sK0,sK1)),sK1)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f178,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f182,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f178,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f193,plain,
    ( m1_subset_1(k6_domain_1(sK1,sK2(sK1,k11_waybel_0(sK0,sK1))),k1_zfmisc_1(sK1))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f182,f184,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f70,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

fof(f210,plain,
    ( r1_yellow_0(sK0,k1_tarski(sK2(sK1,k11_waybel_0(sK0,sK1))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f198,f202])).

fof(f198,plain,
    ( r1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK1,k11_waybel_0(sK0,sK1))))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f45,f46,f47,f44,f185,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
            & r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
            & r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
            & r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_0)).

fof(f105,plain,
    ( ~ r1_tarski(sK1,k11_waybel_0(sK0,sK1))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_2
  <=> r1_tarski(sK1,k11_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f177,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f101,f160,f53])).

fof(f160,plain,
    ( r2_hidden(sK2(sK1,k12_waybel_0(sK0,sK1)),k12_waybel_0(sK0,sK1))
    | spl5_1 ),
    inference(forward_demodulation,[],[f159,f137])).

fof(f137,plain,
    ( sK2(sK1,k12_waybel_0(sK0,sK1)) = k2_yellow_0(sK0,k1_tarski(sK2(sK1,k12_waybel_0(sK0,sK1))))
    | spl5_1 ),
    inference(forward_demodulation,[],[f131,f132])).

fof(f132,plain,
    ( k1_tarski(sK2(sK1,k12_waybel_0(sK0,sK1))) = k6_domain_1(u1_struct_0(sK0),sK2(sK1,k12_waybel_0(sK0,sK1)))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f112,f114,f63])).

fof(f114,plain,
    ( m1_subset_1(sK2(sK1,k12_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f43,f107,f55])).

fof(f107,plain,
    ( r2_hidden(sK2(sK1,k12_waybel_0(sK0,sK1)),sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f101,f52])).

fof(f112,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f43,f107,f57])).

fof(f131,plain,
    ( sK2(sK1,k12_waybel_0(sK0,sK1)) = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK1,k12_waybel_0(sK0,sK1))))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f45,f46,f47,f44,f114,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f159,plain,
    ( r2_hidden(k2_yellow_0(sK0,k1_tarski(sK2(sK1,k12_waybel_0(sK0,sK1)))),k12_waybel_0(sK0,sK1))
    | spl5_1 ),
    inference(forward_demodulation,[],[f155,f93])).

fof(f93,plain,(
    k12_waybel_0(sK0,sK1) = a_2_3_waybel_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f44,f47,f43,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k12_waybel_0(X0,X1) = a_2_3_waybel_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k12_waybel_0(X0,X1) = a_2_3_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k12_waybel_0(X0,X1) = a_2_3_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k12_waybel_0(X0,X1) = a_2_3_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d28_waybel_0)).

fof(f155,plain,
    ( r2_hidden(k2_yellow_0(sK0,k1_tarski(sK2(sK1,k12_waybel_0(sK0,sK1)))),a_2_3_waybel_0(sK0,sK1))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f47,f44,f43,f139,f70,f126,f76])).

fof(f76,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_finset_1(X3)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_struct_0(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ r2_yellow_0(X1,X3)
      | r2_hidden(k2_yellow_0(X1,X3),a_2_3_waybel_0(X1,X2)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v1_finset_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | k2_yellow_0(X1,X3) != X0
      | ~ r2_yellow_0(X1,X3)
      | r2_hidden(X0,a_2_3_waybel_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_3_waybel_0(X1,X2))
      <=> ? [X3] :
            ( r2_yellow_0(X1,X3)
            & k2_yellow_0(X1,X3) = X0
            & m1_subset_1(X3,k1_zfmisc_1(X2))
            & v1_finset_1(X3) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_3_waybel_0(X1,X2))
      <=> ? [X3] :
            ( r2_yellow_0(X1,X3)
            & k2_yellow_0(X1,X3) = X0
            & m1_subset_1(X3,k1_zfmisc_1(X2))
            & v1_finset_1(X3) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_3_waybel_0(X1,X2))
      <=> ? [X3] :
            ( r2_yellow_0(X1,X3)
            & k2_yellow_0(X1,X3) = X0
            & m1_subset_1(X3,k1_zfmisc_1(X2))
            & v1_finset_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_3_waybel_0)).

fof(f126,plain,
    ( m1_subset_1(k1_tarski(sK2(sK1,k12_waybel_0(sK0,sK1))),k1_zfmisc_1(sK1))
    | spl5_1 ),
    inference(backward_demodulation,[],[f123,f122])).

fof(f122,plain,
    ( k1_tarski(sK2(sK1,k12_waybel_0(sK0,sK1))) = k6_domain_1(sK1,sK2(sK1,k12_waybel_0(sK0,sK1)))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f111,f113,f63])).

fof(f113,plain,
    ( m1_subset_1(sK2(sK1,k12_waybel_0(sK0,sK1)),sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f107,f56])).

fof(f111,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f107,f69])).

fof(f123,plain,
    ( m1_subset_1(k6_domain_1(sK1,sK2(sK1,k12_waybel_0(sK0,sK1))),k1_zfmisc_1(sK1))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f111,f113,f58])).

fof(f139,plain,
    ( r2_yellow_0(sK0,k1_tarski(sK2(sK1,k12_waybel_0(sK0,sK1))))
    | spl5_1 ),
    inference(forward_demodulation,[],[f129,f132])).

fof(f129,plain,
    ( r2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK1,k12_waybel_0(sK0,sK1))))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f45,f46,f47,f44,f114,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f101,plain,
    ( ~ r1_tarski(sK1,k12_waybel_0(sK0,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_1
  <=> r1_tarski(sK1,k12_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f106,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f42,f103,f99])).

fof(f42,plain,
    ( ~ r1_tarski(sK1,k11_waybel_0(sK0,sK1))
    | ~ r1_tarski(sK1,k12_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

%------------------------------------------------------------------------------
