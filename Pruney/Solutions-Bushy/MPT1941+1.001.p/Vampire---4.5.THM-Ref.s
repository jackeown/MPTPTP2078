%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1941+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:56 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   73 (1016 expanded)
%              Number of leaves         :   10 ( 237 expanded)
%              Depth                    :   16
%              Number of atoms          :  241 (4571 expanded)
%              Number of equality atoms :   34 ( 410 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(subsumption_resolution,[],[f118,f116])).

fof(f116,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(forward_demodulation,[],[f109,f111])).

fof(f111,plain,(
    sK2 = sK3(sK2,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f30,f31,f32,f29,f104,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | sK3(X0,X1,X2) = X0
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      <=> ? [X3] :
            ( v3_pre_topc(X3,X1)
            & r2_hidden(X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      <=> ? [X3] :
            ( v3_pre_topc(X3,X1)
            & r2_hidden(X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_yellow_6(X1,X2))
      <=> ? [X3] :
            ( v3_pre_topc(X3,X1)
            & r2_hidden(X2,X3)
            & X0 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow_6)).

fof(f104,plain,(
    r2_hidden(sK2,a_2_0_yellow_6(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,
    ( r2_hidden(sK2,a_2_0_yellow_6(sK0,sK1))
    | r2_hidden(sK2,a_2_0_yellow_6(sK0,sK1))
    | r2_hidden(sK2,a_2_0_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f99,f90])).

fof(f90,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK2,a_2_0_yellow_6(sK0,sK1)) ),
    inference(backward_demodulation,[],[f26,f87])).

fof(f87,plain,(
    u1_struct_0(k9_yellow_6(sK0,sK1)) = a_2_0_yellow_6(sK0,sK1) ),
    inference(superposition,[],[f68,f79])).

fof(f79,plain,(
    k9_yellow_6(sK0,sK1) = k7_lattice3(g1_orders_2(a_2_0_yellow_6(sK0,sK1),k1_yellow_1(a_2_0_yellow_6(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f32,f31,f30,f29,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k9_yellow_6(X0,X1) = k7_lattice3(g1_orders_2(a_2_0_yellow_6(X0,X1),k1_yellow_1(a_2_0_yellow_6(X0,X1)))) ) ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f43,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k9_yellow_6(X0,X1) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_yellow_6)).

fof(f68,plain,(
    ! [X0] : u1_struct_0(k7_lattice3(g1_orders_2(X0,k1_yellow_1(X0)))) = X0 ),
    inference(backward_demodulation,[],[f56,f62])).

fof(f62,plain,(
    ! [X0] : u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0 ),
    inference(unit_resulting_resolution,[],[f51,f57,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f57,plain,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) ),
    inference(unit_resulting_resolution,[],[f54,f53,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f53,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f45,f43])).

fof(f45,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f54,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f44,f43])).

fof(f44,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k1_yellow_1(X0),X0)
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_1)).

fof(f56,plain,(
    ! [X0] : u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = u1_struct_0(k7_lattice3(g1_orders_2(X0,k1_yellow_1(X0)))) ),
    inference(unit_resulting_resolution,[],[f53,f42])).

fof(f42,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow_6)).

fof(f26,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <~> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <~> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                <=> ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

fof(f99,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | r2_hidden(sK2,a_2_0_yellow_6(sK0,X3))
      | r2_hidden(sK2,a_2_0_yellow_6(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f95,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f95,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,a_2_0_yellow_6(sK0,X3))
      | r2_hidden(sK2,a_2_0_yellow_6(sK0,sK1)) ) ),
    inference(resolution,[],[f86,f91])).

fof(f91,plain,
    ( v3_pre_topc(sK2,sK0)
    | r2_hidden(sK2,a_2_0_yellow_6(sK0,sK1)) ),
    inference(backward_demodulation,[],[f27,f87])).

fof(f27,plain,
    ( v3_pre_topc(sK2,sK0)
    | r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,sK0)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,a_2_0_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f85,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ v3_pre_topc(X1,sK0)
      | r2_hidden(X1,a_2_0_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f84,f30])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ v3_pre_topc(X1,sK0)
      | r2_hidden(X1,a_2_0_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f83,f31])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ v3_pre_topc(X1,sK0)
      | r2_hidden(X1,a_2_0_yellow_6(sK0,X0)) ) ),
    inference(resolution,[],[f55,f32])).

fof(f55,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X2,X3)
      | ~ v3_pre_topc(X3,X1)
      | r2_hidden(X3,a_2_0_yellow_6(X1,X2)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X0 != X3
      | ~ r2_hidden(X2,X3)
      | ~ v3_pre_topc(X3,X1)
      | r2_hidden(X0,a_2_0_yellow_6(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f109,plain,(
    v3_pre_topc(sK3(sK2,sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f31,f30,f32,f29,f104,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK3(X0,X1,X2),X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f118,plain,(
    ~ v3_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f112,f115])).

fof(f115,plain,(
    r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f110,f111])).

fof(f110,plain,(
    r2_hidden(sK1,sK3(sK2,sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f31,f30,f32,f29,f104,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK3(X0,X1,X2))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_0_yellow_6(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f112,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ v3_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f104,f89])).

fof(f89,plain,
    ( ~ r2_hidden(sK2,a_2_0_yellow_6(sK0,sK1))
    | ~ r2_hidden(sK1,sK2)
    | ~ v3_pre_topc(sK2,sK0) ),
    inference(backward_demodulation,[],[f25,f87])).

fof(f25,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
