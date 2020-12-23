%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:50 EST 2020

% Result     : Theorem 2.65s
% Output     : Refutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :  137 (4190 expanded)
%              Number of leaves         :   19 ( 905 expanded)
%              Depth                    :   20
%              Number of atoms          :  406 (19518 expanded)
%              Number of equality atoms :   61 (2260 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1916,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1915,f530])).

fof(f530,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2(sK1)) ),
    inference(unit_resulting_resolution,[],[f97,f106,f149,f136,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f136,plain,(
    r1_tarski(u1_struct_0(sK2(sK1)),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f94,f108,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f108,plain,(
    m1_pre_topc(sK2(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f94,f57,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_pre_topc(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_pre_topc)).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tex_2)).

fof(f94,plain,(
    l1_pre_topc(sK1) ),
    inference(unit_resulting_resolution,[],[f59,f61,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f149,plain,(
    ~ v1_xboole_0(u1_struct_0(sK2(sK1))) ),
    inference(unit_resulting_resolution,[],[f99,f138,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f138,plain,(
    l1_struct_0(sK2(sK1)) ),
    inference(unit_resulting_resolution,[],[f137,f63])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f137,plain,(
    l1_pre_topc(sK2(sK1)) ),
    inference(unit_resulting_resolution,[],[f94,f108,f65])).

fof(f99,plain,(
    ~ v2_struct_0(sK2(sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f94,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK2(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f106,plain,(
    v1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f58,f96,f83])).

fof(f83,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f96,plain,(
    l1_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f94,f63])).

fof(f58,plain,(
    v7_struct_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f97,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f96,f69])).

fof(f1915,plain,(
    u1_struct_0(sK1) != u1_struct_0(sK2(sK1)) ),
    inference(forward_demodulation,[],[f1914,f590])).

fof(f590,plain,(
    u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK0),sK4(u1_struct_0(sK1))) ),
    inference(backward_demodulation,[],[f222,f588])).

fof(f588,plain,(
    u1_struct_0(sK1) = k1_tarski(sK4(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f574,f530])).

fof(f574,plain,(
    u1_struct_0(sK2(sK1)) = k1_tarski(sK4(u1_struct_0(sK1))) ),
    inference(backward_demodulation,[],[f354,f567])).

fof(f567,plain,(
    sK2(sK1) = k1_tex_2(sK1,sK4(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f566,f362])).

fof(f362,plain,(
    sK2(sK1) = g1_pre_topc(k1_tarski(sK4(u1_struct_0(sK1))),u1_pre_topc(k1_tex_2(sK1,sK4(u1_struct_0(sK1))))) ),
    inference(forward_demodulation,[],[f361,f228])).

fof(f228,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2(sK1) ),
    inference(forward_demodulation,[],[f227,f147])).

fof(f147,plain,(
    sK2(sK1) = g1_pre_topc(u1_struct_0(sK2(sK1)),u1_pre_topc(sK2(sK1))) ),
    inference(unit_resulting_resolution,[],[f101,f137,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f101,plain,(
    v1_pre_topc(sK2(sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f94,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v1_pre_topc(sK2(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f227,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2(sK1)),u1_pre_topc(sK2(sK1))) ),
    inference(unit_resulting_resolution,[],[f94,f108,f210,f57,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v1_tex_2(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v1_tex_2(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v1_tex_2(X1,X0) )
         => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tex_2)).

fof(f210,plain,(
    ~ v1_tex_2(sK2(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f99,f108,f94,f57,f58,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).

fof(f361,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(k1_tarski(sK4(u1_struct_0(sK1))),u1_pre_topc(k1_tex_2(sK1,sK4(u1_struct_0(sK1))))) ),
    inference(forward_demodulation,[],[f360,f354])).

fof(f360,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK4(u1_struct_0(sK1)))),u1_pre_topc(k1_tex_2(sK1,sK4(u1_struct_0(sK1))))) ),
    inference(unit_resulting_resolution,[],[f57,f94,f204,f212,f75])).

fof(f212,plain,(
    ~ v1_tex_2(k1_tex_2(sK1,sK4(u1_struct_0(sK1))),sK1) ),
    inference(unit_resulting_resolution,[],[f57,f58,f94,f84,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_tex_2(k1_tex_2(X0,X1),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_tex_2(k1_tex_2(X0,X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_tex_2(k1_tex_2(X0,X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_tex_2(k1_tex_2(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tex_2)).

fof(f84,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f204,plain,(
    m1_pre_topc(k1_tex_2(sK1,sK4(u1_struct_0(sK1))),sK1) ),
    inference(unit_resulting_resolution,[],[f94,f57,f84,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f566,plain,(
    k1_tex_2(sK1,sK4(u1_struct_0(sK1))) = g1_pre_topc(k1_tarski(sK4(u1_struct_0(sK1))),u1_pre_topc(k1_tex_2(sK1,sK4(u1_struct_0(sK1))))) ),
    inference(forward_demodulation,[],[f548,f354])).

fof(f548,plain,(
    k1_tex_2(sK1,sK4(u1_struct_0(sK1))) = g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK4(u1_struct_0(sK1)))),u1_pre_topc(k1_tex_2(sK1,sK4(u1_struct_0(sK1))))) ),
    inference(unit_resulting_resolution,[],[f197,f348,f64])).

fof(f348,plain,(
    l1_pre_topc(k1_tex_2(sK1,sK4(u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f94,f204,f65])).

fof(f197,plain,(
    v1_pre_topc(k1_tex_2(sK1,sK4(u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f57,f94,f84,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f354,plain,(
    k1_tarski(sK4(u1_struct_0(sK1))) = u1_struct_0(k1_tex_2(sK1,sK4(u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f347,f172])).

fof(f172,plain,(
    k1_tarski(sK4(u1_struct_0(sK1))) = k6_domain_1(u1_struct_0(sK1),sK4(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f84,f97,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f347,plain,(
    k6_domain_1(u1_struct_0(sK1),sK4(u1_struct_0(sK1))) = u1_struct_0(k1_tex_2(sK1,sK4(u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f94,f57,f197,f185,f84,f204,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_pre_topc(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(k1_tex_2(X0,X1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

fof(f185,plain,(
    ~ v2_struct_0(k1_tex_2(sK1,sK4(u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f57,f94,f84,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f222,plain,(
    k1_tarski(sK4(u1_struct_0(sK1))) = k6_domain_1(u1_struct_0(sK0),sK4(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f95,f213,f85])).

fof(f213,plain,(
    m1_subset_1(sK4(u1_struct_0(sK1)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f60,f61,f59,f57,f84,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f95,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f60,f93,f69])).

fof(f93,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f61,f63])).

fof(f1914,plain,(
    u1_struct_0(sK2(sK1)) != k6_domain_1(u1_struct_0(sK0),sK4(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f61,f60,f99,f101,f231,f213,f1913,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0)
      | k1_tex_2(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1913,plain,(
    sK2(sK1) != k1_tex_2(sK0,sK4(u1_struct_0(sK1))) ),
    inference(superposition,[],[f598,f629])).

fof(f629,plain,(
    k1_tex_2(sK0,sK4(u1_struct_0(sK1))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k1_tex_2(sK0,sK4(u1_struct_0(sK1))))) ),
    inference(forward_demodulation,[],[f611,f593])).

fof(f593,plain,(
    u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK0,sK4(u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f441,f588])).

fof(f441,plain,(
    k1_tarski(sK4(u1_struct_0(sK1))) = u1_struct_0(k1_tex_2(sK0,sK4(u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f435,f222])).

fof(f435,plain,(
    k6_domain_1(u1_struct_0(sK0),sK4(u1_struct_0(sK1))) = u1_struct_0(k1_tex_2(sK0,sK4(u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f61,f60,f219,f221,f213,f218,f92])).

fof(f218,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK4(u1_struct_0(sK1))),sK0) ),
    inference(unit_resulting_resolution,[],[f60,f61,f213,f91])).

fof(f221,plain,(
    ~ v2_struct_0(k1_tex_2(sK0,sK4(u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f60,f61,f213,f86])).

fof(f219,plain,(
    v1_pre_topc(k1_tex_2(sK0,sK4(u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f60,f61,f213,f88])).

fof(f611,plain,(
    k1_tex_2(sK0,sK4(u1_struct_0(sK1))) = g1_pre_topc(u1_struct_0(k1_tex_2(sK0,sK4(u1_struct_0(sK1)))),u1_pre_topc(k1_tex_2(sK0,sK4(u1_struct_0(sK1))))) ),
    inference(unit_resulting_resolution,[],[f219,f436,f64])).

fof(f436,plain,(
    l1_pre_topc(k1_tex_2(sK0,sK4(u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f61,f218,f65])).

fof(f598,plain,(
    sK2(sK1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k1_tex_2(sK0,sK4(u1_struct_0(sK1))))) ),
    inference(backward_demodulation,[],[f446,f588])).

fof(f446,plain,(
    sK2(sK1) != g1_pre_topc(k1_tarski(sK4(u1_struct_0(sK1))),u1_pre_topc(k1_tex_2(sK0,sK4(u1_struct_0(sK1))))) ),
    inference(backward_demodulation,[],[f229,f441])).

fof(f229,plain,(
    sK2(sK1) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,sK4(u1_struct_0(sK1)))),u1_pre_topc(k1_tex_2(sK0,sK4(u1_struct_0(sK1))))) ),
    inference(backward_demodulation,[],[f223,f228])).

fof(f223,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,sK4(u1_struct_0(sK1)))),u1_pre_topc(k1_tex_2(sK0,sK4(u1_struct_0(sK1))))) ),
    inference(unit_resulting_resolution,[],[f213,f56])).

fof(f56,plain,(
    ! [X2] :
      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,X2)),u1_pre_topc(k1_tex_2(sK0,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f231,plain,(
    m1_pre_topc(sK2(sK1),sK0) ),
    inference(backward_demodulation,[],[f173,f228])).

fof(f173,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f61,f59,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:41:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (31361)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.50  % (31360)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.50  % (31349)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (31354)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (31371)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (31353)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (31350)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (31355)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (31349)Refutation not found, incomplete strategy% (31349)------------------------------
% 0.22/0.51  % (31349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (31374)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (31367)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (31370)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (31349)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (31349)Memory used [KB]: 10746
% 0.22/0.52  % (31349)Time elapsed: 0.095 s
% 0.22/0.52  % (31349)------------------------------
% 0.22/0.52  % (31349)------------------------------
% 0.22/0.52  % (31366)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (31363)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (31348)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (31369)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (31352)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (31358)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (31362)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (31368)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.53  % (31372)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (31359)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.54  % (31364)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.54  % (31356)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.55  % (31357)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.55  % (31365)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.57  % (31373)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 2.65/0.74  % (31356)Refutation found. Thanks to Tanya!
% 2.65/0.74  % SZS status Theorem for theBenchmark
% 2.65/0.74  % SZS output start Proof for theBenchmark
% 2.65/0.74  fof(f1916,plain,(
% 2.65/0.74    $false),
% 2.65/0.74    inference(subsumption_resolution,[],[f1915,f530])).
% 2.65/0.74  fof(f530,plain,(
% 2.65/0.74    u1_struct_0(sK1) = u1_struct_0(sK2(sK1))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f97,f106,f149,f136,f62])).
% 2.65/0.74  fof(f62,plain,(
% 2.65/0.74    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.65/0.74    inference(cnf_transformation,[],[f25])).
% 2.65/0.74  fof(f25,plain,(
% 2.65/0.74    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.65/0.74    inference(flattening,[],[f24])).
% 2.65/0.74  fof(f24,plain,(
% 2.65/0.74    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.65/0.74    inference(ennf_transformation,[],[f18])).
% 2.65/0.74  fof(f18,axiom,(
% 2.65/0.74    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 2.65/0.74  fof(f136,plain,(
% 2.65/0.74    r1_tarski(u1_struct_0(sK2(sK1)),u1_struct_0(sK1))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f94,f108,f66])).
% 2.65/0.74  fof(f66,plain,(
% 2.65/0.74    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.65/0.74    inference(cnf_transformation,[],[f30])).
% 2.65/0.74  fof(f30,plain,(
% 2.65/0.74    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.65/0.74    inference(ennf_transformation,[],[f11])).
% 2.65/0.74  fof(f11,axiom,(
% 2.65/0.74    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 2.65/0.74  fof(f108,plain,(
% 2.65/0.74    m1_pre_topc(sK2(sK1),sK1)),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f94,f57,f76])).
% 2.65/0.74  fof(f76,plain,(
% 2.65/0.74    ( ! [X0] : (~l1_pre_topc(X0) | v2_struct_0(X0) | m1_pre_topc(sK2(X0),X0)) )),
% 2.65/0.74    inference(cnf_transformation,[],[f45])).
% 2.65/0.74  fof(f45,plain,(
% 2.65/0.74    ! [X0] : (? [X1] : (v1_pre_topc(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.65/0.74    inference(flattening,[],[f44])).
% 2.65/0.74  fof(f44,plain,(
% 2.65/0.74    ! [X0] : (? [X1] : (v1_pre_topc(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.65/0.74    inference(ennf_transformation,[],[f7])).
% 2.65/0.74  fof(f7,axiom,(
% 2.65/0.74    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v1_pre_topc(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)))),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_pre_topc)).
% 2.65/0.74  fof(f57,plain,(
% 2.65/0.74    ~v2_struct_0(sK1)),
% 2.65/0.74    inference(cnf_transformation,[],[f23])).
% 2.65/0.74  fof(f23,plain,(
% 2.65/0.74    ? [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.65/0.74    inference(flattening,[],[f22])).
% 2.65/0.74  fof(f22,plain,(
% 2.65/0.74    ? [X0] : (? [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) & (m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.65/0.74    inference(ennf_transformation,[],[f21])).
% 2.65/0.74  fof(f21,negated_conjecture,(
% 2.65/0.74    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) => ? [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.65/0.74    inference(negated_conjecture,[],[f20])).
% 2.65/0.74  fof(f20,conjecture,(
% 2.65/0.74    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v7_struct_0(X1) & ~v2_struct_0(X1)) => ? [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tex_2)).
% 2.65/0.74  fof(f94,plain,(
% 2.65/0.74    l1_pre_topc(sK1)),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f59,f61,f65])).
% 2.65/0.74  fof(f65,plain,(
% 2.65/0.74    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 2.65/0.74    inference(cnf_transformation,[],[f29])).
% 2.65/0.74  fof(f29,plain,(
% 2.65/0.74    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.65/0.74    inference(ennf_transformation,[],[f4])).
% 2.65/0.74  fof(f4,axiom,(
% 2.65/0.74    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.65/0.74  fof(f61,plain,(
% 2.65/0.74    l1_pre_topc(sK0)),
% 2.65/0.74    inference(cnf_transformation,[],[f23])).
% 2.65/0.74  fof(f59,plain,(
% 2.65/0.74    m1_pre_topc(sK1,sK0)),
% 2.65/0.74    inference(cnf_transformation,[],[f23])).
% 2.65/0.74  fof(f149,plain,(
% 2.65/0.74    ~v1_xboole_0(u1_struct_0(sK2(sK1)))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f99,f138,f69])).
% 2.65/0.74  fof(f69,plain,(
% 2.65/0.74    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.65/0.74    inference(cnf_transformation,[],[f33])).
% 2.65/0.74  fof(f33,plain,(
% 2.65/0.74    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.65/0.74    inference(flattening,[],[f32])).
% 2.65/0.74  fof(f32,plain,(
% 2.65/0.74    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.65/0.74    inference(ennf_transformation,[],[f5])).
% 2.65/0.74  fof(f5,axiom,(
% 2.65/0.74    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 2.65/0.74  fof(f138,plain,(
% 2.65/0.74    l1_struct_0(sK2(sK1))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f137,f63])).
% 2.65/0.74  fof(f63,plain,(
% 2.65/0.74    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.65/0.74    inference(cnf_transformation,[],[f26])).
% 2.65/0.74  fof(f26,plain,(
% 2.65/0.74    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.65/0.74    inference(ennf_transformation,[],[f3])).
% 2.65/0.74  fof(f3,axiom,(
% 2.65/0.74    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.65/0.74  fof(f137,plain,(
% 2.65/0.74    l1_pre_topc(sK2(sK1))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f94,f108,f65])).
% 2.65/0.74  fof(f99,plain,(
% 2.65/0.74    ~v2_struct_0(sK2(sK1))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f57,f94,f77])).
% 2.65/0.74  fof(f77,plain,(
% 2.65/0.74    ( ! [X0] : (~v2_struct_0(sK2(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.65/0.74    inference(cnf_transformation,[],[f45])).
% 2.65/0.74  fof(f106,plain,(
% 2.65/0.74    v1_zfmisc_1(u1_struct_0(sK1))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f58,f96,f83])).
% 2.65/0.74  fof(f83,plain,(
% 2.65/0.74    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 2.65/0.74    inference(cnf_transformation,[],[f49])).
% 2.65/0.74  fof(f49,plain,(
% 2.65/0.74    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 2.65/0.74    inference(flattening,[],[f48])).
% 2.65/0.74  fof(f48,plain,(
% 2.65/0.74    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 2.65/0.74    inference(ennf_transformation,[],[f6])).
% 2.65/0.74  fof(f6,axiom,(
% 2.65/0.74    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 2.65/0.74  fof(f96,plain,(
% 2.65/0.74    l1_struct_0(sK1)),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f94,f63])).
% 2.65/0.74  fof(f58,plain,(
% 2.65/0.74    v7_struct_0(sK1)),
% 2.65/0.74    inference(cnf_transformation,[],[f23])).
% 2.65/0.74  fof(f97,plain,(
% 2.65/0.74    ~v1_xboole_0(u1_struct_0(sK1))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f57,f96,f69])).
% 2.65/0.74  fof(f1915,plain,(
% 2.65/0.74    u1_struct_0(sK1) != u1_struct_0(sK2(sK1))),
% 2.65/0.74    inference(forward_demodulation,[],[f1914,f590])).
% 2.65/0.74  fof(f590,plain,(
% 2.65/0.74    u1_struct_0(sK1) = k6_domain_1(u1_struct_0(sK0),sK4(u1_struct_0(sK1)))),
% 2.65/0.74    inference(backward_demodulation,[],[f222,f588])).
% 2.65/0.74  fof(f588,plain,(
% 2.65/0.74    u1_struct_0(sK1) = k1_tarski(sK4(u1_struct_0(sK1)))),
% 2.65/0.74    inference(forward_demodulation,[],[f574,f530])).
% 2.65/0.74  fof(f574,plain,(
% 2.65/0.74    u1_struct_0(sK2(sK1)) = k1_tarski(sK4(u1_struct_0(sK1)))),
% 2.65/0.74    inference(backward_demodulation,[],[f354,f567])).
% 2.65/0.74  fof(f567,plain,(
% 2.65/0.74    sK2(sK1) = k1_tex_2(sK1,sK4(u1_struct_0(sK1)))),
% 2.65/0.74    inference(forward_demodulation,[],[f566,f362])).
% 2.65/0.74  fof(f362,plain,(
% 2.65/0.74    sK2(sK1) = g1_pre_topc(k1_tarski(sK4(u1_struct_0(sK1))),u1_pre_topc(k1_tex_2(sK1,sK4(u1_struct_0(sK1)))))),
% 2.65/0.74    inference(forward_demodulation,[],[f361,f228])).
% 2.65/0.74  fof(f228,plain,(
% 2.65/0.74    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2(sK1)),
% 2.65/0.74    inference(forward_demodulation,[],[f227,f147])).
% 2.65/0.74  fof(f147,plain,(
% 2.65/0.74    sK2(sK1) = g1_pre_topc(u1_struct_0(sK2(sK1)),u1_pre_topc(sK2(sK1)))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f101,f137,f64])).
% 2.65/0.74  fof(f64,plain,(
% 2.65/0.74    ( ! [X0] : (~v1_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) )),
% 2.65/0.74    inference(cnf_transformation,[],[f28])).
% 2.65/0.74  fof(f28,plain,(
% 2.65/0.74    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.65/0.74    inference(flattening,[],[f27])).
% 2.65/0.74  fof(f27,plain,(
% 2.65/0.74    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 2.65/0.74    inference(ennf_transformation,[],[f2])).
% 2.65/0.74  fof(f2,axiom,(
% 2.65/0.74    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 2.65/0.74  fof(f101,plain,(
% 2.65/0.74    v1_pre_topc(sK2(sK1))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f57,f94,f78])).
% 2.65/0.74  fof(f78,plain,(
% 2.65/0.74    ( ! [X0] : (v1_pre_topc(sK2(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.65/0.74    inference(cnf_transformation,[],[f45])).
% 2.65/0.74  fof(f227,plain,(
% 2.65/0.74    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2(sK1)),u1_pre_topc(sK2(sK1)))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f94,f108,f210,f57,f75])).
% 2.65/0.74  fof(f75,plain,(
% 2.65/0.74    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )),
% 2.65/0.74    inference(cnf_transformation,[],[f43])).
% 2.65/0.74  fof(f43,plain,(
% 2.65/0.74    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v1_tex_2(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.65/0.74    inference(flattening,[],[f42])).
% 2.65/0.74  fof(f42,plain,(
% 2.65/0.74    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v1_tex_2(X1,X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.65/0.74    inference(ennf_transformation,[],[f17])).
% 2.65/0.74  fof(f17,axiom,(
% 2.65/0.74    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tex_2)).
% 2.65/0.74  fof(f210,plain,(
% 2.65/0.74    ~v1_tex_2(sK2(sK1),sK1)),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f99,f108,f94,f57,f58,f70])).
% 2.65/0.74  fof(f70,plain,(
% 2.65/0.74    ( ! [X0,X1] : (~v7_struct_0(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~v1_tex_2(X1,X0)) )),
% 2.65/0.74    inference(cnf_transformation,[],[f35])).
% 2.65/0.74  fof(f35,plain,(
% 2.65/0.74    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 2.65/0.74    inference(flattening,[],[f34])).
% 2.65/0.74  fof(f34,plain,(
% 2.65/0.74    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 2.65/0.74    inference(ennf_transformation,[],[f12])).
% 2.65/0.74  fof(f12,axiom,(
% 2.65/0.74    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).
% 2.65/0.74  fof(f361,plain,(
% 2.65/0.74    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(k1_tarski(sK4(u1_struct_0(sK1))),u1_pre_topc(k1_tex_2(sK1,sK4(u1_struct_0(sK1)))))),
% 2.65/0.74    inference(forward_demodulation,[],[f360,f354])).
% 2.65/0.74  fof(f360,plain,(
% 2.65/0.74    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK4(u1_struct_0(sK1)))),u1_pre_topc(k1_tex_2(sK1,sK4(u1_struct_0(sK1)))))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f57,f94,f204,f212,f75])).
% 2.65/0.74  fof(f212,plain,(
% 2.65/0.74    ~v1_tex_2(k1_tex_2(sK1,sK4(u1_struct_0(sK1))),sK1)),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f57,f58,f94,f84,f71])).
% 2.65/0.74  fof(f71,plain,(
% 2.65/0.74    ( ! [X0,X1] : (~v7_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0) | v2_struct_0(X0)) )),
% 2.65/0.74    inference(cnf_transformation,[],[f37])).
% 2.65/0.74  fof(f37,plain,(
% 2.65/0.74    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_tex_2(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.65/0.74    inference(flattening,[],[f36])).
% 2.65/0.74  fof(f36,plain,(
% 2.65/0.74    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.65/0.74    inference(ennf_transformation,[],[f19])).
% 2.65/0.74  fof(f19,axiom,(
% 2.65/0.74    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_tex_2(k1_tex_2(X0,X1),X0))))),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tex_2)).
% 2.65/0.74  fof(f84,plain,(
% 2.65/0.74    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 2.65/0.74    inference(cnf_transformation,[],[f1])).
% 2.65/0.74  fof(f1,axiom,(
% 2.65/0.74    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 2.65/0.74  fof(f204,plain,(
% 2.65/0.74    m1_pre_topc(k1_tex_2(sK1,sK4(u1_struct_0(sK1))),sK1)),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f94,f57,f84,f91])).
% 2.65/0.74  fof(f91,plain,(
% 2.65/0.74    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0)) )),
% 2.65/0.74    inference(cnf_transformation,[],[f55])).
% 2.65/0.74  fof(f55,plain,(
% 2.65/0.74    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.65/0.74    inference(flattening,[],[f54])).
% 2.65/0.74  fof(f54,plain,(
% 2.65/0.74    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.65/0.74    inference(ennf_transformation,[],[f14])).
% 2.65/0.74  fof(f14,axiom,(
% 2.65/0.74    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 2.65/0.74  fof(f566,plain,(
% 2.65/0.74    k1_tex_2(sK1,sK4(u1_struct_0(sK1))) = g1_pre_topc(k1_tarski(sK4(u1_struct_0(sK1))),u1_pre_topc(k1_tex_2(sK1,sK4(u1_struct_0(sK1)))))),
% 2.65/0.74    inference(forward_demodulation,[],[f548,f354])).
% 2.65/0.74  fof(f548,plain,(
% 2.65/0.74    k1_tex_2(sK1,sK4(u1_struct_0(sK1))) = g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK4(u1_struct_0(sK1)))),u1_pre_topc(k1_tex_2(sK1,sK4(u1_struct_0(sK1)))))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f197,f348,f64])).
% 2.65/0.74  fof(f348,plain,(
% 2.65/0.74    l1_pre_topc(k1_tex_2(sK1,sK4(u1_struct_0(sK1))))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f94,f204,f65])).
% 2.65/0.74  fof(f197,plain,(
% 2.65/0.74    v1_pre_topc(k1_tex_2(sK1,sK4(u1_struct_0(sK1))))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f57,f94,f84,f88])).
% 2.65/0.74  fof(f88,plain,(
% 2.65/0.74    ( ! [X0,X1] : (v1_pre_topc(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 2.65/0.74    inference(cnf_transformation,[],[f53])).
% 2.65/0.74  fof(f53,plain,(
% 2.65/0.74    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.65/0.74    inference(flattening,[],[f52])).
% 2.65/0.74  fof(f52,plain,(
% 2.65/0.74    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.65/0.74    inference(ennf_transformation,[],[f15])).
% 2.65/0.74  fof(f15,axiom,(
% 2.65/0.74    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).
% 2.65/0.74  fof(f354,plain,(
% 2.65/0.74    k1_tarski(sK4(u1_struct_0(sK1))) = u1_struct_0(k1_tex_2(sK1,sK4(u1_struct_0(sK1))))),
% 2.65/0.74    inference(forward_demodulation,[],[f347,f172])).
% 2.65/0.74  fof(f172,plain,(
% 2.65/0.74    k1_tarski(sK4(u1_struct_0(sK1))) = k6_domain_1(u1_struct_0(sK1),sK4(u1_struct_0(sK1)))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f84,f97,f85])).
% 2.65/0.74  fof(f85,plain,(
% 2.65/0.74    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 2.65/0.74    inference(cnf_transformation,[],[f51])).
% 2.65/0.74  fof(f51,plain,(
% 2.65/0.74    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.65/0.74    inference(flattening,[],[f50])).
% 2.65/0.74  fof(f50,plain,(
% 2.65/0.74    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.65/0.74    inference(ennf_transformation,[],[f9])).
% 2.65/0.74  fof(f9,axiom,(
% 2.65/0.74    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 2.65/0.74  fof(f347,plain,(
% 2.65/0.74    k6_domain_1(u1_struct_0(sK1),sK4(u1_struct_0(sK1))) = u1_struct_0(k1_tex_2(sK1,sK4(u1_struct_0(sK1))))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f94,f57,f197,f185,f84,f204,f92])).
% 2.65/0.74  fof(f92,plain,(
% 2.65/0.74    ( ! [X0,X1] : (~v1_pre_topc(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(k1_tex_2(X0,X1)) | v2_struct_0(X0) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))) )),
% 2.65/0.74    inference(equality_resolution,[],[f73])).
% 2.65/0.74  fof(f73,plain,(
% 2.65/0.74    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2) )),
% 2.65/0.74    inference(cnf_transformation,[],[f39])).
% 2.65/0.74  fof(f39,plain,(
% 2.65/0.74    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.65/0.74    inference(flattening,[],[f38])).
% 2.65/0.74  fof(f38,plain,(
% 2.65/0.74    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.65/0.74    inference(ennf_transformation,[],[f13])).
% 2.65/0.74  fof(f13,axiom,(
% 2.65/0.74    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).
% 2.65/0.74  fof(f185,plain,(
% 2.65/0.74    ~v2_struct_0(k1_tex_2(sK1,sK4(u1_struct_0(sK1))))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f57,f94,f84,f86])).
% 2.65/0.74  fof(f86,plain,(
% 2.65/0.74    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 2.65/0.74    inference(cnf_transformation,[],[f53])).
% 2.65/0.74  fof(f222,plain,(
% 2.65/0.74    k1_tarski(sK4(u1_struct_0(sK1))) = k6_domain_1(u1_struct_0(sK0),sK4(u1_struct_0(sK1)))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f95,f213,f85])).
% 2.65/0.74  fof(f213,plain,(
% 2.65/0.74    m1_subset_1(sK4(u1_struct_0(sK1)),u1_struct_0(sK0))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f60,f61,f59,f57,f84,f74])).
% 2.65/0.74  fof(f74,plain,(
% 2.65/0.74    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 2.65/0.74    inference(cnf_transformation,[],[f41])).
% 2.65/0.74  fof(f41,plain,(
% 2.65/0.74    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.65/0.74    inference(flattening,[],[f40])).
% 2.65/0.74  fof(f40,plain,(
% 2.65/0.74    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.65/0.74    inference(ennf_transformation,[],[f8])).
% 2.65/0.74  fof(f8,axiom,(
% 2.65/0.74    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 2.65/0.74  fof(f60,plain,(
% 2.65/0.74    ~v2_struct_0(sK0)),
% 2.65/0.74    inference(cnf_transformation,[],[f23])).
% 2.65/0.74  fof(f95,plain,(
% 2.65/0.74    ~v1_xboole_0(u1_struct_0(sK0))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f60,f93,f69])).
% 2.65/0.74  fof(f93,plain,(
% 2.65/0.74    l1_struct_0(sK0)),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f61,f63])).
% 2.65/0.74  fof(f1914,plain,(
% 2.65/0.74    u1_struct_0(sK2(sK1)) != k6_domain_1(u1_struct_0(sK0),sK4(u1_struct_0(sK1)))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f61,f60,f99,f101,f231,f213,f1913,f72])).
% 2.65/0.74  fof(f72,plain,(
% 2.65/0.74    ( ! [X2,X0,X1] : (u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0) | k1_tex_2(X0,X1) = X2) )),
% 2.65/0.74    inference(cnf_transformation,[],[f39])).
% 2.65/0.74  fof(f1913,plain,(
% 2.65/0.74    sK2(sK1) != k1_tex_2(sK0,sK4(u1_struct_0(sK1)))),
% 2.65/0.74    inference(superposition,[],[f598,f629])).
% 2.65/0.74  fof(f629,plain,(
% 2.65/0.74    k1_tex_2(sK0,sK4(u1_struct_0(sK1))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k1_tex_2(sK0,sK4(u1_struct_0(sK1)))))),
% 2.65/0.74    inference(forward_demodulation,[],[f611,f593])).
% 2.65/0.74  fof(f593,plain,(
% 2.65/0.74    u1_struct_0(sK1) = u1_struct_0(k1_tex_2(sK0,sK4(u1_struct_0(sK1))))),
% 2.65/0.74    inference(backward_demodulation,[],[f441,f588])).
% 2.65/0.74  fof(f441,plain,(
% 2.65/0.74    k1_tarski(sK4(u1_struct_0(sK1))) = u1_struct_0(k1_tex_2(sK0,sK4(u1_struct_0(sK1))))),
% 2.65/0.74    inference(forward_demodulation,[],[f435,f222])).
% 2.65/0.74  fof(f435,plain,(
% 2.65/0.74    k6_domain_1(u1_struct_0(sK0),sK4(u1_struct_0(sK1))) = u1_struct_0(k1_tex_2(sK0,sK4(u1_struct_0(sK1))))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f61,f60,f219,f221,f213,f218,f92])).
% 2.65/0.74  fof(f218,plain,(
% 2.65/0.74    m1_pre_topc(k1_tex_2(sK0,sK4(u1_struct_0(sK1))),sK0)),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f60,f61,f213,f91])).
% 2.65/0.74  fof(f221,plain,(
% 2.65/0.74    ~v2_struct_0(k1_tex_2(sK0,sK4(u1_struct_0(sK1))))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f60,f61,f213,f86])).
% 2.65/0.74  fof(f219,plain,(
% 2.65/0.74    v1_pre_topc(k1_tex_2(sK0,sK4(u1_struct_0(sK1))))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f60,f61,f213,f88])).
% 2.65/0.74  fof(f611,plain,(
% 2.65/0.74    k1_tex_2(sK0,sK4(u1_struct_0(sK1))) = g1_pre_topc(u1_struct_0(k1_tex_2(sK0,sK4(u1_struct_0(sK1)))),u1_pre_topc(k1_tex_2(sK0,sK4(u1_struct_0(sK1)))))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f219,f436,f64])).
% 2.65/0.74  fof(f436,plain,(
% 2.65/0.74    l1_pre_topc(k1_tex_2(sK0,sK4(u1_struct_0(sK1))))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f61,f218,f65])).
% 2.65/0.74  fof(f598,plain,(
% 2.65/0.74    sK2(sK1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k1_tex_2(sK0,sK4(u1_struct_0(sK1)))))),
% 2.65/0.74    inference(backward_demodulation,[],[f446,f588])).
% 2.65/0.74  fof(f446,plain,(
% 2.65/0.74    sK2(sK1) != g1_pre_topc(k1_tarski(sK4(u1_struct_0(sK1))),u1_pre_topc(k1_tex_2(sK0,sK4(u1_struct_0(sK1)))))),
% 2.65/0.74    inference(backward_demodulation,[],[f229,f441])).
% 2.65/0.74  fof(f229,plain,(
% 2.65/0.74    sK2(sK1) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,sK4(u1_struct_0(sK1)))),u1_pre_topc(k1_tex_2(sK0,sK4(u1_struct_0(sK1)))))),
% 2.65/0.74    inference(backward_demodulation,[],[f223,f228])).
% 2.65/0.74  fof(f223,plain,(
% 2.65/0.74    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,sK4(u1_struct_0(sK1)))),u1_pre_topc(k1_tex_2(sK0,sK4(u1_struct_0(sK1)))))),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f213,f56])).
% 2.65/0.74  fof(f56,plain,(
% 2.65/0.74    ( ! [X2] : (g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK0,X2)),u1_pre_topc(k1_tex_2(sK0,X2))) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 2.65/0.74    inference(cnf_transformation,[],[f23])).
% 2.65/0.74  fof(f231,plain,(
% 2.65/0.74    m1_pre_topc(sK2(sK1),sK0)),
% 2.65/0.74    inference(backward_demodulation,[],[f173,f228])).
% 2.65/0.74  fof(f173,plain,(
% 2.65/0.74    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)),
% 2.65/0.74    inference(unit_resulting_resolution,[],[f61,f59,f68])).
% 2.65/0.74  fof(f68,plain,(
% 2.65/0.74    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)) )),
% 2.65/0.74    inference(cnf_transformation,[],[f31])).
% 2.65/0.74  fof(f31,plain,(
% 2.65/0.74    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.65/0.74    inference(ennf_transformation,[],[f10])).
% 2.65/0.74  fof(f10,axiom,(
% 2.65/0.74    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.65/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 2.65/0.74  % SZS output end Proof for theBenchmark
% 2.65/0.74  % (31356)------------------------------
% 2.65/0.74  % (31356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.65/0.74  % (31356)Termination reason: Refutation
% 2.65/0.74  
% 2.65/0.74  % (31356)Memory used [KB]: 3198
% 2.65/0.74  % (31356)Time elapsed: 0.273 s
% 2.65/0.74  % (31356)------------------------------
% 2.65/0.74  % (31356)------------------------------
% 2.65/0.74  % (31347)Success in time 0.371 s
%------------------------------------------------------------------------------
