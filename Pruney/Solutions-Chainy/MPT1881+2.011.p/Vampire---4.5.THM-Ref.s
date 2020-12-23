%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:54 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 964 expanded)
%              Number of leaves         :   19 ( 190 expanded)
%              Depth                    :   23
%              Number of atoms          :  403 (4212 expanded)
%              Number of equality atoms :   51 ( 198 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f350,plain,(
    $false ),
    inference(subsumption_resolution,[],[f349,f312])).

fof(f312,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f110,f306])).

fof(f306,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f303,f44])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

fof(f303,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f230,f302])).

fof(f302,plain,(
    ! [X0] : v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) ),
    inference(subsumption_resolution,[],[f301,f48])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f301,plain,(
    ! [X0] :
      ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f245,f47])).

fof(f47,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f245,plain,(
    ! [X26,X25] :
      ( ~ v1_tdlat_3(X25)
      | v3_pre_topc(k4_xboole_0(u1_struct_0(X25),X26),X25)
      | ~ l1_pre_topc(X25) ) ),
    inference(resolution,[],[f185,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X0) ) ),
    inference(subsumption_resolution,[],[f66,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f185,plain,(
    ! [X2,X3] : m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2)) ),
    inference(resolution,[],[f87,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f87,plain,(
    ! [X0,X1] : r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f80,f69])).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f80,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f230,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f229,f92])).

fof(f92,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) ),
    inference(resolution,[],[f77,f82])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f51,f50])).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f229,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f228,f48])).

fof(f228,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v4_pre_topc(X0,sK0) ) ),
    inference(superposition,[],[f55,f165])).

fof(f165,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(backward_demodulation,[],[f160,f164])).

fof(f164,plain,(
    u1_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0)) ),
    inference(subsumption_resolution,[],[f163,f86])).

fof(f86,plain,(
    v1_tops_1(sK2(sK0),sK0) ),
    inference(resolution,[],[f62,f48])).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v1_tops_1(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_tops_1)).

fof(f163,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0))
    | ~ v1_tops_1(sK2(sK0),sK0) ),
    inference(subsumption_resolution,[],[f148,f48])).

fof(f148,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0))
    | ~ v1_tops_1(sK2(sK0),sK0) ),
    inference(resolution,[],[f88,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(f88,plain,(
    m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f61,f48])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f160,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0)) ),
    inference(subsumption_resolution,[],[f159,f86])).

fof(f159,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0))
    | ~ v1_tops_1(sK2(sK0),sK0) ),
    inference(subsumption_resolution,[],[f146,f48])).

fof(f146,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0))
    | ~ v1_tops_1(sK2(sK0),sK0) ),
    inference(resolution,[],[f88,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f110,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f109,f48])).

fof(f109,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f54,f44])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f349,plain,(
    sK1 != k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f348,f317])).

fof(f317,plain,(
    sK1 = u1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f314])).

fof(f314,plain,
    ( sK1 = u1_struct_0(sK0)
    | sK1 = u1_struct_0(sK0) ),
    inference(backward_demodulation,[],[f246,f312])).

fof(f246,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f231,f122])).

fof(f122,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f121,f48])).

fof(f121,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f60,f44])).

fof(f231,plain,
    ( v1_tops_1(sK1,sK0)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f186,f135])).

fof(f135,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f134,f97])).

fof(f97,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f96,f47])).

fof(f96,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v1_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f95,f48])).

fof(f95,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ v1_tdlat_3(sK0) ),
    inference(resolution,[],[f84,f44])).

fof(f134,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f133,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f133,plain,
    ( v2_struct_0(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f132,f48])).

fof(f132,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f131,f46])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f131,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f64,f44])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

fof(f186,plain,
    ( v3_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f90,f42])).

fof(f42,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f90,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f71,f44])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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

fof(f348,plain,(
    u1_struct_0(sK0) != k2_pre_topc(sK0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f333,f345])).

fof(f345,plain,(
    ~ v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f141,f344])).

fof(f344,plain,(
    ~ v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f319,f81])).

fof(f81,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f49,f50])).

fof(f49,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f319,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f43,f317])).

fof(f43,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f141,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f140,f107])).

fof(f107,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f106,f45])).

fof(f106,plain,
    ( v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f105,f48])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f104,f47])).

fof(f104,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f83,f44])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f63,f52])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f140,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f139,f45])).

fof(f139,plain,
    ( v2_struct_0(sK0)
    | ~ v1_tops_1(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f138,f48])).

fof(f138,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_tops_1(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f137,f46])).

fof(f137,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_tops_1(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f65,f44])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

fof(f333,plain,
    ( v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) != k2_pre_topc(sK0,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f193,f317])).

fof(f193,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,u1_struct_0(sK0))
    | v1_tops_1(u1_struct_0(sK0),sK0) ),
    inference(forward_demodulation,[],[f192,f165])).

fof(f192,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,u1_struct_0(sK0))
    | v1_tops_1(u1_struct_0(sK0),sK0) ),
    inference(resolution,[],[f111,f48])).

fof(f111,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,u1_struct_0(X0))
      | v1_tops_1(u1_struct_0(X0),X0) ) ),
    inference(resolution,[],[f57,f82])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (31881)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (31879)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (31884)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (31877)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (31893)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (31877)Refutation not found, incomplete strategy% (31877)------------------------------
% 0.21/0.49  % (31877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31877)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (31877)Memory used [KB]: 10746
% 0.21/0.49  % (31877)Time elapsed: 0.069 s
% 0.21/0.49  % (31877)------------------------------
% 0.21/0.49  % (31877)------------------------------
% 0.21/0.49  % (31885)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (31879)Refutation not found, incomplete strategy% (31879)------------------------------
% 0.21/0.49  % (31879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31879)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (31879)Memory used [KB]: 10746
% 0.21/0.49  % (31879)Time elapsed: 0.079 s
% 0.21/0.49  % (31879)------------------------------
% 0.21/0.49  % (31879)------------------------------
% 0.21/0.50  % (31887)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (31878)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (31891)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (31876)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (31896)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (31882)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (31891)Refutation not found, incomplete strategy% (31891)------------------------------
% 0.21/0.51  % (31891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31891)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31891)Memory used [KB]: 6268
% 0.21/0.51  % (31891)Time elapsed: 0.101 s
% 0.21/0.51  % (31891)------------------------------
% 0.21/0.51  % (31891)------------------------------
% 0.21/0.51  % (31876)Refutation not found, incomplete strategy% (31876)------------------------------
% 0.21/0.51  % (31876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31876)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31876)Memory used [KB]: 6268
% 0.21/0.51  % (31876)Time elapsed: 0.095 s
% 0.21/0.51  % (31876)------------------------------
% 0.21/0.51  % (31876)------------------------------
% 0.21/0.51  % (31894)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (31883)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.28/0.51  % (31893)Refutation found. Thanks to Tanya!
% 1.28/0.51  % SZS status Theorem for theBenchmark
% 1.28/0.51  % SZS output start Proof for theBenchmark
% 1.28/0.51  fof(f350,plain,(
% 1.28/0.51    $false),
% 1.28/0.51    inference(subsumption_resolution,[],[f349,f312])).
% 1.28/0.51  fof(f312,plain,(
% 1.28/0.51    sK1 = k2_pre_topc(sK0,sK1)),
% 1.28/0.51    inference(subsumption_resolution,[],[f110,f306])).
% 1.28/0.51  fof(f306,plain,(
% 1.28/0.51    v4_pre_topc(sK1,sK0)),
% 1.28/0.51    inference(resolution,[],[f303,f44])).
% 1.28/0.51  fof(f44,plain,(
% 1.28/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.28/0.51    inference(cnf_transformation,[],[f22])).
% 1.28/0.51  fof(f22,plain,(
% 1.28/0.51    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.28/0.51    inference(flattening,[],[f21])).
% 1.28/0.51  fof(f21,plain,(
% 1.28/0.51    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.28/0.51    inference(ennf_transformation,[],[f20])).
% 1.28/0.51  fof(f20,negated_conjecture,(
% 1.28/0.51    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.28/0.51    inference(negated_conjecture,[],[f19])).
% 1.28/0.51  fof(f19,conjecture,(
% 1.28/0.51    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).
% 1.28/0.51  fof(f303,plain,(
% 1.28/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 1.28/0.51    inference(subsumption_resolution,[],[f230,f302])).
% 1.28/0.51  fof(f302,plain,(
% 1.28/0.51    ( ! [X0] : (v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0)) )),
% 1.28/0.51    inference(subsumption_resolution,[],[f301,f48])).
% 1.28/0.51  fof(f48,plain,(
% 1.28/0.51    l1_pre_topc(sK0)),
% 1.28/0.51    inference(cnf_transformation,[],[f22])).
% 1.28/0.51  fof(f301,plain,(
% 1.28/0.51    ( ! [X0] : (v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) | ~l1_pre_topc(sK0)) )),
% 1.28/0.51    inference(resolution,[],[f245,f47])).
% 1.28/0.51  fof(f47,plain,(
% 1.28/0.51    v1_tdlat_3(sK0)),
% 1.28/0.51    inference(cnf_transformation,[],[f22])).
% 1.28/0.51  fof(f245,plain,(
% 1.28/0.51    ( ! [X26,X25] : (~v1_tdlat_3(X25) | v3_pre_topc(k4_xboole_0(u1_struct_0(X25),X26),X25) | ~l1_pre_topc(X25)) )),
% 1.28/0.51    inference(resolution,[],[f185,f84])).
% 1.28/0.51  fof(f84,plain,(
% 1.28/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(X1,X0) | ~v1_tdlat_3(X0)) )),
% 1.28/0.51    inference(subsumption_resolution,[],[f66,f52])).
% 1.28/0.51  fof(f52,plain,(
% 1.28/0.51    ( ! [X0] : (~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 1.28/0.51    inference(cnf_transformation,[],[f24])).
% 1.28/0.51  fof(f24,plain,(
% 1.28/0.51    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.28/0.51    inference(flattening,[],[f23])).
% 1.28/0.51  fof(f23,plain,(
% 1.28/0.51    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.28/0.51    inference(ennf_transformation,[],[f12])).
% 1.28/0.51  fof(f12,axiom,(
% 1.28/0.51    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 1.28/0.51  fof(f66,plain,(
% 1.28/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0) | ~v1_tdlat_3(X0)) )),
% 1.28/0.51    inference(cnf_transformation,[],[f38])).
% 1.28/0.51  fof(f38,plain,(
% 1.28/0.51    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.28/0.51    inference(flattening,[],[f37])).
% 1.28/0.51  fof(f37,plain,(
% 1.28/0.51    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.28/0.51    inference(ennf_transformation,[],[f15])).
% 1.28/0.51  fof(f15,axiom,(
% 1.28/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).
% 1.28/0.51  fof(f185,plain,(
% 1.28/0.51    ( ! [X2,X3] : (m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2))) )),
% 1.28/0.51    inference(resolution,[],[f87,f70])).
% 1.28/0.51  fof(f70,plain,(
% 1.28/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.28/0.51    inference(cnf_transformation,[],[f39])).
% 1.28/0.51  fof(f39,plain,(
% 1.28/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.28/0.51    inference(ennf_transformation,[],[f7])).
% 1.28/0.51  fof(f7,axiom,(
% 1.28/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.28/0.51  fof(f87,plain,(
% 1.28/0.51    ( ! [X0,X1] : (r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 1.28/0.51    inference(resolution,[],[f80,f69])).
% 1.28/0.51  fof(f69,plain,(
% 1.28/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.28/0.51    inference(cnf_transformation,[],[f1])).
% 1.28/0.51  fof(f1,axiom,(
% 1.28/0.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.28/0.51  fof(f80,plain,(
% 1.28/0.51    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 1.28/0.51    inference(equality_resolution,[],[f73])).
% 1.28/0.51  fof(f73,plain,(
% 1.28/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.28/0.51    inference(cnf_transformation,[],[f2])).
% 1.28/0.51  fof(f2,axiom,(
% 1.28/0.51    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.28/0.51  fof(f230,plain,(
% 1.28/0.51    ( ! [X0] : (~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 1.28/0.51    inference(forward_demodulation,[],[f229,f92])).
% 1.28/0.51  fof(f92,plain,(
% 1.28/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 1.28/0.51    inference(resolution,[],[f77,f82])).
% 1.28/0.51  fof(f82,plain,(
% 1.28/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.28/0.51    inference(forward_demodulation,[],[f51,f50])).
% 1.28/0.51  fof(f50,plain,(
% 1.28/0.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.28/0.51    inference(cnf_transformation,[],[f3])).
% 1.28/0.51  fof(f3,axiom,(
% 1.28/0.51    ! [X0] : k2_subset_1(X0) = X0),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.28/0.51  fof(f51,plain,(
% 1.28/0.51    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.28/0.51    inference(cnf_transformation,[],[f4])).
% 1.28/0.51  fof(f4,axiom,(
% 1.28/0.51    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.28/0.51  fof(f77,plain,(
% 1.28/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 1.28/0.51    inference(cnf_transformation,[],[f41])).
% 1.28/0.51  fof(f41,plain,(
% 1.28/0.51    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.51    inference(ennf_transformation,[],[f5])).
% 1.28/0.51  fof(f5,axiom,(
% 1.28/0.51    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.28/0.51  fof(f229,plain,(
% 1.28/0.51    ( ! [X0] : (~v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 1.28/0.51    inference(subsumption_resolution,[],[f228,f48])).
% 1.28/0.51  fof(f228,plain,(
% 1.28/0.51    ( ! [X0] : (~v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v4_pre_topc(X0,sK0)) )),
% 1.28/0.51    inference(superposition,[],[f55,f165])).
% 1.28/0.51  fof(f165,plain,(
% 1.28/0.51    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.28/0.51    inference(backward_demodulation,[],[f160,f164])).
% 1.28/0.51  fof(f164,plain,(
% 1.28/0.51    u1_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0))),
% 1.28/0.51    inference(subsumption_resolution,[],[f163,f86])).
% 1.28/0.51  fof(f86,plain,(
% 1.28/0.51    v1_tops_1(sK2(sK0),sK0)),
% 1.28/0.51    inference(resolution,[],[f62,f48])).
% 1.28/0.51  fof(f62,plain,(
% 1.28/0.51    ( ! [X0] : (~l1_pre_topc(X0) | v1_tops_1(sK2(X0),X0)) )),
% 1.28/0.51    inference(cnf_transformation,[],[f30])).
% 1.28/0.51  fof(f30,plain,(
% 1.28/0.51    ! [X0] : (? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.28/0.51    inference(ennf_transformation,[],[f11])).
% 1.28/0.51  fof(f11,axiom,(
% 1.28/0.51    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_tops_1)).
% 1.28/0.51  fof(f163,plain,(
% 1.28/0.51    u1_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0)) | ~v1_tops_1(sK2(sK0),sK0)),
% 1.28/0.51    inference(subsumption_resolution,[],[f148,f48])).
% 1.28/0.51  fof(f148,plain,(
% 1.28/0.51    ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0)) | ~v1_tops_1(sK2(sK0),sK0)),
% 1.28/0.51    inference(resolution,[],[f88,f60])).
% 1.28/0.51  fof(f60,plain,(
% 1.28/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0)) )),
% 1.28/0.51    inference(cnf_transformation,[],[f29])).
% 1.28/0.51  fof(f29,plain,(
% 1.28/0.51    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.28/0.51    inference(ennf_transformation,[],[f13])).
% 1.28/0.51  fof(f13,axiom,(
% 1.28/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).
% 1.28/0.51  fof(f88,plain,(
% 1.28/0.51    m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.28/0.51    inference(resolution,[],[f61,f48])).
% 1.28/0.51  fof(f61,plain,(
% 1.28/0.51    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.28/0.51    inference(cnf_transformation,[],[f30])).
% 1.28/0.51  fof(f160,plain,(
% 1.28/0.51    k2_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0))),
% 1.28/0.51    inference(subsumption_resolution,[],[f159,f86])).
% 1.28/0.51  fof(f159,plain,(
% 1.28/0.51    k2_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0)) | ~v1_tops_1(sK2(sK0),sK0)),
% 1.28/0.51    inference(subsumption_resolution,[],[f146,f48])).
% 1.28/0.51  fof(f146,plain,(
% 1.28/0.51    ~l1_pre_topc(sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK2(sK0)) | ~v1_tops_1(sK2(sK0),sK0)),
% 1.28/0.51    inference(resolution,[],[f88,f58])).
% 1.28/0.51  fof(f58,plain,(
% 1.28/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0)) )),
% 1.28/0.51    inference(cnf_transformation,[],[f28])).
% 1.28/0.51  fof(f28,plain,(
% 1.28/0.51    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.28/0.51    inference(ennf_transformation,[],[f10])).
% 1.28/0.51  fof(f10,axiom,(
% 1.28/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 1.28/0.51  fof(f55,plain,(
% 1.28/0.51    ( ! [X0,X1] : (~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 1.28/0.51    inference(cnf_transformation,[],[f27])).
% 1.28/0.51  fof(f27,plain,(
% 1.28/0.51    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.28/0.51    inference(ennf_transformation,[],[f8])).
% 1.28/0.51  fof(f8,axiom,(
% 1.28/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).
% 1.28/0.51  fof(f110,plain,(
% 1.28/0.51    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.28/0.51    inference(subsumption_resolution,[],[f109,f48])).
% 1.28/0.51  fof(f109,plain,(
% 1.28/0.51    ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.28/0.51    inference(resolution,[],[f54,f44])).
% 1.28/0.51  fof(f54,plain,(
% 1.28/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 1.28/0.51    inference(cnf_transformation,[],[f26])).
% 1.28/0.51  fof(f26,plain,(
% 1.28/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.28/0.51    inference(flattening,[],[f25])).
% 1.28/0.51  fof(f25,plain,(
% 1.28/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.28/0.51    inference(ennf_transformation,[],[f9])).
% 1.28/0.51  fof(f9,axiom,(
% 1.28/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.28/0.51  fof(f349,plain,(
% 1.28/0.51    sK1 != k2_pre_topc(sK0,sK1)),
% 1.28/0.51    inference(forward_demodulation,[],[f348,f317])).
% 1.28/0.51  fof(f317,plain,(
% 1.28/0.51    sK1 = u1_struct_0(sK0)),
% 1.28/0.51    inference(duplicate_literal_removal,[],[f314])).
% 1.28/0.51  fof(f314,plain,(
% 1.28/0.51    sK1 = u1_struct_0(sK0) | sK1 = u1_struct_0(sK0)),
% 1.28/0.51    inference(backward_demodulation,[],[f246,f312])).
% 1.28/0.51  fof(f246,plain,(
% 1.28/0.51    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | sK1 = u1_struct_0(sK0)),
% 1.28/0.51    inference(resolution,[],[f231,f122])).
% 1.28/0.51  fof(f122,plain,(
% 1.28/0.51    ~v1_tops_1(sK1,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.28/0.51    inference(subsumption_resolution,[],[f121,f48])).
% 1.28/0.51  fof(f121,plain,(
% 1.28/0.51    ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~v1_tops_1(sK1,sK0)),
% 1.28/0.51    inference(resolution,[],[f60,f44])).
% 1.28/0.51  fof(f231,plain,(
% 1.28/0.51    v1_tops_1(sK1,sK0) | sK1 = u1_struct_0(sK0)),
% 1.28/0.51    inference(resolution,[],[f186,f135])).
% 1.28/0.51  fof(f135,plain,(
% 1.28/0.51    ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 1.28/0.51    inference(subsumption_resolution,[],[f134,f97])).
% 1.28/0.51  fof(f97,plain,(
% 1.28/0.51    v3_pre_topc(sK1,sK0)),
% 1.28/0.51    inference(subsumption_resolution,[],[f96,f47])).
% 1.28/0.51  fof(f96,plain,(
% 1.28/0.51    v3_pre_topc(sK1,sK0) | ~v1_tdlat_3(sK0)),
% 1.28/0.51    inference(subsumption_resolution,[],[f95,f48])).
% 1.28/0.51  fof(f95,plain,(
% 1.28/0.51    ~l1_pre_topc(sK0) | v3_pre_topc(sK1,sK0) | ~v1_tdlat_3(sK0)),
% 1.28/0.51    inference(resolution,[],[f84,f44])).
% 1.28/0.51  fof(f134,plain,(
% 1.28/0.51    ~v3_pre_topc(sK1,sK0) | ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 1.28/0.51    inference(subsumption_resolution,[],[f133,f45])).
% 1.28/0.51  fof(f45,plain,(
% 1.28/0.51    ~v2_struct_0(sK0)),
% 1.28/0.51    inference(cnf_transformation,[],[f22])).
% 1.28/0.51  fof(f133,plain,(
% 1.28/0.51    v2_struct_0(sK0) | ~v3_pre_topc(sK1,sK0) | ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 1.28/0.51    inference(subsumption_resolution,[],[f132,f48])).
% 1.28/0.51  fof(f132,plain,(
% 1.28/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_pre_topc(sK1,sK0) | ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 1.28/0.51    inference(subsumption_resolution,[],[f131,f46])).
% 1.28/0.51  fof(f46,plain,(
% 1.28/0.51    v2_pre_topc(sK0)),
% 1.28/0.51    inference(cnf_transformation,[],[f22])).
% 1.28/0.51  fof(f131,plain,(
% 1.28/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_pre_topc(sK1,sK0) | ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 1.28/0.51    inference(resolution,[],[f64,f44])).
% 1.28/0.51  fof(f64,plain,(
% 1.28/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v3_pre_topc(X1,X0) | ~v3_tex_2(X1,X0) | v1_tops_1(X1,X0)) )),
% 1.28/0.51    inference(cnf_transformation,[],[f34])).
% 1.28/0.51  fof(f34,plain,(
% 1.28/0.51    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.28/0.51    inference(flattening,[],[f33])).
% 1.28/0.51  fof(f33,plain,(
% 1.28/0.51    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.28/0.51    inference(ennf_transformation,[],[f17])).
% 1.28/0.51  fof(f17,axiom,(
% 1.28/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).
% 1.28/0.51  fof(f186,plain,(
% 1.28/0.51    v3_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK0)),
% 1.28/0.51    inference(resolution,[],[f90,f42])).
% 1.28/0.51  fof(f42,plain,(
% 1.28/0.51    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 1.28/0.51    inference(cnf_transformation,[],[f22])).
% 1.28/0.51  fof(f90,plain,(
% 1.28/0.51    v1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 1.28/0.51    inference(resolution,[],[f71,f44])).
% 1.28/0.51  fof(f71,plain,(
% 1.28/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.28/0.51    inference(cnf_transformation,[],[f40])).
% 1.28/0.51  fof(f40,plain,(
% 1.28/0.51    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.51    inference(ennf_transformation,[],[f14])).
% 1.28/0.51  fof(f14,axiom,(
% 1.28/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 1.28/0.51  fof(f348,plain,(
% 1.28/0.51    u1_struct_0(sK0) != k2_pre_topc(sK0,u1_struct_0(sK0))),
% 1.28/0.51    inference(subsumption_resolution,[],[f333,f345])).
% 1.28/0.51  fof(f345,plain,(
% 1.28/0.51    ~v1_tops_1(sK1,sK0)),
% 1.28/0.51    inference(subsumption_resolution,[],[f141,f344])).
% 1.28/0.51  fof(f344,plain,(
% 1.28/0.51    ~v3_tex_2(sK1,sK0)),
% 1.28/0.51    inference(subsumption_resolution,[],[f319,f81])).
% 1.28/0.51  fof(f81,plain,(
% 1.28/0.51    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 1.28/0.51    inference(backward_demodulation,[],[f49,f50])).
% 1.28/0.51  fof(f49,plain,(
% 1.28/0.51    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 1.28/0.51    inference(cnf_transformation,[],[f6])).
% 1.28/0.51  fof(f6,axiom,(
% 1.28/0.51    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).
% 1.28/0.51  fof(f319,plain,(
% 1.28/0.51    v1_subset_1(sK1,sK1) | ~v3_tex_2(sK1,sK0)),
% 1.28/0.51    inference(backward_demodulation,[],[f43,f317])).
% 1.28/0.51  fof(f43,plain,(
% 1.28/0.51    ~v3_tex_2(sK1,sK0) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.28/0.51    inference(cnf_transformation,[],[f22])).
% 1.28/0.51  fof(f141,plain,(
% 1.28/0.51    ~v1_tops_1(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 1.28/0.51    inference(subsumption_resolution,[],[f140,f107])).
% 1.28/0.51  fof(f107,plain,(
% 1.28/0.51    v2_tex_2(sK1,sK0)),
% 1.28/0.51    inference(subsumption_resolution,[],[f106,f45])).
% 1.28/0.51  fof(f106,plain,(
% 1.28/0.51    v2_struct_0(sK0) | v2_tex_2(sK1,sK0)),
% 1.28/0.51    inference(subsumption_resolution,[],[f105,f48])).
% 1.28/0.51  fof(f105,plain,(
% 1.28/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(sK1,sK0)),
% 1.28/0.51    inference(subsumption_resolution,[],[f104,f47])).
% 1.28/0.51  fof(f104,plain,(
% 1.28/0.51    ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(sK1,sK0)),
% 1.28/0.51    inference(resolution,[],[f83,f44])).
% 1.28/0.51  fof(f83,plain,(
% 1.28/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_tex_2(X1,X0)) )),
% 1.28/0.51    inference(subsumption_resolution,[],[f63,f52])).
% 1.28/0.51  fof(f63,plain,(
% 1.28/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 1.28/0.51    inference(cnf_transformation,[],[f32])).
% 1.28/0.51  fof(f32,plain,(
% 1.28/0.51    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.28/0.51    inference(flattening,[],[f31])).
% 1.28/0.51  fof(f31,plain,(
% 1.28/0.51    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.28/0.51    inference(ennf_transformation,[],[f16])).
% 1.28/0.51  fof(f16,axiom,(
% 1.28/0.51    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 1.28/0.51  fof(f140,plain,(
% 1.28/0.51    ~v1_tops_1(sK1,sK0) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 1.28/0.51    inference(subsumption_resolution,[],[f139,f45])).
% 1.28/0.51  fof(f139,plain,(
% 1.28/0.51    v2_struct_0(sK0) | ~v1_tops_1(sK1,sK0) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 1.28/0.51    inference(subsumption_resolution,[],[f138,f48])).
% 1.28/0.51  fof(f138,plain,(
% 1.28/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_tops_1(sK1,sK0) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 1.28/0.51    inference(subsumption_resolution,[],[f137,f46])).
% 1.28/0.51  fof(f137,plain,(
% 1.28/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_tops_1(sK1,sK0) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 1.28/0.51    inference(resolution,[],[f65,f44])).
% 1.28/0.51  fof(f65,plain,(
% 1.28/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v1_tops_1(X1,X0) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0)) )),
% 1.28/0.51    inference(cnf_transformation,[],[f36])).
% 1.28/0.51  fof(f36,plain,(
% 1.28/0.51    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.28/0.51    inference(flattening,[],[f35])).
% 1.28/0.51  fof(f35,plain,(
% 1.28/0.51    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.28/0.51    inference(ennf_transformation,[],[f18])).
% 1.28/0.51  fof(f18,axiom,(
% 1.28/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 1.28/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).
% 1.28/0.51  fof(f333,plain,(
% 1.28/0.51    v1_tops_1(sK1,sK0) | u1_struct_0(sK0) != k2_pre_topc(sK0,u1_struct_0(sK0))),
% 1.28/0.51    inference(backward_demodulation,[],[f193,f317])).
% 1.28/0.51  fof(f193,plain,(
% 1.28/0.51    u1_struct_0(sK0) != k2_pre_topc(sK0,u1_struct_0(sK0)) | v1_tops_1(u1_struct_0(sK0),sK0)),
% 1.28/0.51    inference(forward_demodulation,[],[f192,f165])).
% 1.28/0.51  fof(f192,plain,(
% 1.28/0.51    k2_struct_0(sK0) != k2_pre_topc(sK0,u1_struct_0(sK0)) | v1_tops_1(u1_struct_0(sK0),sK0)),
% 1.28/0.51    inference(resolution,[],[f111,f48])).
% 1.28/0.51  fof(f111,plain,(
% 1.28/0.51    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) != k2_pre_topc(X0,u1_struct_0(X0)) | v1_tops_1(u1_struct_0(X0),X0)) )),
% 1.28/0.51    inference(resolution,[],[f57,f82])).
% 1.28/0.51  fof(f57,plain,(
% 1.28/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0)) )),
% 1.28/0.51    inference(cnf_transformation,[],[f28])).
% 1.28/0.51  % SZS output end Proof for theBenchmark
% 1.28/0.51  % (31893)------------------------------
% 1.28/0.51  % (31893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.51  % (31893)Termination reason: Refutation
% 1.28/0.51  
% 1.28/0.51  % (31893)Memory used [KB]: 1918
% 1.28/0.51  % (31893)Time elapsed: 0.081 s
% 1.28/0.51  % (31893)------------------------------
% 1.28/0.51  % (31893)------------------------------
% 1.28/0.51  % (31886)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.28/0.51  % (31875)Success in time 0.15 s
%------------------------------------------------------------------------------
