%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:35 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 831 expanded)
%              Number of leaves         :    9 ( 156 expanded)
%              Depth                    :   23
%              Number of atoms          :  202 (3422 expanded)
%              Number of equality atoms :   23 ( 525 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f277,plain,(
    $false ),
    inference(subsumption_resolution,[],[f276,f143])).

fof(f143,plain,(
    ~ v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f71,f139])).

fof(f139,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f138,f71])).

fof(f138,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK0)
    | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f61,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f61,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f55,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( ( v1_tex_2(X1,X0)
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
               => v1_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).

fof(f55,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f24,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

% (17103)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f24,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f70,f67])).

fof(f67,plain,(
    u1_struct_0(sK2) = sK3(sK0,sK2) ),
    inference(subsumption_resolution,[],[f66,f27])).

fof(f27,plain,(
    ~ v1_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,
    ( u1_struct_0(sK2) = sK3(sK0,sK2)
    | v1_tex_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f58,f29])).

fof(f58,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK2) = sK3(sK0,sK2)
    | v1_tex_2(sK2,sK0) ),
    inference(resolution,[],[f24,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

% (17106)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f70,plain,(
    ~ v1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f69,f27])).

fof(f69,plain,
    ( ~ v1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | v1_tex_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f59,f29])).

fof(f59,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | v1_tex_2(sK2,sK0) ),
    inference(resolution,[],[f24,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f276,plain,(
    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f275,f255])).

fof(f255,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(global_subsumption,[],[f173,f253])).

fof(f253,plain,(
    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(resolution,[],[f245,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f245,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f244,f139])).

fof(f244,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f239,f82])).

fof(f82,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f76,f29])).

fof(f76,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f28,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f28,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f239,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f234,f39])).

fof(f234,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(subsumption_resolution,[],[f225,f60])).

fof(f60,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f54,f29])).

fof(f54,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f24,f40])).

fof(f225,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_pre_topc(sK2,sK1) ),
    inference(resolution,[],[f152,f157])).

fof(f157,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)))
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f155,f82])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)))
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,sK1) ) ),
    inference(superposition,[],[f37,f140])).

fof(f140,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)) ),
    inference(backward_demodulation,[],[f25,f139])).

fof(f25,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f152,plain,(
    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))) ),
    inference(backward_demodulation,[],[f112,f140])).

fof(f112,plain,(
    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(forward_demodulation,[],[f111,f25])).

fof(f111,plain,(
    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f109,f60])).

fof(f109,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f72,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f72,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f60,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f173,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(resolution,[],[f170,f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f170,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f83,f44])).

fof(f83,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f77,f29])).

fof(f77,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f28,f39])).

fof(f275,plain,(
    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f256,f98])).

fof(f98,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f92,f29])).

fof(f92,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f53,f39])).

fof(f53,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f29,f41])).

fof(f256,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f75,f255])).

fof(f75,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f74,f29])).

fof(f74,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f73,f28])).

fof(f73,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f26,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f26,plain,(
    v1_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:25:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (17091)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.36/0.54  % (17090)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.36/0.54  % (17091)Refutation not found, incomplete strategy% (17091)------------------------------
% 1.36/0.54  % (17091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (17085)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.36/0.55  % (17088)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.36/0.56  % (17099)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.36/0.56  % (17091)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (17091)Memory used [KB]: 10746
% 1.36/0.56  % (17091)Time elapsed: 0.121 s
% 1.36/0.56  % (17091)------------------------------
% 1.36/0.56  % (17091)------------------------------
% 1.36/0.56  % (17108)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.36/0.56  % (17085)Refutation not found, incomplete strategy% (17085)------------------------------
% 1.36/0.56  % (17085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (17085)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (17085)Memory used [KB]: 10618
% 1.36/0.56  % (17085)Time elapsed: 0.131 s
% 1.36/0.56  % (17085)------------------------------
% 1.36/0.56  % (17085)------------------------------
% 1.36/0.56  % (17105)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.55/0.56  % (17090)Refutation found. Thanks to Tanya!
% 1.55/0.56  % SZS status Theorem for theBenchmark
% 1.55/0.56  % SZS output start Proof for theBenchmark
% 1.55/0.56  fof(f277,plain,(
% 1.55/0.56    $false),
% 1.55/0.56    inference(subsumption_resolution,[],[f276,f143])).
% 1.55/0.56  fof(f143,plain,(
% 1.55/0.56    ~v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.55/0.56    inference(backward_demodulation,[],[f71,f139])).
% 1.55/0.56  fof(f139,plain,(
% 1.55/0.56    u1_struct_0(sK2) = u1_struct_0(sK0)),
% 1.55/0.56    inference(subsumption_resolution,[],[f138,f71])).
% 1.55/0.56  fof(f138,plain,(
% 1.55/0.56    u1_struct_0(sK2) = u1_struct_0(sK0) | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))),
% 1.55/0.56    inference(resolution,[],[f61,f34])).
% 1.55/0.56  fof(f34,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f18])).
% 1.55/0.56  fof(f18,plain,(
% 1.55/0.56    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.56    inference(ennf_transformation,[],[f11])).
% 1.55/0.56  fof(f11,axiom,(
% 1.55/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 1.55/0.56  fof(f61,plain,(
% 1.55/0.56    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.55/0.56    inference(subsumption_resolution,[],[f55,f29])).
% 1.55/0.56  fof(f29,plain,(
% 1.55/0.56    l1_pre_topc(sK0)),
% 1.55/0.56    inference(cnf_transformation,[],[f15])).
% 1.55/0.56  fof(f15,plain,(
% 1.55/0.56    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 1.55/0.56    inference(flattening,[],[f14])).
% 1.55/0.56  fof(f14,plain,(
% 1.55/0.56    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X2,X0) & (v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f13])).
% 1.55/0.56  fof(f13,negated_conjecture,(
% 1.55/0.56    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 1.55/0.56    inference(negated_conjecture,[],[f12])).
% 1.55/0.56  fof(f12,conjecture,(
% 1.55/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).
% 1.55/0.56  fof(f55,plain,(
% 1.55/0.56    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.55/0.56    inference(resolution,[],[f24,f39])).
% 1.55/0.56  fof(f39,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.55/0.56    inference(cnf_transformation,[],[f21])).
% 1.55/0.56  fof(f21,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f8])).
% 1.55/0.56  % (17103)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.55/0.56  fof(f8,axiom,(
% 1.55/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.55/0.56  fof(f24,plain,(
% 1.55/0.56    m1_pre_topc(sK2,sK0)),
% 1.55/0.56    inference(cnf_transformation,[],[f15])).
% 1.55/0.56  fof(f71,plain,(
% 1.55/0.56    ~v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK0))),
% 1.55/0.56    inference(forward_demodulation,[],[f70,f67])).
% 1.55/0.56  fof(f67,plain,(
% 1.55/0.56    u1_struct_0(sK2) = sK3(sK0,sK2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f66,f27])).
% 1.55/0.56  fof(f27,plain,(
% 1.55/0.56    ~v1_tex_2(sK2,sK0)),
% 1.55/0.56    inference(cnf_transformation,[],[f15])).
% 1.55/0.56  fof(f66,plain,(
% 1.55/0.56    u1_struct_0(sK2) = sK3(sK0,sK2) | v1_tex_2(sK2,sK0)),
% 1.55/0.56    inference(subsumption_resolution,[],[f58,f29])).
% 1.55/0.56  fof(f58,plain,(
% 1.55/0.56    ~l1_pre_topc(sK0) | u1_struct_0(sK2) = sK3(sK0,sK2) | v1_tex_2(sK2,sK0)),
% 1.55/0.56    inference(resolution,[],[f24,f32])).
% 1.55/0.56  fof(f32,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | u1_struct_0(X1) = sK3(X0,X1) | v1_tex_2(X1,X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f17])).
% 1.55/0.56  fof(f17,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.55/0.56    inference(flattening,[],[f16])).
% 1.55/0.56  fof(f16,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f10])).
% 1.55/0.56  % (17106)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.55/0.56  fof(f10,axiom,(
% 1.55/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 1.55/0.56  fof(f70,plain,(
% 1.55/0.56    ~v1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))),
% 1.55/0.56    inference(subsumption_resolution,[],[f69,f27])).
% 1.55/0.56  fof(f69,plain,(
% 1.55/0.56    ~v1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0)) | v1_tex_2(sK2,sK0)),
% 1.55/0.56    inference(subsumption_resolution,[],[f59,f29])).
% 1.55/0.56  fof(f59,plain,(
% 1.55/0.56    ~l1_pre_topc(sK0) | ~v1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0)) | v1_tex_2(sK2,sK0)),
% 1.55/0.56    inference(resolution,[],[f24,f33])).
% 1.55/0.56  fof(f33,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f17])).
% 1.55/0.56  fof(f276,plain,(
% 1.55/0.56    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.55/0.56    inference(forward_demodulation,[],[f275,f255])).
% 1.55/0.56  fof(f255,plain,(
% 1.55/0.56    u1_struct_0(sK1) = u1_struct_0(sK0)),
% 1.55/0.56    inference(global_subsumption,[],[f173,f253])).
% 1.55/0.56  fof(f253,plain,(
% 1.55/0.56    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.55/0.56    inference(resolution,[],[f245,f44])).
% 1.55/0.56  fof(f44,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f4])).
% 1.55/0.56  fof(f4,axiom,(
% 1.55/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.55/0.56  fof(f245,plain,(
% 1.55/0.56    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.55/0.56    inference(forward_demodulation,[],[f244,f139])).
% 1.55/0.56  fof(f244,plain,(
% 1.55/0.56    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.55/0.56    inference(subsumption_resolution,[],[f239,f82])).
% 1.55/0.56  fof(f82,plain,(
% 1.55/0.56    l1_pre_topc(sK1)),
% 1.55/0.56    inference(subsumption_resolution,[],[f76,f29])).
% 1.55/0.56  fof(f76,plain,(
% 1.55/0.56    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 1.55/0.56    inference(resolution,[],[f28,f40])).
% 1.55/0.56  fof(f40,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f22])).
% 1.55/0.56  fof(f22,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f5])).
% 1.55/0.56  fof(f5,axiom,(
% 1.55/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.55/0.56  fof(f28,plain,(
% 1.55/0.56    m1_pre_topc(sK1,sK0)),
% 1.55/0.56    inference(cnf_transformation,[],[f15])).
% 1.55/0.56  fof(f239,plain,(
% 1.55/0.56    ~l1_pre_topc(sK1) | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.55/0.56    inference(resolution,[],[f234,f39])).
% 1.55/0.56  fof(f234,plain,(
% 1.55/0.56    m1_pre_topc(sK2,sK1)),
% 1.55/0.56    inference(subsumption_resolution,[],[f225,f60])).
% 1.55/0.56  fof(f60,plain,(
% 1.55/0.56    l1_pre_topc(sK2)),
% 1.55/0.56    inference(subsumption_resolution,[],[f54,f29])).
% 1.55/0.56  fof(f54,plain,(
% 1.55/0.56    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 1.55/0.56    inference(resolution,[],[f24,f40])).
% 1.55/0.56  fof(f225,plain,(
% 1.55/0.56    ~l1_pre_topc(sK2) | m1_pre_topc(sK2,sK1)),
% 1.55/0.56    inference(resolution,[],[f152,f157])).
% 1.55/0.56  fof(f157,plain,(
% 1.55/0.56    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))) | ~l1_pre_topc(X0) | m1_pre_topc(X0,sK1)) )),
% 1.55/0.56    inference(subsumption_resolution,[],[f155,f82])).
% 1.55/0.56  fof(f155,plain,(
% 1.55/0.56    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,sK1)) )),
% 1.55/0.56    inference(superposition,[],[f37,f140])).
% 1.55/0.56  fof(f140,plain,(
% 1.55/0.56    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2))),
% 1.55/0.56    inference(backward_demodulation,[],[f25,f139])).
% 1.55/0.56  fof(f25,plain,(
% 1.55/0.56    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 1.55/0.56    inference(cnf_transformation,[],[f15])).
% 1.55/0.56  fof(f37,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f20])).
% 1.55/0.56  fof(f20,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f7])).
% 1.55/0.56  fof(f7,axiom,(
% 1.55/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.55/0.56  fof(f152,plain,(
% 1.55/0.56    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK2)))),
% 1.55/0.56    inference(backward_demodulation,[],[f112,f140])).
% 1.55/0.56  fof(f112,plain,(
% 1.55/0.56    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.55/0.56    inference(forward_demodulation,[],[f111,f25])).
% 1.55/0.56  fof(f111,plain,(
% 1.55/0.56    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 1.55/0.56    inference(subsumption_resolution,[],[f109,f60])).
% 1.55/0.56  fof(f109,plain,(
% 1.55/0.56    ~l1_pre_topc(sK2) | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 1.55/0.56    inference(duplicate_literal_removal,[],[f105])).
% 1.55/0.56  fof(f105,plain,(
% 1.55/0.56    ~l1_pre_topc(sK2) | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2)),
% 1.55/0.56    inference(resolution,[],[f72,f38])).
% 1.55/0.56  fof(f38,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f20])).
% 1.55/0.56  fof(f72,plain,(
% 1.55/0.56    m1_pre_topc(sK2,sK2)),
% 1.55/0.56    inference(resolution,[],[f60,f41])).
% 1.55/0.56  fof(f41,plain,(
% 1.55/0.56    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f23])).
% 1.55/0.56  fof(f23,plain,(
% 1.55/0.56    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f9])).
% 1.55/0.56  fof(f9,axiom,(
% 1.55/0.56    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.55/0.56  fof(f173,plain,(
% 1.55/0.56    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | u1_struct_0(sK1) = u1_struct_0(sK0)),
% 1.55/0.56    inference(resolution,[],[f170,f48])).
% 1.55/0.56  fof(f48,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.55/0.56    inference(cnf_transformation,[],[f1])).
% 1.55/0.56  fof(f1,axiom,(
% 1.55/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.55/0.56  fof(f170,plain,(
% 1.55/0.56    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.55/0.56    inference(resolution,[],[f83,f44])).
% 1.55/0.56  fof(f83,plain,(
% 1.55/0.56    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.55/0.56    inference(subsumption_resolution,[],[f77,f29])).
% 1.55/0.56  fof(f77,plain,(
% 1.55/0.56    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.55/0.56    inference(resolution,[],[f28,f39])).
% 1.55/0.56  fof(f275,plain,(
% 1.55/0.56    v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.55/0.56    inference(subsumption_resolution,[],[f256,f98])).
% 1.55/0.56  fof(f98,plain,(
% 1.55/0.56    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.55/0.56    inference(subsumption_resolution,[],[f92,f29])).
% 1.55/0.56  fof(f92,plain,(
% 1.55/0.56    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.55/0.56    inference(resolution,[],[f53,f39])).
% 1.55/0.56  fof(f53,plain,(
% 1.55/0.56    m1_pre_topc(sK0,sK0)),
% 1.55/0.56    inference(resolution,[],[f29,f41])).
% 1.55/0.56  fof(f256,plain,(
% 1.55/0.56    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.55/0.56    inference(backward_demodulation,[],[f75,f255])).
% 1.55/0.56  fof(f75,plain,(
% 1.55/0.56    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.55/0.56    inference(subsumption_resolution,[],[f74,f29])).
% 1.55/0.56  fof(f74,plain,(
% 1.55/0.56    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 1.55/0.56    inference(subsumption_resolution,[],[f73,f28])).
% 1.55/0.56  fof(f73,plain,(
% 1.55/0.56    ~m1_pre_topc(sK1,sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_subset_1(u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 1.55/0.56    inference(resolution,[],[f26,f49])).
% 1.55/0.56  fof(f49,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 1.55/0.56    inference(equality_resolution,[],[f30])).
% 1.55/0.56  fof(f30,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f17])).
% 1.55/0.56  fof(f26,plain,(
% 1.55/0.56    v1_tex_2(sK1,sK0)),
% 1.55/0.56    inference(cnf_transformation,[],[f15])).
% 1.55/0.56  % SZS output end Proof for theBenchmark
% 1.55/0.56  % (17090)------------------------------
% 1.55/0.56  % (17090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (17090)Termination reason: Refutation
% 1.55/0.56  
% 1.55/0.56  % (17090)Memory used [KB]: 6268
% 1.55/0.56  % (17090)Time elapsed: 0.136 s
% 1.55/0.56  % (17090)------------------------------
% 1.55/0.56  % (17090)------------------------------
% 1.55/0.57  % (17084)Success in time 0.2 s
%------------------------------------------------------------------------------
