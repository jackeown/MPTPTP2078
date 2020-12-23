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
% DateTime   : Thu Dec  3 13:20:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 490 expanded)
%              Number of leaves         :   16 ( 100 expanded)
%              Depth                    :   21
%              Number of atoms          :  412 (1777 expanded)
%              Number of equality atoms :   26 ( 232 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (13651)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (13656)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (13642)Refutation not found, incomplete strategy% (13642)------------------------------
% (13642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13642)Termination reason: Refutation not found, incomplete strategy

% (13642)Memory used [KB]: 6140
% (13642)Time elapsed: 0.111 s
% (13642)------------------------------
% (13642)------------------------------
% (13655)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (13653)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% (13662)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (13647)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% (13648)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f263,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f174,f180,f262])).

fof(f262,plain,(
    ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f260,f251])).

fof(f251,plain,
    ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f250,f194])).

fof(f194,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK1)
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f193,f105])).

fof(f105,plain,(
    u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f104,f45])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tex_2)).

fof(f104,plain,
    ( u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f51,f43])).

fof(f43,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tdlat_3)).

fof(f193,plain,
    ( u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f192,f44])).

fof(f44,plain,(
    ~ v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f192,plain,
    ( u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | v2_tdlat_3(sK1)
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f188,f41])).

fof(f41,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f188,plain,
    ( u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK1)
    | v2_tdlat_3(sK1)
    | ~ spl2_5 ),
    inference(superposition,[],[f50,f169])).

fof(f169,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl2_5
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f50,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f250,plain,
    ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl2_5 ),
    inference(resolution,[],[f249,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f249,plain,
    ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f248,f45])).

fof(f248,plain,
    ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f246,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f246,plain,
    ( ~ r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0))
    | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f244,f47])).

fof(f47,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f244,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X2,u1_pre_topc(sK0))
        | r1_tarski(X2,u1_pre_topc(sK1)) )
    | ~ spl2_5 ),
    inference(duplicate_literal_removal,[],[f243])).

fof(f243,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X2,u1_pre_topc(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r1_tarski(X2,u1_pre_topc(sK1)) )
    | ~ spl2_5 ),
    inference(resolution,[],[f241,f183])).

fof(f183,plain,
    ( ! [X0] :
        ( ~ v1_tops_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r1_tarski(X0,u1_pre_topc(sK1)) )
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f149,f169])).

fof(f149,plain,(
    ! [X0] :
      ( ~ v1_tops_2(X0,sK1)
      | r1_tarski(X0,u1_pre_topc(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ) ),
    inference(resolution,[],[f57,f41])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(f241,plain,
    ( ! [X0] :
        ( v1_tops_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,u1_pre_topc(sK0)) )
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f239,f169])).

fof(f239,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
      | v1_tops_2(X0,sK1)
      | ~ r1_tarski(X0,u1_pre_topc(sK0)) ) ),
    inference(resolution,[],[f221,f137])).

fof(f137,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f136,f72])).

fof(f72,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f46,f41])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f136,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | m1_pre_topc(X1,sK0) ) ),
    inference(resolution,[],[f133,f109])).

fof(f109,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_pre_topc(X1,sK0) ) ),
    inference(resolution,[],[f59,f45])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f133,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_pre_topc(X0,sK1) ) ),
    inference(forward_demodulation,[],[f132,f42])).

fof(f42,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f132,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f130,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f54,f41])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f130,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_pre_topc(X0,sK1) ) ),
    inference(resolution,[],[f53,f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f221,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_tops_2(X1,X0)
      | ~ r1_tarski(X1,u1_pre_topc(sK0)) ) ),
    inference(subsumption_resolution,[],[f220,f208])).

fof(f208,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X2,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f55,f45])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

fof(f220,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_tops_2(X1,X0)
      | ~ r1_tarski(X1,u1_pre_topc(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f217,f148])).

fof(f148,plain,(
    ! [X1] :
      ( v1_tops_2(X1,sK0)
      | ~ r1_tarski(X1,u1_pre_topc(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f56,f45])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f217,plain,(
    ! [X2,X3] :
      ( ~ v1_tops_2(X3,sK0)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | v1_tops_2(X3,X2) ) ),
    inference(resolution,[],[f70,f45])).

fof(f70,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tops_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | v1_tops_2(X3,X2) ) ),
    inference(subsumption_resolution,[],[f67,f55])).

fof(f67,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tops_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | v1_tops_2(X3,X2) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | X1 != X3
      | v1_tops_2(X3,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v1_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).

fof(f260,plain,
    ( r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f259,f68])).

fof(f259,plain,
    ( ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1))
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | ~ spl2_5 ),
    inference(resolution,[],[f257,f198])).

fof(f198,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f191,f41])).

fof(f191,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK1)
    | ~ spl2_5 ),
    inference(superposition,[],[f47,f169])).

fof(f257,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X2,u1_pre_topc(sK1))
        | r1_tarski(X2,u1_pre_topc(sK0)) )
    | ~ spl2_5 ),
    inference(duplicate_literal_removal,[],[f256])).

fof(f256,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_pre_topc(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r1_tarski(X2,u1_pre_topc(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl2_5 ),
    inference(resolution,[],[f253,f150])).

fof(f150,plain,(
    ! [X1] :
      ( ~ v1_tops_2(X1,sK0)
      | r1_tarski(X1,u1_pre_topc(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f57,f45])).

fof(f253,plain,
    ( ! [X1] :
        ( v1_tops_2(X1,sK0)
        | ~ r1_tarski(X1,u1_pre_topc(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl2_5 ),
    inference(resolution,[],[f237,f73])).

fof(f73,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f46,f45])).

fof(f237,plain,
    ( ! [X2,X1] :
        ( ~ m1_pre_topc(X2,sK0)
        | v1_tops_2(X1,X2)
        | ~ r1_tarski(X1,u1_pre_topc(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
    | ~ spl2_5 ),
    inference(resolution,[],[f219,f140])).

fof(f140,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,sK1)
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f134,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_pre_topc(X0,sK1) ) ),
    inference(forward_demodulation,[],[f108,f42])).

fof(f108,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(X0,sK1) ) ),
    inference(resolution,[],[f59,f41])).

fof(f134,plain,(
    ! [X1] :
      ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f131,f77])).

fof(f77,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | l1_pre_topc(X1) ) ),
    inference(resolution,[],[f54,f45])).

fof(f131,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_pre_topc(X1,sK0) ) ),
    inference(resolution,[],[f53,f45])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | v1_tops_2(X1,X0)
        | ~ r1_tarski(X1,u1_pre_topc(sK1)) )
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f218,f209])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK1)
        | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f207,f169])).

fof(f207,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ) ),
    inference(resolution,[],[f55,f41])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | v1_tops_2(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X1,u1_pre_topc(sK1)) )
    | ~ spl2_5 ),
    inference(resolution,[],[f216,f182])).

fof(f182,plain,
    ( ! [X0] :
        ( v1_tops_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X0,u1_pre_topc(sK1)) )
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f147,f169])).

fof(f147,plain,(
    ! [X0] :
      ( v1_tops_2(X0,sK1)
      | ~ r1_tarski(X0,u1_pre_topc(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ) ),
    inference(resolution,[],[f56,f41])).

fof(f216,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_2(X1,sK1)
      | ~ m1_pre_topc(X0,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_tops_2(X1,X0) ) ),
    inference(resolution,[],[f70,f41])).

fof(f180,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl2_6 ),
    inference(subsumption_resolution,[],[f178,f173])).

fof(f173,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl2_6
  <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f178,plain,(
    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(resolution,[],[f176,f73])).

fof(f176,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f161,f140])).

fof(f161,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f159,f137])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f155,f45])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f71,f75])).

fof(f75,plain,(
    v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f74,f45])).

fof(f74,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK0) ),
    inference(resolution,[],[f48,f43])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f62,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f174,plain,
    ( spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f165,f171,f167])).

fof(f165,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(resolution,[],[f163,f66])).

fof(f163,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f162,f137])).

fof(f162,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f159,f73])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:49:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (13643)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.47  % (13644)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.48  % (13654)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.48  % (13637)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.48  % (13637)Refutation not found, incomplete strategy% (13637)------------------------------
% 0.21/0.48  % (13637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (13637)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (13637)Memory used [KB]: 10618
% 0.21/0.48  % (13637)Time elapsed: 0.071 s
% 0.21/0.48  % (13637)------------------------------
% 0.21/0.48  % (13637)------------------------------
% 0.21/0.48  % (13644)Refutation not found, incomplete strategy% (13644)------------------------------
% 0.21/0.48  % (13644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (13644)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (13644)Memory used [KB]: 1663
% 0.21/0.48  % (13644)Time elapsed: 0.071 s
% 0.21/0.48  % (13644)------------------------------
% 0.21/0.48  % (13644)------------------------------
% 0.21/0.50  % (13646)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (13652)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (13639)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (13658)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (13640)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (13650)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (13650)Refutation not found, incomplete strategy% (13650)------------------------------
% 0.21/0.52  % (13650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13650)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13650)Memory used [KB]: 6140
% 0.21/0.52  % (13650)Time elapsed: 0.094 s
% 0.21/0.52  % (13650)------------------------------
% 0.21/0.52  % (13650)------------------------------
% 0.21/0.53  % (13641)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (13642)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (13645)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (13661)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (13660)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (13638)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (13659)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (13657)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  % (13649)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (13659)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.55  % (13651)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.55  % (13656)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.55  % (13642)Refutation not found, incomplete strategy% (13642)------------------------------
% 0.21/0.55  % (13642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (13642)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (13642)Memory used [KB]: 6140
% 0.21/0.55  % (13642)Time elapsed: 0.111 s
% 0.21/0.55  % (13642)------------------------------
% 0.21/0.55  % (13642)------------------------------
% 0.21/0.55  % (13655)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.55  % (13653)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.55  % (13662)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.55  % (13647)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.56  % (13648)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.56  fof(f263,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f174,f180,f262])).
% 0.21/0.56  fof(f262,plain,(
% 0.21/0.56    ~spl2_5),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f261])).
% 0.21/0.56  fof(f261,plain,(
% 0.21/0.56    $false | ~spl2_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f260,f251])).
% 0.21/0.56  fof(f251,plain,(
% 0.21/0.56    ~r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | ~spl2_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f250,f194])).
% 0.21/0.56  fof(f194,plain,(
% 0.21/0.56    u1_pre_topc(sK0) != u1_pre_topc(sK1) | ~spl2_5),
% 0.21/0.56    inference(forward_demodulation,[],[f193,f105])).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))),
% 0.21/0.56    inference(subsumption_resolution,[],[f104,f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    l1_pre_topc(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (~v2_tdlat_3(X1) & v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.56    inference(flattening,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : ((~v2_tdlat_3(X1) & (v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,negated_conjecture,(
% 0.21/0.56    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tdlat_3(X1))))),
% 0.21/0.56    inference(negated_conjecture,[],[f16])).
% 0.21/0.56  fof(f16,conjecture,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v2_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tdlat_3(X1))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tex_2)).
% 0.21/0.56  fof(f104,plain,(
% 0.21/0.56    u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.56    inference(resolution,[],[f51,f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    v2_tdlat_3(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X0] : (~v2_tdlat_3(X0) | u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0] : ((v2_tdlat_3(X0) <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tdlat_3)).
% 0.21/0.56  fof(f193,plain,(
% 0.21/0.56    u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0)) | ~spl2_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f192,f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ~v2_tdlat_3(sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f192,plain,(
% 0.21/0.56    u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0)) | v2_tdlat_3(sK1) | ~spl2_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f188,f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    l1_pre_topc(sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f188,plain,(
% 0.21/0.56    u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0)) | ~l1_pre_topc(sK1) | v2_tdlat_3(sK1) | ~spl2_5),
% 0.21/0.56    inference(superposition,[],[f50,f169])).
% 0.21/0.56  fof(f169,plain,(
% 0.21/0.56    u1_struct_0(sK0) = u1_struct_0(sK1) | ~spl2_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f167])).
% 0.21/0.56  fof(f167,plain,(
% 0.21/0.56    spl2_5 <=> u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    ( ! [X0] : (u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_tdlat_3(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f250,plain,(
% 0.21/0.56    ~r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = u1_pre_topc(sK1) | ~spl2_5),
% 0.21/0.56    inference(resolution,[],[f249,f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.56  fof(f249,plain,(
% 0.21/0.56    r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | ~spl2_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f248,f45])).
% 0.21/0.56  fof(f248,plain,(
% 0.21/0.56    r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | ~l1_pre_topc(sK0) | ~spl2_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f246,f68])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.56    inference(equality_resolution,[],[f65])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f246,plain,(
% 0.21/0.56    ~r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK0)) | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | ~l1_pre_topc(sK0) | ~spl2_5),
% 0.21/0.56    inference(resolution,[],[f244,f47])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.56  fof(f244,plain,(
% 0.21/0.56    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X2,u1_pre_topc(sK0)) | r1_tarski(X2,u1_pre_topc(sK1))) ) | ~spl2_5),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f243])).
% 0.21/0.56  fof(f243,plain,(
% 0.21/0.56    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X2,u1_pre_topc(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(X2,u1_pre_topc(sK1))) ) | ~spl2_5),
% 0.21/0.56    inference(resolution,[],[f241,f183])).
% 0.21/0.56  fof(f183,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_tops_2(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(X0,u1_pre_topc(sK1))) ) | ~spl2_5),
% 0.21/0.56    inference(backward_demodulation,[],[f149,f169])).
% 0.21/0.56  fof(f149,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_tops_2(X0,sK1) | r1_tarski(X0,u1_pre_topc(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) )),
% 0.21/0.56    inference(resolution,[],[f57,f41])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).
% 0.21/0.56  fof(f241,plain,(
% 0.21/0.56    ( ! [X0] : (v1_tops_2(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,u1_pre_topc(sK0))) ) | ~spl2_5),
% 0.21/0.56    inference(forward_demodulation,[],[f239,f169])).
% 0.21/0.56  fof(f239,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | v1_tops_2(X0,sK1) | ~r1_tarski(X0,u1_pre_topc(sK0))) )),
% 0.21/0.56    inference(resolution,[],[f221,f137])).
% 0.21/0.56  fof(f137,plain,(
% 0.21/0.56    m1_pre_topc(sK1,sK0)),
% 0.21/0.56    inference(resolution,[],[f136,f72])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    m1_pre_topc(sK1,sK1)),
% 0.21/0.56    inference(resolution,[],[f46,f41])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.56  fof(f136,plain,(
% 0.21/0.56    ( ! [X1] : (~m1_pre_topc(X1,sK1) | m1_pre_topc(X1,sK0)) )),
% 0.21/0.56    inference(resolution,[],[f133,f109])).
% 0.21/0.56  fof(f109,plain,(
% 0.21/0.56    ( ! [X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X1,sK0)) )),
% 0.21/0.56    inference(resolution,[],[f59,f45])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.21/0.56  fof(f133,plain,(
% 0.21/0.56    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X0,sK1)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f132,f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f132,plain,(
% 0.21/0.56    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(X0,sK1)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f130,f76])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK1) | l1_pre_topc(X0)) )),
% 0.21/0.56    inference(resolution,[],[f54,f41])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.56  fof(f130,plain,(
% 0.21/0.56    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(X0,sK1)) )),
% 0.21/0.56    inference(resolution,[],[f53,f41])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.56  fof(f221,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(sK0))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f220,f208])).
% 0.21/0.56  fof(f208,plain,(
% 0.21/0.56    ( ! [X2,X3] : (~m1_pre_topc(X2,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 0.21/0.56    inference(resolution,[],[f55,f45])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).
% 0.21/0.56  fof(f220,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 0.21/0.56    inference(resolution,[],[f217,f148])).
% 0.21/0.56  fof(f148,plain,(
% 0.21/0.56    ( ! [X1] : (v1_tops_2(X1,sK0) | ~r1_tarski(X1,u1_pre_topc(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 0.21/0.56    inference(resolution,[],[f56,f45])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f31])).
% 0.21/0.56  fof(f217,plain,(
% 0.21/0.56    ( ! [X2,X3] : (~v1_tops_2(X3,sK0) | ~m1_pre_topc(X2,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | v1_tops_2(X3,X2)) )),
% 0.21/0.56    inference(resolution,[],[f70,f45])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X2,X0,X3] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~v1_tops_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | v1_tops_2(X3,X2)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f67,f55])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X2,X0,X3] : (~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X2,X0) | ~v1_tops_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | v1_tops_2(X3,X2)) )),
% 0.21/0.56    inference(equality_resolution,[],[f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X2,X0) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | X1 != X3 | v1_tops_2(X3,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(flattening,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v1_tops_2(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).
% 0.21/0.56  fof(f260,plain,(
% 0.21/0.56    r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | ~spl2_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f259,f68])).
% 0.21/0.56  fof(f259,plain,(
% 0.21/0.56    ~r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK1)) | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | ~spl2_5),
% 0.21/0.56    inference(resolution,[],[f257,f198])).
% 0.21/0.56  fof(f198,plain,(
% 0.21/0.56    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl2_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f191,f41])).
% 0.21/0.56  fof(f191,plain,(
% 0.21/0.56    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK1) | ~spl2_5),
% 0.21/0.56    inference(superposition,[],[f47,f169])).
% 0.21/0.56  fof(f257,plain,(
% 0.21/0.56    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X2,u1_pre_topc(sK1)) | r1_tarski(X2,u1_pre_topc(sK0))) ) | ~spl2_5),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f256])).
% 0.21/0.56  fof(f256,plain,(
% 0.21/0.56    ( ! [X2] : (~r1_tarski(X2,u1_pre_topc(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(X2,u1_pre_topc(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl2_5),
% 0.21/0.56    inference(resolution,[],[f253,f150])).
% 0.21/0.56  fof(f150,plain,(
% 0.21/0.56    ( ! [X1] : (~v1_tops_2(X1,sK0) | r1_tarski(X1,u1_pre_topc(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 0.21/0.56    inference(resolution,[],[f57,f45])).
% 0.21/0.56  fof(f253,plain,(
% 0.21/0.56    ( ! [X1] : (v1_tops_2(X1,sK0) | ~r1_tarski(X1,u1_pre_topc(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl2_5),
% 0.21/0.56    inference(resolution,[],[f237,f73])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    m1_pre_topc(sK0,sK0)),
% 0.21/0.56    inference(resolution,[],[f46,f45])).
% 0.21/0.56  fof(f237,plain,(
% 0.21/0.56    ( ! [X2,X1] : (~m1_pre_topc(X2,sK0) | v1_tops_2(X1,X2) | ~r1_tarski(X1,u1_pre_topc(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) ) | ~spl2_5),
% 0.21/0.56    inference(resolution,[],[f219,f140])).
% 0.21/0.56  fof(f140,plain,(
% 0.21/0.56    ( ! [X0] : (m1_pre_topc(X0,sK1) | ~m1_pre_topc(X0,sK0)) )),
% 0.21/0.56    inference(resolution,[],[f134,f110])).
% 0.21/0.56  fof(f110,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X0,sK1)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f108,f42])).
% 0.21/0.56  fof(f108,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(X0,sK1)) )),
% 0.21/0.56    inference(resolution,[],[f59,f41])).
% 0.21/0.56  fof(f134,plain,(
% 0.21/0.56    ( ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X1,sK0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f131,f77])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X1] : (~m1_pre_topc(X1,sK0) | l1_pre_topc(X1)) )),
% 0.21/0.56    inference(resolution,[],[f54,f45])).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    ( ! [X1] : (~l1_pre_topc(X1) | m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(X1,sK0)) )),
% 0.21/0.56    inference(resolution,[],[f53,f45])).
% 0.21/0.56  fof(f219,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(sK1))) ) | ~spl2_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f218,f209])).
% 0.21/0.56  fof(f209,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK1) | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) ) | ~spl2_5),
% 0.21/0.56    inference(forward_demodulation,[],[f207,f169])).
% 0.21/0.56  fof(f207,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) )),
% 0.21/0.56    inference(resolution,[],[f55,f41])).
% 0.21/0.56  fof(f218,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X1,u1_pre_topc(sK1))) ) | ~spl2_5),
% 0.21/0.56    inference(resolution,[],[f216,f182])).
% 0.21/0.56  fof(f182,plain,(
% 0.21/0.56    ( ! [X0] : (v1_tops_2(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X0,u1_pre_topc(sK1))) ) | ~spl2_5),
% 0.21/0.56    inference(backward_demodulation,[],[f147,f169])).
% 0.21/0.56  fof(f147,plain,(
% 0.21/0.56    ( ! [X0] : (v1_tops_2(X0,sK1) | ~r1_tarski(X0,u1_pre_topc(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) )),
% 0.21/0.56    inference(resolution,[],[f56,f41])).
% 0.21/0.56  fof(f216,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_tops_2(X1,sK1) | ~m1_pre_topc(X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_2(X1,X0)) )),
% 0.21/0.56    inference(resolution,[],[f70,f41])).
% 0.21/0.56  fof(f180,plain,(
% 0.21/0.56    spl2_6),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f179])).
% 0.21/0.56  fof(f179,plain,(
% 0.21/0.56    $false | spl2_6),
% 0.21/0.56    inference(subsumption_resolution,[],[f178,f173])).
% 0.21/0.56  fof(f173,plain,(
% 0.21/0.56    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | spl2_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f171])).
% 0.21/0.56  fof(f171,plain,(
% 0.21/0.56    spl2_6 <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.56  fof(f178,plain,(
% 0.21/0.56    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.56    inference(resolution,[],[f176,f73])).
% 0.21/0.56  fof(f176,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1))) )),
% 0.21/0.56    inference(resolution,[],[f161,f140])).
% 0.21/0.56  fof(f161,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK1) | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1))) )),
% 0.21/0.56    inference(resolution,[],[f159,f137])).
% 0.21/0.56  fof(f159,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f155,f45])).
% 0.21/0.56  fof(f155,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.21/0.56    inference(resolution,[],[f71,f75])).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    v2_pre_topc(sK0)),
% 0.21/0.56    inference(subsumption_resolution,[],[f74,f45])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ~l1_pre_topc(sK0) | v2_pre_topc(sK0)),
% 0.21/0.56    inference(resolution,[],[f48,f43])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ( ! [X0] : (~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(flattening,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f62,f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.56    inference(flattening,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.56    inference(flattening,[],[f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.21/0.56  fof(f174,plain,(
% 0.21/0.56    spl2_5 | ~spl2_6),
% 0.21/0.56    inference(avatar_split_clause,[],[f165,f171,f167])).
% 0.21/0.56  fof(f165,plain,(
% 0.21/0.56    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.21/0.56    inference(resolution,[],[f163,f66])).
% 0.21/0.56  fof(f163,plain,(
% 0.21/0.56    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.56    inference(resolution,[],[f162,f137])).
% 0.21/0.56  fof(f162,plain,(
% 0.21/0.56    ( ! [X1] : (~m1_pre_topc(X1,sK0) | r1_tarski(u1_struct_0(X1),u1_struct_0(sK0))) )),
% 0.21/0.56    inference(resolution,[],[f159,f73])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (13659)------------------------------
% 0.21/0.56  % (13659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (13659)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (13659)Memory used [KB]: 10746
% 0.21/0.56  % (13659)Time elapsed: 0.144 s
% 0.21/0.56  % (13659)------------------------------
% 0.21/0.56  % (13659)------------------------------
% 0.21/0.56  % (13636)Success in time 0.202 s
%------------------------------------------------------------------------------
