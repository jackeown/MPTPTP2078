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
% DateTime   : Thu Dec  3 13:21:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 290 expanded)
%              Number of leaves         :    5 (  50 expanded)
%              Depth                    :   21
%              Number of atoms          :  251 (1425 expanded)
%              Number of equality atoms :   12 (  21 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f135,plain,(
    $false ),
    inference(subsumption_resolution,[],[f134,f18])).

fof(f18,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f134,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f133,f84])).

fof(f84,plain,(
    m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f83,f69])).

fof(f69,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f68,f17])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f68,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f67,f22])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f66,f20])).

fof(f20,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f65,f19])).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f18,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
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
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f83,plain,
    ( v1_xboole_0(sK1)
    | m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f82,f22])).

fof(f82,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f76,f19])).

fof(f76,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(resolution,[],[f17,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

% (21703)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f133,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f132,f22])).

fof(f132,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f129,f19])).

fof(f129,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f124,f17])).

fof(f124,plain,(
    ! [X10] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X10)))
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(sK2(sK0,sK1),X10)
      | v2_tex_2(sK1,X10) ) ),
    inference(subsumption_resolution,[],[f123,f108])).

fof(f108,plain,(
    v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f107,f22])).

fof(f107,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f106,f21])).

fof(f21,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f106,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f105,f20])).

fof(f105,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f104,f19])).

fof(f104,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(resolution,[],[f84,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).

fof(f123,plain,(
    ! [X10] :
      ( v2_tex_2(sK1,X10)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(sK2(sK0,sK1),X10)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ v1_tdlat_3(sK2(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f119,f81])).

fof(f81,plain,(
    ~ v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f80,f69])).

fof(f80,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f79,f22])).

fof(f79,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f74,f19])).

fof(f74,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ v2_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f17,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f119,plain,(
    ! [X10] :
      ( v2_tex_2(sK1,X10)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(sK2(sK0,sK1))
      | ~ m1_pre_topc(sK2(sK0,sK1),X10)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ v1_tdlat_3(sK2(sK0,sK1)) ) ),
    inference(superposition,[],[f34,f87])).

fof(f87,plain,(
    sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f86,f69])).

fof(f86,plain,
    ( v1_xboole_0(sK1)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f85,f22])).

fof(f85,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f77,f19])).

fof(f77,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f17,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:53:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.46  % (21694)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (21702)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (21702)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f134,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f133,f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f83,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f68,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f67,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f66,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f65,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(resolution,[],[f18,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f82,f22])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f76,f19])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.21/0.48    inference(resolution,[],[f17,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK2(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  % (21703)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ~m1_pre_topc(sK2(sK0,sK1),sK0) | v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f132,f22])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2(sK0,sK1),sK0) | v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f129,f19])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2(sK0,sK1),sK0) | v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(resolution,[],[f124,f17])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ( ! [X10] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X10))) | v2_struct_0(X10) | ~l1_pre_topc(X10) | ~m1_pre_topc(sK2(sK0,sK1),X10) | v2_tex_2(sK1,X10)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f123,f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    v1_tdlat_3(sK2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f107,f22])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v1_tdlat_3(sK2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f106,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    v1_tdlat_3(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v1_tdlat_3(sK2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f105,f20])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v1_tdlat_3(sK2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f104,f19])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v1_tdlat_3(sK2(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f84,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_tdlat_3(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ( ! [X10] : (v2_tex_2(sK1,X10) | v2_struct_0(X10) | ~l1_pre_topc(X10) | ~m1_pre_topc(sK2(sK0,sK1),X10) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X10))) | ~v1_tdlat_3(sK2(sK0,sK1))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f119,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ~v2_struct_0(sK2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f80,f69])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | ~v2_struct_0(sK2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f79,f22])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~v2_struct_0(sK2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f74,f19])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~v2_struct_0(sK2(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f17,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_struct_0(sK2(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    ( ! [X10] : (v2_tex_2(sK1,X10) | v2_struct_0(X10) | ~l1_pre_topc(X10) | v2_struct_0(sK2(sK0,sK1)) | ~m1_pre_topc(sK2(sK0,sK1),X10) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X10))) | ~v1_tdlat_3(sK2(sK0,sK1))) )),
% 0.21/0.48    inference(superposition,[],[f34,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f86,f69])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f22])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f77,f19])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f17,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v1_tdlat_3(X1) | v2_tex_2(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (21702)------------------------------
% 0.21/0.48  % (21702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21702)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (21702)Memory used [KB]: 1663
% 0.21/0.48  % (21702)Time elapsed: 0.067 s
% 0.21/0.48  % (21702)------------------------------
% 0.21/0.48  % (21702)------------------------------
% 0.21/0.48  % (21701)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (21688)Success in time 0.124 s
%------------------------------------------------------------------------------
