%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:16 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  141 (4141 expanded)
%              Number of leaves         :   12 ( 717 expanded)
%              Depth                    :   40
%              Number of atoms          :  555 (26501 expanded)
%              Number of equality atoms :   53 ( 434 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (17506)Termination reason: Refutation not found, incomplete strategy
fof(f320,plain,(
    $false ),
    inference(subsumption_resolution,[],[f319,f108])).

fof(f108,plain,(
    ~ v1_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f107,f39])).

fof(f39,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

% (17506)Memory used [KB]: 1791
fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

% (17506)Time elapsed: 0.122 s
fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

% (17506)------------------------------
% (17506)------------------------------
fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( v1_subset_1(X1,u1_struct_0(X0))
                & v3_tex_2(X1,X0)
                & ( v4_pre_topc(X1,X0)
                  | v3_pre_topc(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( v1_subset_1(X1,u1_struct_0(X0))
              & v3_tex_2(X1,X0)
              & ( v4_pre_topc(X1,X0)
                | v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).

fof(f107,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f106,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f106,plain,
    ( ~ v1_tdlat_3(sK0)
    | v2_struct_0(sK0)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f105,f38])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f105,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f104,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f104,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f103,f42])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f103,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f40,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

fof(f40,plain,(
    v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f319,plain,(
    v1_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f318,f42])).

fof(f318,plain,
    ( ~ v2_pre_topc(sK0)
    | v1_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f315,f44])).

fof(f315,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v1_tdlat_3(sK0) ),
    inference(resolution,[],[f297,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(sK6(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X1,X0)
              & k1_tarski(X2) = X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X1,X0)
              & k1_tarski(X2) = X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k1_tarski(X2) = X1
                 => v3_pre_topc(X1,X0) ) ) )
       => v1_tdlat_3(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tdlat_3)).

fof(f297,plain,(
    v3_pre_topc(sK6(sK0),sK0) ),
    inference(backward_demodulation,[],[f228,f295])).

fof(f295,plain,(
    sK6(sK0) = sK9(sK0,sK1,sK6(sK0)) ),
    inference(forward_demodulation,[],[f294,f245])).

fof(f245,plain,(
    sK6(sK0) = k9_subset_1(sK1,sK1,sK9(sK0,sK1,sK6(sK0))) ),
    inference(resolution,[],[f192,f185])).

fof(f185,plain,(
    m1_subset_1(sK6(sK0),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f173,f108])).

fof(f173,plain,
    ( m1_subset_1(sK6(sK0),k1_zfmisc_1(sK1))
    | v1_tdlat_3(sK0) ),
    inference(backward_demodulation,[],[f91,f169])).

fof(f169,plain,(
    sK1 = u1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f168,f151])).

fof(f151,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f150,f44])).

fof(f150,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f148,f38])).

fof(f148,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f147,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f147,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f146,f43])).

fof(f43,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f146,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f145,f42])).

fof(f145,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f144,f38])).

fof(f144,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f141,f44])).

fof(f141,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(resolution,[],[f37,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
             => v4_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).

fof(f37,plain,
    ( v3_pre_topc(sK1,sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f168,plain,(
    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f167,f44])).

fof(f167,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f166,f38])).

fof(f166,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f164,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

% (17514)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f164,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f102,f158])).

fof(f158,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f157,f43])).

fof(f157,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f156,f42])).

fof(f156,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f155,f38])).

fof(f155,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f149,f44])).

fof(f149,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(resolution,[],[f147,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(X1,X0)
      | ~ v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f102,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f101,f41])).

fof(f101,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f100,f38])).

fof(f100,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f99,f44])).

fof(f99,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f94,f42])).

fof(f94,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f39,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

fof(f91,plain,
    ( m1_subset_1(sK6(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f88,f44])).

fof(f88,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK6(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tdlat_3(sK0) ),
    inference(resolution,[],[f42,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f192,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | k9_subset_1(sK1,sK1,sK9(sK0,sK1,X3)) = X3 ) ),
    inference(forward_demodulation,[],[f191,f169])).

fof(f191,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | k9_subset_1(u1_struct_0(sK0),sK1,sK9(sK0,sK1,X3)) = X3 ) ),
    inference(subsumption_resolution,[],[f179,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f179,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | ~ r1_tarski(X3,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,sK9(sK0,sK1,X3)) = X3 ) ),
    inference(backward_demodulation,[],[f138,f169])).

fof(f138,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X3,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,sK9(sK0,sK1,X3)) = X3 ) ),
    inference(subsumption_resolution,[],[f137,f44])).

fof(f137,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X3,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,sK9(sK0,sK1,X3)) = X3
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f128,f38])).

fof(f128,plain,(
    ! [X3] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X3,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,sK9(sK0,sK1,X3)) = X3
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f98,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | k9_subset_1(u1_struct_0(X0),X1,sK9(X0,X1,X2)) = X2
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(f98,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f97,f44])).

fof(f97,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f93,f38])).

fof(f93,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f39,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f294,plain,(
    sK9(sK0,sK1,sK6(sK0)) = k9_subset_1(sK1,sK1,sK9(sK0,sK1,sK6(sK0))) ),
    inference(backward_demodulation,[],[f285,f293])).

fof(f293,plain,(
    sK9(sK0,sK1,sK6(sK0)) = k2_pre_topc(sK0,sK9(sK0,sK1,sK6(sK0))) ),
    inference(subsumption_resolution,[],[f292,f226])).

fof(f226,plain,(
    m1_subset_1(sK9(sK0,sK1,sK6(sK0)),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f189,f196])).

fof(f196,plain,(
    r1_tarski(sK6(sK0),sK1) ),
    inference(resolution,[],[f185,f75])).

fof(f189,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1)
      | m1_subset_1(sK9(sK0,sK1,X1),k1_zfmisc_1(sK1)) ) ),
    inference(forward_demodulation,[],[f188,f169])).

fof(f188,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1)
      | m1_subset_1(sK9(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f177,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f177,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
      | ~ r1_tarski(X1,sK1)
      | m1_subset_1(sK9(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f134,f169])).

fof(f134,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X1,sK1)
      | m1_subset_1(sK9(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f133,f44])).

fof(f133,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X1,sK1)
      | m1_subset_1(sK9(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f126,f38])).

fof(f126,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X1,sK1)
      | m1_subset_1(sK9(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f98,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f292,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK6(sK0)),k1_zfmisc_1(sK1))
    | sK9(sK0,sK1,sK6(sK0)) = k2_pre_topc(sK0,sK9(sK0,sK1,sK6(sK0))) ),
    inference(forward_demodulation,[],[f291,f169])).

fof(f291,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK6(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK9(sK0,sK1,sK6(sK0)) = k2_pre_topc(sK0,sK9(sK0,sK1,sK6(sK0))) ),
    inference(subsumption_resolution,[],[f289,f44])).

fof(f289,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK6(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | sK9(sK0,sK1,sK6(sK0)) = k2_pre_topc(sK0,sK9(sK0,sK1,sK6(sK0))) ),
    inference(resolution,[],[f283,f63])).

fof(f283,plain,(
    v4_pre_topc(sK9(sK0,sK1,sK6(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f282,f226])).

fof(f282,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK6(sK0)),k1_zfmisc_1(sK1))
    | v4_pre_topc(sK9(sK0,sK1,sK6(sK0)),sK0) ),
    inference(forward_demodulation,[],[f281,f169])).

fof(f281,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK6(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK9(sK0,sK1,sK6(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f280,f43])).

fof(f280,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK6(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK9(sK0,sK1,sK6(sK0)),sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f279,f42])).

fof(f279,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK6(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK9(sK0,sK1,sK6(sK0)),sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f273,f44])).

fof(f273,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK9(sK0,sK1,sK6(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK9(sK0,sK1,sK6(sK0)),sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(resolution,[],[f228,f58])).

fof(f285,plain,(
    sK9(sK0,sK1,sK6(sK0)) = k9_subset_1(sK1,sK1,k2_pre_topc(sK0,sK9(sK0,sK1,sK6(sK0)))) ),
    inference(resolution,[],[f226,f187])).

fof(f187,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | k9_subset_1(sK1,sK1,k2_pre_topc(sK0,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f186,f169])).

fof(f186,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f176,f75])).

fof(f176,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | ~ r1_tarski(X0,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 ) ),
    inference(backward_demodulation,[],[f132,f169])).

fof(f132,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f131,f41])).

fof(f131,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f130,f38])).

fof(f130,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f129,f44])).

fof(f129,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f125,f42])).

fof(f125,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f98,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

fof(f228,plain,(
    v3_pre_topc(sK9(sK0,sK1,sK6(sK0)),sK0) ),
    inference(resolution,[],[f190,f185])).

fof(f190,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | v3_pre_topc(sK9(sK0,sK1,X2),sK0) ) ),
    inference(subsumption_resolution,[],[f178,f75])).

fof(f178,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | ~ r1_tarski(X2,sK1)
      | v3_pre_topc(sK9(sK0,sK1,X2),sK0) ) ),
    inference(backward_demodulation,[],[f136,f169])).

fof(f136,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X2,sK1)
      | v3_pre_topc(sK9(sK0,sK1,X2),sK0) ) ),
    inference(subsumption_resolution,[],[f135,f44])).

fof(f135,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X2,sK1)
      | v3_pre_topc(sK9(sK0,sK1,X2),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f127,f38])).

fof(f127,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X2,sK1)
      | v3_pre_topc(sK9(sK0,sK1,X2),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f98,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | v3_pre_topc(sK9(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:05:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (17501)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (17503)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (17499)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (17506)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (17517)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (17502)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (17500)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (17508)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (17505)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (17507)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (17512)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (17512)Refutation not found, incomplete strategy% (17512)------------------------------
% 0.21/0.53  % (17512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (17516)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.33/0.53  % (17520)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.33/0.53  % (17524)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.33/0.53  % (17512)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (17512)Memory used [KB]: 6140
% 1.33/0.53  % (17512)Time elapsed: 0.098 s
% 1.33/0.53  % (17512)------------------------------
% 1.33/0.53  % (17512)------------------------------
% 1.33/0.53  % (17523)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.33/0.53  % (17510)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.33/0.53  % (17504)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.33/0.53  % (17506)Refutation not found, incomplete strategy% (17506)------------------------------
% 1.33/0.53  % (17506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (17515)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.33/0.53  % (17521)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.33/0.53  % (17499)Refutation not found, incomplete strategy% (17499)------------------------------
% 1.33/0.53  % (17499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (17499)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (17499)Memory used [KB]: 10618
% 1.33/0.53  % (17499)Time elapsed: 0.120 s
% 1.33/0.53  % (17499)------------------------------
% 1.33/0.53  % (17499)------------------------------
% 1.33/0.53  % (17504)Refutation found. Thanks to Tanya!
% 1.33/0.53  % SZS status Theorem for theBenchmark
% 1.33/0.53  % SZS output start Proof for theBenchmark
% 1.33/0.53  % (17506)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  fof(f320,plain,(
% 1.33/0.53    $false),
% 1.33/0.53    inference(subsumption_resolution,[],[f319,f108])).
% 1.33/0.53  
% 1.33/0.53  fof(f108,plain,(
% 1.33/0.53    ~v1_tdlat_3(sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f107,f39])).
% 1.33/0.53  fof(f39,plain,(
% 1.33/0.53    v3_tex_2(sK1,sK0)),
% 1.33/0.53    inference(cnf_transformation,[],[f17])).
% 1.33/0.53  % (17506)Memory used [KB]: 1791
% 1.33/0.53  fof(f17,plain,(
% 1.33/0.53    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.33/0.53    inference(flattening,[],[f16])).
% 1.33/0.53  % (17506)Time elapsed: 0.122 s
% 1.33/0.53  fof(f16,plain,(
% 1.33/0.53    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.33/0.53    inference(ennf_transformation,[],[f15])).
% 1.33/0.53  % (17506)------------------------------
% 1.33/0.53  % (17506)------------------------------
% 1.33/0.53  fof(f15,negated_conjecture,(
% 1.33/0.53    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 1.33/0.53    inference(negated_conjecture,[],[f14])).
% 1.33/0.53  fof(f14,conjecture,(
% 1.33/0.53    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).
% 1.33/0.53  fof(f107,plain,(
% 1.33/0.53    ~v1_tdlat_3(sK0) | ~v3_tex_2(sK1,sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f106,f41])).
% 1.33/0.53  fof(f41,plain,(
% 1.33/0.53    ~v2_struct_0(sK0)),
% 1.33/0.53    inference(cnf_transformation,[],[f17])).
% 1.33/0.53  fof(f106,plain,(
% 1.33/0.53    ~v1_tdlat_3(sK0) | v2_struct_0(sK0) | ~v3_tex_2(sK1,sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f105,f38])).
% 1.33/0.53  fof(f38,plain,(
% 1.33/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.33/0.53    inference(cnf_transformation,[],[f17])).
% 1.33/0.53  fof(f105,plain,(
% 1.33/0.53    ~v1_tdlat_3(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v3_tex_2(sK1,sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f104,f44])).
% 1.33/0.53  fof(f44,plain,(
% 1.33/0.53    l1_pre_topc(sK0)),
% 1.33/0.53    inference(cnf_transformation,[],[f17])).
% 1.33/0.53  fof(f104,plain,(
% 1.33/0.53    ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v3_tex_2(sK1,sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f103,f42])).
% 1.33/0.53  fof(f42,plain,(
% 1.33/0.53    v2_pre_topc(sK0)),
% 1.33/0.53    inference(cnf_transformation,[],[f17])).
% 1.33/0.53  fof(f103,plain,(
% 1.33/0.53    ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v3_tex_2(sK1,sK0)),
% 1.33/0.53    inference(resolution,[],[f40,f46])).
% 1.33/0.53  fof(f46,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~v1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~v3_tex_2(X1,X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f19])).
% 1.33/0.53  fof(f19,plain,(
% 1.33/0.53    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.33/0.53    inference(flattening,[],[f18])).
% 1.33/0.53  fof(f18,plain,(
% 1.33/0.53    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.33/0.53    inference(ennf_transformation,[],[f13])).
% 1.33/0.53  fof(f13,axiom,(
% 1.33/0.53    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).
% 1.33/0.53  fof(f40,plain,(
% 1.33/0.53    v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.33/0.53    inference(cnf_transformation,[],[f17])).
% 1.33/0.53  fof(f319,plain,(
% 1.33/0.53    v1_tdlat_3(sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f318,f42])).
% 1.33/0.53  fof(f318,plain,(
% 1.33/0.53    ~v2_pre_topc(sK0) | v1_tdlat_3(sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f315,f44])).
% 1.33/0.53  fof(f315,plain,(
% 1.33/0.53    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v1_tdlat_3(sK0)),
% 1.33/0.53    inference(resolution,[],[f297,f70])).
% 1.33/0.53  fof(f70,plain,(
% 1.33/0.53    ( ! [X0] : (~v3_pre_topc(sK6(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v1_tdlat_3(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f33])).
% 1.33/0.53  fof(f33,plain,(
% 1.33/0.53    ! [X0] : (v1_tdlat_3(X0) | ? [X1] : (? [X2] : (~v3_pre_topc(X1,X0) & k1_tarski(X2) = X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.33/0.53    inference(flattening,[],[f32])).
% 1.33/0.53  fof(f32,plain,(
% 1.33/0.53    ! [X0] : ((v1_tdlat_3(X0) | ? [X1] : (? [X2] : ((~v3_pre_topc(X1,X0) & k1_tarski(X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.33/0.53    inference(ennf_transformation,[],[f8])).
% 1.33/0.53  fof(f8,axiom,(
% 1.33/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k1_tarski(X2) = X1 => v3_pre_topc(X1,X0)))) => v1_tdlat_3(X0)))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tdlat_3)).
% 1.33/0.53  fof(f297,plain,(
% 1.33/0.53    v3_pre_topc(sK6(sK0),sK0)),
% 1.33/0.53    inference(backward_demodulation,[],[f228,f295])).
% 1.33/0.53  fof(f295,plain,(
% 1.33/0.53    sK6(sK0) = sK9(sK0,sK1,sK6(sK0))),
% 1.33/0.53    inference(forward_demodulation,[],[f294,f245])).
% 1.33/0.53  fof(f245,plain,(
% 1.33/0.53    sK6(sK0) = k9_subset_1(sK1,sK1,sK9(sK0,sK1,sK6(sK0)))),
% 1.33/0.53    inference(resolution,[],[f192,f185])).
% 1.33/0.53  fof(f185,plain,(
% 1.33/0.53    m1_subset_1(sK6(sK0),k1_zfmisc_1(sK1))),
% 1.33/0.53    inference(subsumption_resolution,[],[f173,f108])).
% 1.33/0.53  fof(f173,plain,(
% 1.33/0.53    m1_subset_1(sK6(sK0),k1_zfmisc_1(sK1)) | v1_tdlat_3(sK0)),
% 1.33/0.53    inference(backward_demodulation,[],[f91,f169])).
% 1.33/0.53  fof(f169,plain,(
% 1.33/0.53    sK1 = u1_struct_0(sK0)),
% 1.33/0.53    inference(forward_demodulation,[],[f168,f151])).
% 1.33/0.53  fof(f151,plain,(
% 1.33/0.53    sK1 = k2_pre_topc(sK0,sK1)),
% 1.33/0.53    inference(subsumption_resolution,[],[f150,f44])).
% 1.33/0.53  fof(f150,plain,(
% 1.33/0.53    ~l1_pre_topc(sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.33/0.53    inference(subsumption_resolution,[],[f148,f38])).
% 1.33/0.53  fof(f148,plain,(
% 1.33/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.33/0.53    inference(resolution,[],[f147,f63])).
% 1.33/0.53  fof(f63,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = X1) )),
% 1.33/0.53    inference(cnf_transformation,[],[f29])).
% 1.33/0.53  fof(f29,plain,(
% 1.33/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.53    inference(flattening,[],[f28])).
% 1.33/0.53  fof(f28,plain,(
% 1.33/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.53    inference(ennf_transformation,[],[f4])).
% 1.33/0.53  fof(f4,axiom,(
% 1.33/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.33/0.53  fof(f147,plain,(
% 1.33/0.53    v4_pre_topc(sK1,sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f146,f43])).
% 1.33/0.53  fof(f43,plain,(
% 1.33/0.53    v3_tdlat_3(sK0)),
% 1.33/0.53    inference(cnf_transformation,[],[f17])).
% 1.33/0.53  fof(f146,plain,(
% 1.33/0.53    v4_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f145,f42])).
% 1.33/0.53  fof(f145,plain,(
% 1.33/0.53    v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f144,f38])).
% 1.33/0.53  fof(f144,plain,(
% 1.33/0.53    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f141,f44])).
% 1.33/0.53  fof(f141,plain,(
% 1.33/0.53    v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0)),
% 1.33/0.53    inference(duplicate_literal_removal,[],[f140])).
% 1.33/0.53  fof(f140,plain,(
% 1.33/0.53    v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0)),
% 1.33/0.53    inference(resolution,[],[f37,f58])).
% 1.33/0.53  fof(f58,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | v4_pre_topc(X1,X0) | ~v3_tdlat_3(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f27])).
% 1.33/0.53  fof(f27,plain,(
% 1.33/0.53    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.33/0.53    inference(flattening,[],[f26])).
% 1.33/0.53  fof(f26,plain,(
% 1.33/0.53    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.33/0.53    inference(ennf_transformation,[],[f9])).
% 1.33/0.53  fof(f9,axiom,(
% 1.33/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => v4_pre_topc(X1,X0)))))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).
% 1.33/0.53  fof(f37,plain,(
% 1.33/0.53    v3_pre_topc(sK1,sK0) | v4_pre_topc(sK1,sK0)),
% 1.33/0.53    inference(cnf_transformation,[],[f17])).
% 1.33/0.53  fof(f168,plain,(
% 1.33/0.53    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.33/0.53    inference(subsumption_resolution,[],[f167,f44])).
% 1.33/0.53  fof(f167,plain,(
% 1.33/0.53    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f166,f38])).
% 1.33/0.53  fof(f166,plain,(
% 1.33/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.33/0.53    inference(resolution,[],[f164,f73])).
% 1.33/0.53  fof(f73,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f34])).
% 1.33/0.53  % (17514)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.33/0.53  fof(f34,plain,(
% 1.33/0.53    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.53    inference(ennf_transformation,[],[f5])).
% 1.33/0.53  fof(f5,axiom,(
% 1.33/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 1.33/0.53  fof(f164,plain,(
% 1.33/0.53    v1_tops_1(sK1,sK0)),
% 1.33/0.53    inference(resolution,[],[f102,f158])).
% 1.33/0.53  fof(f158,plain,(
% 1.33/0.53    v3_pre_topc(sK1,sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f157,f43])).
% 1.33/0.53  fof(f157,plain,(
% 1.33/0.53    v3_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f156,f42])).
% 1.33/0.53  fof(f156,plain,(
% 1.33/0.53    ~v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f155,f38])).
% 1.33/0.53  fof(f155,plain,(
% 1.33/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f149,f44])).
% 1.33/0.53  fof(f149,plain,(
% 1.33/0.53    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0)),
% 1.33/0.53    inference(resolution,[],[f147,f54])).
% 1.33/0.54  fof(f54,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | v3_pre_topc(X1,X0) | ~v3_tdlat_3(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f25])).
% 1.33/0.54  fof(f25,plain,(
% 1.33/0.54    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.33/0.54    inference(flattening,[],[f24])).
% 1.33/0.54  fof(f24,plain,(
% 1.33/0.54    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f10])).
% 1.33/0.54  fof(f10,axiom,(
% 1.33/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).
% 1.33/0.54  fof(f102,plain,(
% 1.33/0.54    ~v3_pre_topc(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f101,f41])).
% 1.33/0.54  fof(f101,plain,(
% 1.33/0.54    ~v3_pre_topc(sK1,sK0) | v2_struct_0(sK0) | v1_tops_1(sK1,sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f100,f38])).
% 1.33/0.54  fof(f100,plain,(
% 1.33/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | v2_struct_0(sK0) | v1_tops_1(sK1,sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f99,f44])).
% 1.33/0.54  fof(f99,plain,(
% 1.33/0.54    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | v2_struct_0(sK0) | v1_tops_1(sK1,sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f94,f42])).
% 1.33/0.54  fof(f94,plain,(
% 1.33/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | v2_struct_0(sK0) | v1_tops_1(sK1,sK0)),
% 1.33/0.54    inference(resolution,[],[f39,f47])).
% 1.33/0.54  fof(f47,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | v2_struct_0(X0) | v1_tops_1(X1,X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f21])).
% 1.33/0.54  fof(f21,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.33/0.54    inference(flattening,[],[f20])).
% 1.33/0.54  fof(f20,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f12])).
% 1.33/0.54  fof(f12,axiom,(
% 1.33/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).
% 1.33/0.54  fof(f91,plain,(
% 1.33/0.54    m1_subset_1(sK6(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tdlat_3(sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f88,f44])).
% 1.33/0.54  fof(f88,plain,(
% 1.33/0.54    ~l1_pre_topc(sK0) | m1_subset_1(sK6(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tdlat_3(sK0)),
% 1.33/0.54    inference(resolution,[],[f42,f71])).
% 1.33/0.54  fof(f71,plain,(
% 1.33/0.54    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) | v1_tdlat_3(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f33])).
% 1.33/0.54  fof(f192,plain,(
% 1.33/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK1)) | k9_subset_1(sK1,sK1,sK9(sK0,sK1,X3)) = X3) )),
% 1.33/0.54    inference(forward_demodulation,[],[f191,f169])).
% 1.33/0.54  fof(f191,plain,(
% 1.33/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK1)) | k9_subset_1(u1_struct_0(sK0),sK1,sK9(sK0,sK1,X3)) = X3) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f179,f75])).
% 1.33/0.54  fof(f75,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f3])).
% 1.33/0.54  fof(f3,axiom,(
% 1.33/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.33/0.54  fof(f179,plain,(
% 1.33/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK1)) | ~r1_tarski(X3,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,sK9(sK0,sK1,X3)) = X3) )),
% 1.33/0.54    inference(backward_demodulation,[],[f138,f169])).
% 1.33/0.54  fof(f138,plain,(
% 1.33/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,sK9(sK0,sK1,X3)) = X3) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f137,f44])).
% 1.33/0.54  fof(f137,plain,(
% 1.33/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,sK9(sK0,sK1,X3)) = X3 | ~l1_pre_topc(sK0)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f128,f38])).
% 1.33/0.54  fof(f128,plain,(
% 1.33/0.54    ( ! [X3] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,sK9(sK0,sK1,X3)) = X3 | ~l1_pre_topc(sK0)) )),
% 1.33/0.54    inference(resolution,[],[f98,f79])).
% 1.33/0.54  fof(f79,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | k9_subset_1(u1_struct_0(X0),X1,sK9(X0,X1,X2)) = X2 | ~l1_pre_topc(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f36])).
% 1.33/0.54  fof(f36,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(flattening,[],[f35])).
% 1.33/0.54  fof(f35,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f6])).
% 1.33/0.54  fof(f6,axiom,(
% 1.33/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).
% 1.33/0.54  fof(f98,plain,(
% 1.33/0.54    v2_tex_2(sK1,sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f97,f44])).
% 1.33/0.54  fof(f97,plain,(
% 1.33/0.54    v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f93,f38])).
% 1.33/0.54  fof(f93,plain,(
% 1.33/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.33/0.54    inference(resolution,[],[f39,f53])).
% 1.33/0.54  fof(f53,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f23])).
% 1.33/0.54  fof(f23,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(flattening,[],[f22])).
% 1.33/0.54  fof(f22,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f7])).
% 1.33/0.54  fof(f7,axiom,(
% 1.33/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 1.33/0.54  fof(f294,plain,(
% 1.33/0.54    sK9(sK0,sK1,sK6(sK0)) = k9_subset_1(sK1,sK1,sK9(sK0,sK1,sK6(sK0)))),
% 1.33/0.54    inference(backward_demodulation,[],[f285,f293])).
% 1.33/0.54  fof(f293,plain,(
% 1.33/0.54    sK9(sK0,sK1,sK6(sK0)) = k2_pre_topc(sK0,sK9(sK0,sK1,sK6(sK0)))),
% 1.33/0.54    inference(subsumption_resolution,[],[f292,f226])).
% 1.33/0.54  fof(f226,plain,(
% 1.33/0.54    m1_subset_1(sK9(sK0,sK1,sK6(sK0)),k1_zfmisc_1(sK1))),
% 1.33/0.54    inference(resolution,[],[f189,f196])).
% 1.33/0.54  fof(f196,plain,(
% 1.33/0.54    r1_tarski(sK6(sK0),sK1)),
% 1.33/0.54    inference(resolution,[],[f185,f75])).
% 1.33/0.54  fof(f189,plain,(
% 1.33/0.54    ( ! [X1] : (~r1_tarski(X1,sK1) | m1_subset_1(sK9(sK0,sK1,X1),k1_zfmisc_1(sK1))) )),
% 1.33/0.54    inference(forward_demodulation,[],[f188,f169])).
% 1.33/0.54  fof(f188,plain,(
% 1.33/0.54    ( ! [X1] : (~r1_tarski(X1,sK1) | m1_subset_1(sK9(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f177,f74])).
% 1.33/0.54  fof(f74,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f3])).
% 1.33/0.54  fof(f177,plain,(
% 1.33/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~r1_tarski(X1,sK1) | m1_subset_1(sK9(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.33/0.54    inference(backward_demodulation,[],[f134,f169])).
% 1.33/0.54  fof(f134,plain,(
% 1.33/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,sK1) | m1_subset_1(sK9(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f133,f44])).
% 1.33/0.54  fof(f133,plain,(
% 1.33/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,sK1) | m1_subset_1(sK9(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f126,f38])).
% 1.33/0.54  fof(f126,plain,(
% 1.33/0.54    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,sK1) | m1_subset_1(sK9(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.33/0.54    inference(resolution,[],[f98,f77])).
% 1.33/0.54  fof(f77,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f36])).
% 1.33/0.54  fof(f292,plain,(
% 1.33/0.54    ~m1_subset_1(sK9(sK0,sK1,sK6(sK0)),k1_zfmisc_1(sK1)) | sK9(sK0,sK1,sK6(sK0)) = k2_pre_topc(sK0,sK9(sK0,sK1,sK6(sK0)))),
% 1.33/0.54    inference(forward_demodulation,[],[f291,f169])).
% 1.33/0.54  fof(f291,plain,(
% 1.33/0.54    ~m1_subset_1(sK9(sK0,sK1,sK6(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | sK9(sK0,sK1,sK6(sK0)) = k2_pre_topc(sK0,sK9(sK0,sK1,sK6(sK0)))),
% 1.33/0.54    inference(subsumption_resolution,[],[f289,f44])).
% 1.33/0.54  fof(f289,plain,(
% 1.33/0.54    ~m1_subset_1(sK9(sK0,sK1,sK6(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | sK9(sK0,sK1,sK6(sK0)) = k2_pre_topc(sK0,sK9(sK0,sK1,sK6(sK0)))),
% 1.33/0.54    inference(resolution,[],[f283,f63])).
% 1.33/0.54  fof(f283,plain,(
% 1.33/0.54    v4_pre_topc(sK9(sK0,sK1,sK6(sK0)),sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f282,f226])).
% 1.33/0.54  fof(f282,plain,(
% 1.33/0.54    ~m1_subset_1(sK9(sK0,sK1,sK6(sK0)),k1_zfmisc_1(sK1)) | v4_pre_topc(sK9(sK0,sK1,sK6(sK0)),sK0)),
% 1.33/0.54    inference(forward_demodulation,[],[f281,f169])).
% 1.33/0.54  fof(f281,plain,(
% 1.33/0.54    ~m1_subset_1(sK9(sK0,sK1,sK6(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK9(sK0,sK1,sK6(sK0)),sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f280,f43])).
% 1.33/0.54  fof(f280,plain,(
% 1.33/0.54    ~m1_subset_1(sK9(sK0,sK1,sK6(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK9(sK0,sK1,sK6(sK0)),sK0) | ~v3_tdlat_3(sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f279,f42])).
% 1.33/0.54  fof(f279,plain,(
% 1.33/0.54    ~m1_subset_1(sK9(sK0,sK1,sK6(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v4_pre_topc(sK9(sK0,sK1,sK6(sK0)),sK0) | ~v3_tdlat_3(sK0)),
% 1.33/0.54    inference(subsumption_resolution,[],[f273,f44])).
% 1.33/0.54  fof(f273,plain,(
% 1.33/0.54    ~l1_pre_topc(sK0) | ~m1_subset_1(sK9(sK0,sK1,sK6(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v4_pre_topc(sK9(sK0,sK1,sK6(sK0)),sK0) | ~v3_tdlat_3(sK0)),
% 1.33/0.54    inference(resolution,[],[f228,f58])).
% 1.33/0.54  fof(f285,plain,(
% 1.33/0.54    sK9(sK0,sK1,sK6(sK0)) = k9_subset_1(sK1,sK1,k2_pre_topc(sK0,sK9(sK0,sK1,sK6(sK0))))),
% 1.33/0.54    inference(resolution,[],[f226,f187])).
% 1.33/0.54  fof(f187,plain,(
% 1.33/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | k9_subset_1(sK1,sK1,k2_pre_topc(sK0,X0)) = X0) )),
% 1.33/0.54    inference(forward_demodulation,[],[f186,f169])).
% 1.33/0.54  fof(f186,plain,(
% 1.33/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f176,f75])).
% 1.33/0.54  fof(f176,plain,(
% 1.33/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) )),
% 1.33/0.54    inference(backward_demodulation,[],[f132,f169])).
% 1.33/0.54  fof(f132,plain,(
% 1.33/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f131,f41])).
% 1.33/0.54  fof(f131,plain,(
% 1.33/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | v2_struct_0(sK0)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f130,f38])).
% 1.33/0.54  fof(f130,plain,(
% 1.33/0.54    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | v2_struct_0(sK0)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f129,f44])).
% 1.33/0.54  fof(f129,plain,(
% 1.33/0.54    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | v2_struct_0(sK0)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f125,f42])).
% 1.33/0.54  fof(f125,plain,(
% 1.33/0.54    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | v2_struct_0(sK0)) )),
% 1.33/0.54    inference(resolution,[],[f98,f64])).
% 1.33/0.54  fof(f64,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~v2_tex_2(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | v2_struct_0(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f31])).
% 1.33/0.54  fof(f31,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.33/0.54    inference(flattening,[],[f30])).
% 1.33/0.54  fof(f30,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f11])).
% 1.33/0.54  fof(f11,axiom,(
% 1.33/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).
% 1.33/0.54  fof(f228,plain,(
% 1.33/0.54    v3_pre_topc(sK9(sK0,sK1,sK6(sK0)),sK0)),
% 1.33/0.54    inference(resolution,[],[f190,f185])).
% 1.33/0.54  fof(f190,plain,(
% 1.33/0.54    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(sK1)) | v3_pre_topc(sK9(sK0,sK1,X2),sK0)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f178,f75])).
% 1.33/0.54  fof(f178,plain,(
% 1.33/0.54    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(sK1)) | ~r1_tarski(X2,sK1) | v3_pre_topc(sK9(sK0,sK1,X2),sK0)) )),
% 1.33/0.54    inference(backward_demodulation,[],[f136,f169])).
% 1.33/0.54  fof(f136,plain,(
% 1.33/0.54    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK1) | v3_pre_topc(sK9(sK0,sK1,X2),sK0)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f135,f44])).
% 1.33/0.54  fof(f135,plain,(
% 1.33/0.54    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK1) | v3_pre_topc(sK9(sK0,sK1,X2),sK0) | ~l1_pre_topc(sK0)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f127,f38])).
% 1.33/0.54  fof(f127,plain,(
% 1.33/0.54    ( ! [X2] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK1) | v3_pre_topc(sK9(sK0,sK1,X2),sK0) | ~l1_pre_topc(sK0)) )),
% 1.33/0.54    inference(resolution,[],[f98,f78])).
% 1.33/0.54  fof(f78,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | v3_pre_topc(sK9(X0,X1,X2),X0) | ~l1_pre_topc(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f36])).
% 1.33/0.54  % SZS output end Proof for theBenchmark
% 1.33/0.54  % (17504)------------------------------
% 1.33/0.54  % (17504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (17504)Termination reason: Refutation
% 1.33/0.54  
% 1.33/0.54  % (17504)Memory used [KB]: 6268
% 1.33/0.54  % (17504)Time elapsed: 0.127 s
% 1.33/0.54  % (17504)------------------------------
% 1.33/0.54  % (17504)------------------------------
% 1.33/0.54  % (17495)Success in time 0.177 s
%------------------------------------------------------------------------------
