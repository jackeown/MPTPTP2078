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
% DateTime   : Thu Dec  3 13:21:39 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  189 (2557 expanded)
%              Number of leaves         :   17 ( 510 expanded)
%              Depth                    :   49
%              Number of atoms          :  632 (12276 expanded)
%              Number of equality atoms :   63 ( 453 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f608,plain,(
    $false ),
    inference(subsumption_resolution,[],[f607,f48])).

fof(f48,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(f607,plain,(
    v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f605,f49])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f605,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f556,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f73,f67])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f44])).

% (13676)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f556,plain,(
    ~ m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f527,f450])).

fof(f450,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f449,f47])).

fof(f47,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f449,plain,(
    v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f448,f295])).

fof(f295,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f294,f48])).

fof(f294,plain,
    ( v1_xboole_0(sK1)
    | l1_pre_topc(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f289,f49])).

fof(f289,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | l1_pre_topc(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f288,f46])).

fof(f46,plain,
    ( v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f288,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | l1_pre_topc(sK2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f287,f53])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f287,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_xboole_0(X0)
      | ~ l1_pre_topc(sK0)
      | l1_pre_topc(sK2(sK0,X0)) ) ),
    inference(resolution,[],[f286,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f286,plain,(
    ! [X0] :
      ( m1_pre_topc(sK2(sK0,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f285,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f285,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | m1_pre_topc(sK2(sK0,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f284,f51])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f284,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | m1_pre_topc(sK2(sK0,X0),sK0) ) ),
    inference(resolution,[],[f64,f53])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

fof(f448,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_pre_topc(sK2(sK0,sK1)) ),
    inference(resolution,[],[f447,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f447,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f446,f46])).

fof(f446,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ l1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f445,f47])).

fof(f445,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f444,f344])).

fof(f344,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f343,f47])).

fof(f343,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f342,f50])).

fof(f342,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f341,f49])).

fof(f341,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f340,f48])).

fof(f340,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f339,f53])).

fof(f339,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f338,f51])).

fof(f338,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f337,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f337,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f336,f46])).

fof(f336,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f335,f47])).

fof(f335,plain,
    ( v1_zfmisc_1(sK1)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f334,f48])).

fof(f334,plain,
    ( v1_zfmisc_1(sK1)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f333,f49])).

fof(f333,plain,
    ( v1_zfmisc_1(sK1)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f327,f286])).

fof(f327,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v1_zfmisc_1(sK1)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f326,f50])).

fof(f326,plain,
    ( v1_zfmisc_1(sK1)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f325,f53])).

fof(f325,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f250,f52])).

fof(f52,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f250,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | v1_zfmisc_1(sK1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2(sK0,sK1),X0)
      | v2_struct_0(sK2(sK0,sK1))
      | v7_struct_0(sK2(sK0,sK1))
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f247,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | v7_struct_0(X1)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f60,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | v7_struct_0(X1)
      | ~ v1_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( ~ v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc32_tex_2)).

fof(f247,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f246,f48])).

fof(f246,plain,
    ( v1_xboole_0(sK1)
    | v1_tdlat_3(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f242,f49])).

fof(f242,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | v1_tdlat_3(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f241,f46])).

fof(f241,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | v1_tdlat_3(sK2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f240,f50])).

fof(f240,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_tdlat_3(sK2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f239,f51])).

fof(f239,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v1_tdlat_3(sK2(sK0,X0)) ) ),
    inference(resolution,[],[f63,f53])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v1_tdlat_3(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f444,plain,
    ( ~ v7_struct_0(sK2(sK0,sK1))
    | ~ l1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(superposition,[],[f66,f435])).

fof(f435,plain,(
    sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f433,f48])).

fof(f433,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f425,f49])).

fof(f425,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = u1_struct_0(sK2(sK0,sK1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f423,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f423,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f422,f139])).

fof(f139,plain,
    ( m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f138,f48])).

fof(f138,plain,
    ( m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f136,f49])).

fof(f136,plain,
    ( m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f135,f78])).

fof(f135,plain,
    ( ~ m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f71,f133])).

fof(f133,plain,(
    k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) ),
    inference(subsumption_resolution,[],[f130,f48])).

fof(f130,plain,
    ( k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f84,f49])).

fof(f84,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | k6_domain_1(X2,sK3(X3)) = k1_tarski(sK3(X3))
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f82,f59])).

fof(f82,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(X2)
      | k6_domain_1(X2,sK3(X3)) = k1_tarski(sK3(X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f70,f78])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f422,plain,
    ( ~ m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f420,f54])).

fof(f54,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f420,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_tarski(sK3(sK1))) ),
    inference(resolution,[],[f397,f78])).

fof(f397,plain,
    ( ~ m1_subset_1(sK3(k1_tarski(sK3(sK1))),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f380,f355])).

fof(f355,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f351,f47])).

fof(f351,plain,
    ( v1_zfmisc_1(sK1)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f350,f48])).

fof(f350,plain,
    ( v1_xboole_0(sK1)
    | sK1 = u1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f345,f49])).

fof(f345,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | sK1 = u1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f332,f46])).

fof(f332,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | u1_struct_0(sK2(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f331,f53])).

fof(f331,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | u1_struct_0(sK2(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f328,f50])).

fof(f328,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | u1_struct_0(sK2(sK0,X0)) = X0 ) ),
    inference(resolution,[],[f65,f51])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f380,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK3(k1_tarski(sK3(sK1))),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(superposition,[],[f270,f368])).

fof(f368,plain,
    ( sK1 = k1_tarski(sK3(k1_tarski(sK3(sK1))))
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f360,f54])).

fof(f360,plain,
    ( v1_xboole_0(k1_tarski(sK3(k1_tarski(sK3(sK1)))))
    | sK1 = u1_struct_0(sK2(sK0,sK1))
    | sK1 = k1_tarski(sK3(k1_tarski(sK3(sK1)))) ),
    inference(resolution,[],[f357,f166])).

fof(f166,plain,(
    r1_tarski(k1_tarski(sK3(k1_tarski(sK3(sK1)))),sK1) ),
    inference(resolution,[],[f164,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f164,plain,(
    m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(sK1)))),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f163,f48])).

fof(f163,plain,
    ( m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(sK1)))),k1_zfmisc_1(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f161,f67])).

fof(f161,plain,
    ( ~ r2_hidden(sK3(sK1),sK1)
    | m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(sK1)))),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f158,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f158,plain,
    ( ~ m1_subset_1(sK3(sK1),sK1)
    | m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(sK1)))),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f157,f96])).

fof(f96,plain,
    ( m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3(sK1),sK1) ),
    inference(subsumption_resolution,[],[f95,f48])).

fof(f95,plain,
    ( m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3(sK1),sK1)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f71,f89])).

fof(f89,plain,(
    k1_tarski(sK3(sK1)) = k6_domain_1(sK1,sK3(sK1)) ),
    inference(resolution,[],[f85,f48])).

fof(f85,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k1_tarski(sK3(X0)) = k6_domain_1(X0,sK3(X0)) ) ),
    inference(resolution,[],[f83,f67])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(subsumption_resolution,[],[f81,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f70,f69])).

fof(f157,plain,
    ( ~ m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1))
    | m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(sK1)))),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f155,f54])).

fof(f155,plain,
    ( m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(sK1)))),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_tarski(sK3(sK1))) ),
    inference(resolution,[],[f154,f78])).

fof(f154,plain,
    ( ~ m1_subset_1(sK3(k1_tarski(sK3(sK1))),sK1)
    | m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(sK1)))),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f152,f48])).

fof(f152,plain,
    ( m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(sK1)))),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3(k1_tarski(sK3(sK1))),sK1)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f71,f150])).

fof(f150,plain,(
    k6_domain_1(sK1,sK3(k1_tarski(sK3(sK1)))) = k1_tarski(sK3(k1_tarski(sK3(sK1)))) ),
    inference(subsumption_resolution,[],[f149,f48])).

fof(f149,plain,
    ( k6_domain_1(sK1,sK3(k1_tarski(sK3(sK1)))) = k1_tarski(sK3(k1_tarski(sK3(sK1))))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f145,f67])).

fof(f145,plain,
    ( ~ r2_hidden(sK3(sK1),sK1)
    | k6_domain_1(sK1,sK3(k1_tarski(sK3(sK1)))) = k1_tarski(sK3(k1_tarski(sK3(sK1)))) ),
    inference(resolution,[],[f132,f69])).

fof(f132,plain,
    ( ~ m1_subset_1(sK3(sK1),sK1)
    | k6_domain_1(sK1,sK3(k1_tarski(sK3(sK1)))) = k1_tarski(sK3(k1_tarski(sK3(sK1)))) ),
    inference(subsumption_resolution,[],[f128,f54])).

fof(f128,plain,
    ( k6_domain_1(sK1,sK3(k1_tarski(sK3(sK1)))) = k1_tarski(sK3(k1_tarski(sK3(sK1))))
    | v1_xboole_0(k1_tarski(sK3(sK1)))
    | ~ m1_subset_1(sK3(sK1),sK1) ),
    inference(resolution,[],[f84,f96])).

fof(f357,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | v1_xboole_0(X0)
      | sK1 = u1_struct_0(sK2(sK0,sK1))
      | sK1 = X0 ) ),
    inference(subsumption_resolution,[],[f356,f48])).

fof(f356,plain,(
    ! [X0] :
      ( sK1 = u1_struct_0(sK2(sK0,sK1))
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,sK1)
      | sK1 = X0 ) ),
    inference(resolution,[],[f351,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f270,plain,
    ( v2_tex_2(k1_tarski(sK3(k1_tarski(sK3(sK1)))),sK0)
    | ~ m1_subset_1(sK3(k1_tarski(sK3(sK1))),u1_struct_0(sK0)) ),
    inference(superposition,[],[f172,f269])).

fof(f269,plain,(
    k1_tarski(sK3(k1_tarski(sK3(sK1)))) = k6_domain_1(u1_struct_0(sK0),sK3(k1_tarski(sK3(sK1)))) ),
    inference(subsumption_resolution,[],[f267,f48])).

fof(f267,plain,
    ( k1_tarski(sK3(k1_tarski(sK3(sK1)))) = k6_domain_1(u1_struct_0(sK0),sK3(k1_tarski(sK3(sK1))))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f147,f49])).

fof(f147,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tarski(sK3(k1_tarski(sK3(sK1)))) = k6_domain_1(u1_struct_0(sK0),sK3(k1_tarski(sK3(sK1))))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f143,f59])).

fof(f143,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_tarski(sK3(k1_tarski(sK3(sK1)))) = k6_domain_1(u1_struct_0(sK0),sK3(k1_tarski(sK3(sK1)))) ),
    inference(subsumption_resolution,[],[f140,f54])).

fof(f140,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_tarski(sK3(k1_tarski(sK3(sK1)))) = k6_domain_1(u1_struct_0(sK0),sK3(k1_tarski(sK3(sK1))))
    | v1_xboole_0(k1_tarski(sK3(sK1))) ),
    inference(resolution,[],[f139,f84])).

fof(f172,plain,(
    ! [X0] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f171,f50])).

fof(f171,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f170,f51])).

fof(f170,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(resolution,[],[f61,f53])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f66,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f527,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f173,f508])).

fof(f508,plain,(
    sK1 = k1_tarski(sK3(sK1)) ),
    inference(forward_demodulation,[],[f507,f463])).

fof(f463,plain,(
    sK1 = k1_tarski(sK3(k1_tarski(sK3(sK1)))) ),
    inference(subsumption_resolution,[],[f455,f54])).

fof(f455,plain,
    ( v1_xboole_0(k1_tarski(sK3(k1_tarski(sK3(sK1)))))
    | sK1 = k1_tarski(sK3(k1_tarski(sK3(sK1)))) ),
    inference(resolution,[],[f452,f166])).

fof(f452,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | v1_xboole_0(X0)
      | sK1 = X0 ) ),
    inference(subsumption_resolution,[],[f451,f48])).

fof(f451,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,sK1)
      | sK1 = X0 ) ),
    inference(resolution,[],[f449,f55])).

fof(f507,plain,(
    sK1 = k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))) ),
    inference(subsumption_resolution,[],[f457,f54])).

fof(f457,plain,
    ( v1_xboole_0(k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))))
    | sK1 = k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))) ),
    inference(resolution,[],[f452,f186])).

fof(f186,plain,(
    r1_tarski(k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))),sK1) ),
    inference(resolution,[],[f184,f72])).

fof(f184,plain,(
    m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f183,f54])).

fof(f183,plain,
    ( m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))),k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_tarski(sK3(k1_tarski(sK3(sK1))))) ),
    inference(subsumption_resolution,[],[f181,f164])).

fof(f181,plain,
    ( m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(sK1)))),k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_tarski(sK3(k1_tarski(sK3(sK1))))) ),
    inference(resolution,[],[f177,f78])).

fof(f177,plain,
    ( ~ m1_subset_1(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1))))),sK1)
    | m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f175,f48])).

fof(f175,plain,
    ( m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1))))),sK1)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f71,f168])).

fof(f168,plain,(
    k6_domain_1(sK1,sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))) = k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))) ),
    inference(subsumption_resolution,[],[f165,f54])).

fof(f165,plain,
    ( k6_domain_1(sK1,sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))) = k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1))))))
    | v1_xboole_0(k1_tarski(sK3(k1_tarski(sK3(sK1))))) ),
    inference(resolution,[],[f164,f84])).

fof(f173,plain,
    ( v2_tex_2(k1_tarski(sK3(sK1)),sK0)
    | ~ m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    inference(superposition,[],[f172,f133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n005.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 11:58:32 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.19/0.44  % (13680)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.47  % (13696)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.48  % (13696)Refutation not found, incomplete strategy% (13696)------------------------------
% 0.19/0.48  % (13696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (13698)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.48  % (13688)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.48  % (13696)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (13696)Memory used [KB]: 10746
% 0.19/0.48  % (13696)Time elapsed: 0.104 s
% 0.19/0.48  % (13696)------------------------------
% 0.19/0.48  % (13696)------------------------------
% 0.19/0.49  % (13674)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.49  % (13678)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.49  % (13680)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f608,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(subsumption_resolution,[],[f607,f48])).
% 0.19/0.49  fof(f48,plain,(
% 0.19/0.49    ~v1_xboole_0(sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.49    inference(flattening,[],[f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f18])).
% 0.19/0.49  fof(f18,negated_conjecture,(
% 0.19/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.19/0.49    inference(negated_conjecture,[],[f17])).
% 0.19/0.49  fof(f17,conjecture,(
% 0.19/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 0.19/0.49  fof(f607,plain,(
% 0.19/0.49    v1_xboole_0(sK1)),
% 0.19/0.49    inference(subsumption_resolution,[],[f605,f49])).
% 0.19/0.49  fof(f49,plain,(
% 0.19/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f605,plain,(
% 0.19/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1)),
% 0.19/0.49    inference(resolution,[],[f556,f78])).
% 0.19/0.49  fof(f78,plain,(
% 0.19/0.49    ( ! [X0,X1] : (m1_subset_1(sK3(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_xboole_0(X0)) )),
% 0.19/0.49    inference(resolution,[],[f73,f67])).
% 0.19/0.49  fof(f67,plain,(
% 0.19/0.49    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.49  fof(f73,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f45])).
% 0.19/0.49  fof(f45,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.19/0.49    inference(flattening,[],[f44])).
% 0.19/0.49  % (13676)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.50  fof(f44,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.19/0.50    inference(ennf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.19/0.50  fof(f556,plain,(
% 0.19/0.50    ~m1_subset_1(sK3(sK1),u1_struct_0(sK0))),
% 0.19/0.50    inference(subsumption_resolution,[],[f527,f450])).
% 0.19/0.50  fof(f450,plain,(
% 0.19/0.50    ~v2_tex_2(sK1,sK0)),
% 0.19/0.50    inference(resolution,[],[f449,f47])).
% 0.19/0.50  fof(f47,plain,(
% 0.19/0.50    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f22])).
% 0.19/0.50  fof(f449,plain,(
% 0.19/0.50    v1_zfmisc_1(sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f448,f295])).
% 0.19/0.50  fof(f295,plain,(
% 0.19/0.50    l1_pre_topc(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f294,f48])).
% 0.19/0.50  fof(f294,plain,(
% 0.19/0.50    v1_xboole_0(sK1) | l1_pre_topc(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f289,f49])).
% 0.19/0.50  fof(f289,plain,(
% 0.19/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | l1_pre_topc(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.19/0.50    inference(resolution,[],[f288,f46])).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f22])).
% 0.19/0.50  fof(f288,plain,(
% 0.19/0.50    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | l1_pre_topc(sK2(sK0,X0))) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f287,f53])).
% 0.19/0.50  fof(f53,plain,(
% 0.19/0.50    l1_pre_topc(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f22])).
% 0.19/0.50  fof(f287,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_xboole_0(X0) | ~l1_pre_topc(sK0) | l1_pre_topc(sK2(sK0,X0))) )),
% 0.19/0.50    inference(resolution,[],[f286,f58])).
% 0.19/0.50  fof(f58,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f28])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f8])).
% 0.19/0.50  fof(f8,axiom,(
% 0.19/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.19/0.50  fof(f286,plain,(
% 0.19/0.50    ( ! [X0] : (m1_pre_topc(sK2(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_xboole_0(X0)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f285,f50])).
% 0.19/0.50  fof(f50,plain,(
% 0.19/0.50    ~v2_struct_0(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f22])).
% 0.19/0.50  fof(f285,plain,(
% 0.19/0.50    ( ! [X0] : (v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | m1_pre_topc(sK2(sK0,X0),sK0)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f284,f51])).
% 0.19/0.50  fof(f51,plain,(
% 0.19/0.50    v2_pre_topc(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f22])).
% 0.19/0.50  fof(f284,plain,(
% 0.19/0.50    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | m1_pre_topc(sK2(sK0,X0),sK0)) )),
% 0.19/0.50    inference(resolution,[],[f64,f53])).
% 0.19/0.50  fof(f64,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | m1_pre_topc(sK2(X0,X1),X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f35])).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f34])).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f20])).
% 0.19/0.50  fof(f20,plain,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.19/0.50    inference(pure_predicate_removal,[],[f15])).
% 0.19/0.50  fof(f15,axiom,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).
% 0.19/0.50  fof(f448,plain,(
% 0.19/0.50    v1_zfmisc_1(sK1) | ~l1_pre_topc(sK2(sK0,sK1))),
% 0.19/0.50    inference(resolution,[],[f447,f56])).
% 0.19/0.50  fof(f56,plain,(
% 0.19/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f25])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,axiom,(
% 0.19/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.50  fof(f447,plain,(
% 0.19/0.50    ~l1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.19/0.50    inference(resolution,[],[f446,f46])).
% 0.19/0.50  fof(f446,plain,(
% 0.19/0.50    ~v2_tex_2(sK1,sK0) | ~l1_struct_0(sK2(sK0,sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f445,f47])).
% 0.19/0.50  fof(f445,plain,(
% 0.19/0.50    ~l1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.19/0.50    inference(resolution,[],[f444,f344])).
% 0.19/0.50  fof(f344,plain,(
% 0.19/0.50    v7_struct_0(sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f343,f47])).
% 0.19/0.50  fof(f343,plain,(
% 0.19/0.50    v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f342,f50])).
% 0.19/0.50  fof(f342,plain,(
% 0.19/0.50    v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f341,f49])).
% 0.19/0.50  fof(f341,plain,(
% 0.19/0.50    v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f340,f48])).
% 0.19/0.50  fof(f340,plain,(
% 0.19/0.50    v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f339,f53])).
% 0.19/0.50  fof(f339,plain,(
% 0.19/0.50    v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f338,f51])).
% 0.19/0.50  fof(f338,plain,(
% 0.19/0.50    v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 0.19/0.50    inference(resolution,[],[f337,f62])).
% 0.19/0.50  fof(f62,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f35])).
% 0.19/0.50  fof(f337,plain,(
% 0.19/0.50    v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.19/0.50    inference(resolution,[],[f336,f46])).
% 0.19/0.50  fof(f336,plain,(
% 0.19/0.50    ~v2_tex_2(sK1,sK0) | v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f335,f47])).
% 0.19/0.50  fof(f335,plain,(
% 0.19/0.50    v1_zfmisc_1(sK1) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f334,f48])).
% 0.19/0.50  fof(f334,plain,(
% 0.19/0.50    v1_zfmisc_1(sK1) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f333,f49])).
% 0.19/0.50  fof(f333,plain,(
% 0.19/0.50    v1_zfmisc_1(sK1) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v1_xboole_0(sK1)),
% 0.19/0.50    inference(resolution,[],[f327,f286])).
% 0.19/0.50  fof(f327,plain,(
% 0.19/0.50    ~m1_pre_topc(sK2(sK0,sK1),sK0) | v1_zfmisc_1(sK1) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f326,f50])).
% 0.19/0.50  fof(f326,plain,(
% 0.19/0.50    v1_zfmisc_1(sK1) | ~m1_pre_topc(sK2(sK0,sK1),sK0) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.19/0.50    inference(subsumption_resolution,[],[f325,f53])).
% 0.19/0.50  fof(f325,plain,(
% 0.19/0.50    v1_zfmisc_1(sK1) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2(sK0,sK1),sK0) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.19/0.50    inference(resolution,[],[f250,f52])).
% 0.19/0.50  fof(f52,plain,(
% 0.19/0.50    v2_tdlat_3(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f22])).
% 0.19/0.50  fof(f250,plain,(
% 0.19/0.50    ( ! [X0] : (~v2_tdlat_3(X0) | v1_zfmisc_1(sK1) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2(sK0,sK1),X0) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(resolution,[],[f247,f74])).
% 0.19/0.50  fof(f74,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~v1_tdlat_3(X1) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | v7_struct_0(X1) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f60,f57])).
% 0.19/0.50  fof(f57,plain,(
% 0.19/0.50    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f27])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(flattening,[],[f26])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,axiom,(
% 0.19/0.50    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.19/0.50  fof(f60,plain,(
% 0.19/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | v7_struct_0(X1) | ~v1_tdlat_3(X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f31])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f30])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f13])).
% 0.19/0.50  fof(f13,axiom,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc32_tex_2)).
% 0.19/0.50  fof(f247,plain,(
% 0.19/0.50    v1_tdlat_3(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f246,f48])).
% 0.19/0.50  fof(f246,plain,(
% 0.19/0.50    v1_xboole_0(sK1) | v1_tdlat_3(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f242,f49])).
% 0.19/0.50  fof(f242,plain,(
% 0.19/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | v1_tdlat_3(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.19/0.50    inference(resolution,[],[f241,f46])).
% 0.19/0.50  fof(f241,plain,(
% 0.19/0.50    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | v1_tdlat_3(sK2(sK0,X0))) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f240,f50])).
% 0.19/0.50  fof(f240,plain,(
% 0.19/0.50    ( ! [X0] : (v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_tdlat_3(sK2(sK0,X0))) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f239,f51])).
% 0.19/0.50  fof(f239,plain,(
% 0.19/0.50    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v1_tdlat_3(sK2(sK0,X0))) )),
% 0.19/0.50    inference(resolution,[],[f63,f53])).
% 0.19/0.50  fof(f63,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v1_tdlat_3(sK2(X0,X1))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f35])).
% 0.19/0.50  fof(f444,plain,(
% 0.19/0.50    ~v7_struct_0(sK2(sK0,sK1)) | ~l1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.19/0.50    inference(superposition,[],[f66,f435])).
% 0.19/0.50  fof(f435,plain,(
% 0.19/0.50    sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f433,f48])).
% 0.19/0.50  fof(f433,plain,(
% 0.19/0.50    sK1 = u1_struct_0(sK2(sK0,sK1)) | v1_xboole_0(sK1)),
% 0.19/0.50    inference(resolution,[],[f425,f49])).
% 0.19/0.50  fof(f425,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK2(sK0,sK1)) | v1_xboole_0(X0)) )),
% 0.19/0.50    inference(resolution,[],[f423,f59])).
% 0.19/0.50  fof(f59,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f29])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.19/0.50  fof(f423,plain,(
% 0.19/0.50    v1_xboole_0(u1_struct_0(sK0)) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.19/0.50    inference(resolution,[],[f422,f139])).
% 0.19/0.50  fof(f139,plain,(
% 0.19/0.50    m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.50    inference(subsumption_resolution,[],[f138,f48])).
% 0.19/0.50  fof(f138,plain,(
% 0.19/0.50    m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f136,f49])).
% 0.19/0.50  fof(f136,plain,(
% 0.19/0.50    m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1)),
% 0.19/0.50    inference(resolution,[],[f135,f78])).
% 0.19/0.50  fof(f135,plain,(
% 0.19/0.50    ~m1_subset_1(sK3(sK1),u1_struct_0(sK0)) | m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.50    inference(superposition,[],[f71,f133])).
% 0.19/0.50  fof(f133,plain,(
% 0.19/0.50    k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f130,f48])).
% 0.19/0.50  fof(f130,plain,(
% 0.19/0.50    k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) | v1_xboole_0(sK1)),
% 0.19/0.50    inference(resolution,[],[f84,f49])).
% 0.19/0.50  fof(f84,plain,(
% 0.19/0.50    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X2)) | k6_domain_1(X2,sK3(X3)) = k1_tarski(sK3(X3)) | v1_xboole_0(X3)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f82,f59])).
% 0.19/0.50  fof(f82,plain,(
% 0.19/0.50    ( ! [X2,X3] : (v1_xboole_0(X2) | k6_domain_1(X2,sK3(X3)) = k1_tarski(sK3(X3)) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | v1_xboole_0(X3)) )),
% 0.19/0.50    inference(resolution,[],[f70,f78])).
% 0.19/0.50  fof(f70,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f40])).
% 0.19/0.50  fof(f40,plain,(
% 0.19/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.19/0.50    inference(flattening,[],[f39])).
% 0.19/0.50  fof(f39,plain,(
% 0.19/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f11])).
% 0.19/0.50  fof(f11,axiom,(
% 0.19/0.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.19/0.50  fof(f71,plain,(
% 0.19/0.50    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f42])).
% 0.19/0.50  fof(f42,plain,(
% 0.19/0.50    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.19/0.50    inference(flattening,[],[f41])).
% 0.19/0.50  fof(f41,plain,(
% 0.19/0.50    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,axiom,(
% 0.19/0.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.19/0.50  fof(f422,plain,(
% 0.19/0.50    ~m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f420,f54])).
% 0.19/0.50  fof(f54,plain,(
% 0.19/0.50    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.19/0.50  fof(f420,plain,(
% 0.19/0.50    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k1_tarski(sK3(sK1)))),
% 0.19/0.50    inference(resolution,[],[f397,f78])).
% 0.19/0.50  fof(f397,plain,(
% 0.19/0.50    ~m1_subset_1(sK3(k1_tarski(sK3(sK1))),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f380,f355])).
% 0.19/0.50  fof(f355,plain,(
% 0.19/0.50    ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.19/0.50    inference(resolution,[],[f351,f47])).
% 0.19/0.50  fof(f351,plain,(
% 0.19/0.50    v1_zfmisc_1(sK1) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f350,f48])).
% 0.19/0.50  fof(f350,plain,(
% 0.19/0.50    v1_xboole_0(sK1) | sK1 = u1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f345,f49])).
% 0.19/0.50  fof(f345,plain,(
% 0.19/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | sK1 = u1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.19/0.50    inference(resolution,[],[f332,f46])).
% 0.19/0.50  fof(f332,plain,(
% 0.19/0.50    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | u1_struct_0(sK2(sK0,X0)) = X0) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f331,f53])).
% 0.19/0.50  fof(f331,plain,(
% 0.19/0.50    ( ! [X0] : (~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | u1_struct_0(sK2(sK0,X0)) = X0) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f328,f50])).
% 0.19/0.50  fof(f328,plain,(
% 0.19/0.50    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | u1_struct_0(sK2(sK0,X0)) = X0) )),
% 0.19/0.50    inference(resolution,[],[f65,f51])).
% 0.19/0.50  fof(f65,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | u1_struct_0(sK2(X0,X1)) = X1) )),
% 0.19/0.50    inference(cnf_transformation,[],[f35])).
% 0.19/0.50  fof(f380,plain,(
% 0.19/0.50    v2_tex_2(sK1,sK0) | ~m1_subset_1(sK3(k1_tarski(sK3(sK1))),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.19/0.50    inference(superposition,[],[f270,f368])).
% 0.19/0.50  fof(f368,plain,(
% 0.19/0.50    sK1 = k1_tarski(sK3(k1_tarski(sK3(sK1)))) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f360,f54])).
% 0.19/0.50  fof(f360,plain,(
% 0.19/0.50    v1_xboole_0(k1_tarski(sK3(k1_tarski(sK3(sK1))))) | sK1 = u1_struct_0(sK2(sK0,sK1)) | sK1 = k1_tarski(sK3(k1_tarski(sK3(sK1))))),
% 0.19/0.50    inference(resolution,[],[f357,f166])).
% 0.19/0.50  fof(f166,plain,(
% 0.19/0.50    r1_tarski(k1_tarski(sK3(k1_tarski(sK3(sK1)))),sK1)),
% 0.19/0.50    inference(resolution,[],[f164,f72])).
% 0.19/0.50  fof(f72,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f43])).
% 0.19/0.50  fof(f43,plain,(
% 0.19/0.50    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.19/0.50    inference(ennf_transformation,[],[f19])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.19/0.50    inference(unused_predicate_definition_removal,[],[f5])).
% 0.19/0.50  fof(f5,axiom,(
% 0.19/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.50  fof(f164,plain,(
% 0.19/0.50    m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(sK1)))),k1_zfmisc_1(sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f163,f48])).
% 0.19/0.50  fof(f163,plain,(
% 0.19/0.50    m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(sK1)))),k1_zfmisc_1(sK1)) | v1_xboole_0(sK1)),
% 0.19/0.50    inference(resolution,[],[f161,f67])).
% 0.19/0.50  fof(f161,plain,(
% 0.19/0.50    ~r2_hidden(sK3(sK1),sK1) | m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(sK1)))),k1_zfmisc_1(sK1))),
% 0.19/0.50    inference(resolution,[],[f158,f69])).
% 0.19/0.50  fof(f69,plain,(
% 0.19/0.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f38])).
% 0.19/0.50  fof(f38,plain,(
% 0.19/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.19/0.50    inference(ennf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.19/0.50  fof(f158,plain,(
% 0.19/0.50    ~m1_subset_1(sK3(sK1),sK1) | m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(sK1)))),k1_zfmisc_1(sK1))),
% 0.19/0.50    inference(resolution,[],[f157,f96])).
% 0.19/0.50  fof(f96,plain,(
% 0.19/0.50    m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK3(sK1),sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f95,f48])).
% 0.19/0.50  fof(f95,plain,(
% 0.19/0.50    m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK3(sK1),sK1) | v1_xboole_0(sK1)),
% 0.19/0.50    inference(superposition,[],[f71,f89])).
% 0.19/0.50  fof(f89,plain,(
% 0.19/0.50    k1_tarski(sK3(sK1)) = k6_domain_1(sK1,sK3(sK1))),
% 0.19/0.50    inference(resolution,[],[f85,f48])).
% 0.19/0.50  fof(f85,plain,(
% 0.19/0.50    ( ! [X0] : (v1_xboole_0(X0) | k1_tarski(sK3(X0)) = k6_domain_1(X0,sK3(X0))) )),
% 0.19/0.50    inference(resolution,[],[f83,f67])).
% 0.19/0.50  fof(f83,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f81,f68])).
% 0.19/0.50  fof(f68,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f1])).
% 0.19/0.50  fof(f81,plain,(
% 0.19/0.50    ( ! [X0,X1] : (v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | ~r2_hidden(X1,X0)) )),
% 0.19/0.50    inference(resolution,[],[f70,f69])).
% 0.19/0.50  fof(f157,plain,(
% 0.19/0.50    ~m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1)) | m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(sK1)))),k1_zfmisc_1(sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f155,f54])).
% 0.19/0.50  fof(f155,plain,(
% 0.19/0.50    m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(sK1)))),k1_zfmisc_1(sK1)) | ~m1_subset_1(k1_tarski(sK3(sK1)),k1_zfmisc_1(sK1)) | v1_xboole_0(k1_tarski(sK3(sK1)))),
% 0.19/0.50    inference(resolution,[],[f154,f78])).
% 0.19/0.50  fof(f154,plain,(
% 0.19/0.50    ~m1_subset_1(sK3(k1_tarski(sK3(sK1))),sK1) | m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(sK1)))),k1_zfmisc_1(sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f152,f48])).
% 0.19/0.50  fof(f152,plain,(
% 0.19/0.50    m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(sK1)))),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK3(k1_tarski(sK3(sK1))),sK1) | v1_xboole_0(sK1)),
% 0.19/0.50    inference(superposition,[],[f71,f150])).
% 0.19/0.50  fof(f150,plain,(
% 0.19/0.50    k6_domain_1(sK1,sK3(k1_tarski(sK3(sK1)))) = k1_tarski(sK3(k1_tarski(sK3(sK1))))),
% 0.19/0.50    inference(subsumption_resolution,[],[f149,f48])).
% 0.19/0.50  fof(f149,plain,(
% 0.19/0.50    k6_domain_1(sK1,sK3(k1_tarski(sK3(sK1)))) = k1_tarski(sK3(k1_tarski(sK3(sK1)))) | v1_xboole_0(sK1)),
% 0.19/0.50    inference(resolution,[],[f145,f67])).
% 0.19/0.50  fof(f145,plain,(
% 0.19/0.50    ~r2_hidden(sK3(sK1),sK1) | k6_domain_1(sK1,sK3(k1_tarski(sK3(sK1)))) = k1_tarski(sK3(k1_tarski(sK3(sK1))))),
% 0.19/0.50    inference(resolution,[],[f132,f69])).
% 0.19/0.50  fof(f132,plain,(
% 0.19/0.50    ~m1_subset_1(sK3(sK1),sK1) | k6_domain_1(sK1,sK3(k1_tarski(sK3(sK1)))) = k1_tarski(sK3(k1_tarski(sK3(sK1))))),
% 0.19/0.50    inference(subsumption_resolution,[],[f128,f54])).
% 0.19/0.50  fof(f128,plain,(
% 0.19/0.50    k6_domain_1(sK1,sK3(k1_tarski(sK3(sK1)))) = k1_tarski(sK3(k1_tarski(sK3(sK1)))) | v1_xboole_0(k1_tarski(sK3(sK1))) | ~m1_subset_1(sK3(sK1),sK1)),
% 0.19/0.50    inference(resolution,[],[f84,f96])).
% 0.19/0.50  fof(f357,plain,(
% 0.19/0.50    ( ! [X0] : (~r1_tarski(X0,sK1) | v1_xboole_0(X0) | sK1 = u1_struct_0(sK2(sK0,sK1)) | sK1 = X0) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f356,f48])).
% 0.19/0.50  fof(f356,plain,(
% 0.19/0.50    ( ! [X0] : (sK1 = u1_struct_0(sK2(sK0,sK1)) | v1_xboole_0(sK1) | v1_xboole_0(X0) | ~r1_tarski(X0,sK1) | sK1 = X0) )),
% 0.19/0.50    inference(resolution,[],[f351,f55])).
% 0.19/0.50  fof(f55,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.19/0.50    inference(cnf_transformation,[],[f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.19/0.50    inference(flattening,[],[f23])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f14])).
% 0.19/0.50  fof(f14,axiom,(
% 0.19/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.19/0.50  fof(f270,plain,(
% 0.19/0.50    v2_tex_2(k1_tarski(sK3(k1_tarski(sK3(sK1)))),sK0) | ~m1_subset_1(sK3(k1_tarski(sK3(sK1))),u1_struct_0(sK0))),
% 0.19/0.50    inference(superposition,[],[f172,f269])).
% 0.19/0.50  fof(f269,plain,(
% 0.19/0.50    k1_tarski(sK3(k1_tarski(sK3(sK1)))) = k6_domain_1(u1_struct_0(sK0),sK3(k1_tarski(sK3(sK1))))),
% 0.19/0.50    inference(subsumption_resolution,[],[f267,f48])).
% 0.19/0.50  fof(f267,plain,(
% 0.19/0.50    k1_tarski(sK3(k1_tarski(sK3(sK1)))) = k6_domain_1(u1_struct_0(sK0),sK3(k1_tarski(sK3(sK1)))) | v1_xboole_0(sK1)),
% 0.19/0.50    inference(resolution,[],[f147,f49])).
% 0.19/0.50  fof(f147,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tarski(sK3(k1_tarski(sK3(sK1)))) = k6_domain_1(u1_struct_0(sK0),sK3(k1_tarski(sK3(sK1)))) | v1_xboole_0(X0)) )),
% 0.19/0.50    inference(resolution,[],[f143,f59])).
% 0.19/0.50  fof(f143,plain,(
% 0.19/0.50    v1_xboole_0(u1_struct_0(sK0)) | k1_tarski(sK3(k1_tarski(sK3(sK1)))) = k6_domain_1(u1_struct_0(sK0),sK3(k1_tarski(sK3(sK1))))),
% 0.19/0.50    inference(subsumption_resolution,[],[f140,f54])).
% 0.19/0.50  fof(f140,plain,(
% 0.19/0.50    v1_xboole_0(u1_struct_0(sK0)) | k1_tarski(sK3(k1_tarski(sK3(sK1)))) = k6_domain_1(u1_struct_0(sK0),sK3(k1_tarski(sK3(sK1)))) | v1_xboole_0(k1_tarski(sK3(sK1)))),
% 0.19/0.50    inference(resolution,[],[f139,f84])).
% 0.19/0.50  fof(f172,plain,(
% 0.19/0.50    ( ! [X0] : (v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f171,f50])).
% 0.19/0.50  fof(f171,plain,(
% 0.19/0.50    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f170,f51])).
% 0.19/0.50  fof(f170,plain,(
% 0.19/0.50    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)) )),
% 0.19/0.50    inference(resolution,[],[f61,f53])).
% 0.19/0.50  fof(f61,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f33])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f32])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f16])).
% 0.19/0.50  fof(f16,axiom,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 0.19/0.50  fof(f66,plain,(
% 0.19/0.50    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f37])).
% 0.19/0.50  fof(f37,plain,(
% 0.19/0.50    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f36])).
% 0.19/0.50  fof(f36,plain,(
% 0.19/0.50    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,axiom,(
% 0.19/0.50    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.19/0.50  fof(f527,plain,(
% 0.19/0.50    v2_tex_2(sK1,sK0) | ~m1_subset_1(sK3(sK1),u1_struct_0(sK0))),
% 0.19/0.50    inference(backward_demodulation,[],[f173,f508])).
% 0.19/0.50  fof(f508,plain,(
% 0.19/0.50    sK1 = k1_tarski(sK3(sK1))),
% 0.19/0.50    inference(forward_demodulation,[],[f507,f463])).
% 0.19/0.50  fof(f463,plain,(
% 0.19/0.50    sK1 = k1_tarski(sK3(k1_tarski(sK3(sK1))))),
% 0.19/0.50    inference(subsumption_resolution,[],[f455,f54])).
% 0.19/0.50  fof(f455,plain,(
% 0.19/0.50    v1_xboole_0(k1_tarski(sK3(k1_tarski(sK3(sK1))))) | sK1 = k1_tarski(sK3(k1_tarski(sK3(sK1))))),
% 0.19/0.50    inference(resolution,[],[f452,f166])).
% 0.19/0.50  fof(f452,plain,(
% 0.19/0.50    ( ! [X0] : (~r1_tarski(X0,sK1) | v1_xboole_0(X0) | sK1 = X0) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f451,f48])).
% 0.19/0.50  fof(f451,plain,(
% 0.19/0.50    ( ! [X0] : (v1_xboole_0(sK1) | v1_xboole_0(X0) | ~r1_tarski(X0,sK1) | sK1 = X0) )),
% 0.19/0.50    inference(resolution,[],[f449,f55])).
% 0.19/0.50  fof(f507,plain,(
% 0.19/0.50    sK1 = k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1))))))),
% 0.19/0.50    inference(subsumption_resolution,[],[f457,f54])).
% 0.19/0.50  fof(f457,plain,(
% 0.19/0.50    v1_xboole_0(k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1))))))) | sK1 = k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1))))))),
% 0.19/0.50    inference(resolution,[],[f452,f186])).
% 0.19/0.50  fof(f186,plain,(
% 0.19/0.50    r1_tarski(k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))),sK1)),
% 0.19/0.50    inference(resolution,[],[f184,f72])).
% 0.19/0.50  fof(f184,plain,(
% 0.19/0.50    m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))),k1_zfmisc_1(sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f183,f54])).
% 0.19/0.50  fof(f183,plain,(
% 0.19/0.50    m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))),k1_zfmisc_1(sK1)) | v1_xboole_0(k1_tarski(sK3(k1_tarski(sK3(sK1)))))),
% 0.19/0.50    inference(subsumption_resolution,[],[f181,f164])).
% 0.19/0.50  fof(f181,plain,(
% 0.19/0.50    m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))),k1_zfmisc_1(sK1)) | ~m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(sK1)))),k1_zfmisc_1(sK1)) | v1_xboole_0(k1_tarski(sK3(k1_tarski(sK3(sK1)))))),
% 0.19/0.50    inference(resolution,[],[f177,f78])).
% 0.19/0.50  fof(f177,plain,(
% 0.19/0.50    ~m1_subset_1(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1))))),sK1) | m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))),k1_zfmisc_1(sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f175,f48])).
% 0.19/0.50  fof(f175,plain,(
% 0.19/0.50    m1_subset_1(k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1))))),sK1) | v1_xboole_0(sK1)),
% 0.19/0.50    inference(superposition,[],[f71,f168])).
% 0.19/0.50  fof(f168,plain,(
% 0.19/0.50    k6_domain_1(sK1,sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))) = k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1))))))),
% 0.19/0.50    inference(subsumption_resolution,[],[f165,f54])).
% 0.19/0.50  fof(f165,plain,(
% 0.19/0.50    k6_domain_1(sK1,sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))) = k1_tarski(sK3(k1_tarski(sK3(k1_tarski(sK3(sK1)))))) | v1_xboole_0(k1_tarski(sK3(k1_tarski(sK3(sK1)))))),
% 0.19/0.50    inference(resolution,[],[f164,f84])).
% 0.19/0.50  fof(f173,plain,(
% 0.19/0.50    v2_tex_2(k1_tarski(sK3(sK1)),sK0) | ~m1_subset_1(sK3(sK1),u1_struct_0(sK0))),
% 0.19/0.50    inference(superposition,[],[f172,f133])).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (13680)------------------------------
% 0.19/0.50  % (13680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (13680)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (13680)Memory used [KB]: 6652
% 0.19/0.50  % (13680)Time elapsed: 0.115 s
% 0.19/0.50  % (13680)------------------------------
% 0.19/0.50  % (13680)------------------------------
% 0.19/0.50  % (13690)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.51  % (13673)Success in time 0.167 s
%------------------------------------------------------------------------------
