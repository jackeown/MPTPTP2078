%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  197 (2123 expanded)
%              Number of leaves         :   25 ( 570 expanded)
%              Depth                    :   33
%              Number of atoms          :  660 (13626 expanded)
%              Number of equality atoms :   97 (3037 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f580,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f90,f130,f259,f279,f337,f466,f488,f540,f544,f579])).

fof(f579,plain,
    ( spl2_2
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f578])).

fof(f578,plain,
    ( $false
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f577,f88])).

fof(f88,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl2_2
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f577,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f349,f125])).

fof(f125,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl2_3
  <=> u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f349,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f348,f115])).

fof(f115,plain,(
    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f114,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f114,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f113,f51])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f113,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f97,f52])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f97,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f53,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f348,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f149,f118])).

fof(f118,plain,(
    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f117,f50])).

fof(f117,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f116,f51])).

fof(f116,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f98,f52])).

fof(f98,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f53,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f149,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) ),
    inference(global_subsumption,[],[f143,f148])).

fof(f148,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f137,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

% (28543)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f137,plain,(
    v1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f136,f50])).

fof(f136,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f135,f51])).

fof(f135,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f102,f52])).

fof(f102,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f53,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f143,plain,(
    l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f142,f50])).

fof(f142,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f141,f51])).

fof(f141,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f104,f52])).

fof(f104,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f53,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f544,plain,
    ( spl2_4
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f543,f82,f127])).

fof(f127,plain,
    ( spl2_4
  <=> r2_hidden(sK1,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f82,plain,
    ( spl2_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f543,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f94,f52])).

% (28541)Refutation not found, incomplete strategy% (28541)------------------------------
% (28541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f94,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f53,f62])).

% (28541)Termination reason: Refutation not found, incomplete strategy

% (28541)Memory used [KB]: 10618
% (28541)Time elapsed: 0.091 s
% (28541)------------------------------
% (28541)------------------------------
fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f540,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(avatar_contradiction_clause,[],[f539])).

fof(f539,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f538,f50])).

fof(f538,plain,
    ( v2_struct_0(sK0)
    | spl2_1
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f537,f51])).

fof(f537,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl2_1
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f536,f52])).

fof(f536,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl2_1
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f535,f53])).

fof(f535,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl2_1
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f534,f109])).

fof(f109,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | spl2_1 ),
    inference(subsumption_resolution,[],[f108,f52])).

fof(f108,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f95,f84])).

fof(f84,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f95,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f53,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f534,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(trivial_inequality_removal,[],[f533])).

fof(f533,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(superposition,[],[f68,f528])).

fof(f528,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(backward_demodulation,[],[f118,f527])).

fof(f527,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(backward_demodulation,[],[f501,f514])).

fof(f514,plain,
    ( k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0))
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f513,f87])).

fof(f87,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f513,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK0))
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f512,f268])).

fof(f268,plain,(
    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f267,f50])).

fof(f267,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f266,f51])).

fof(f266,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f239,f52])).

fof(f239,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f234,f65])).

fof(f234,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f147,f162])).

fof(f162,plain,(
    m2_connsp_2(u1_struct_0(sK0),sK0,sK1) ),
    inference(backward_demodulation,[],[f112,f92])).

fof(f92,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f91,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f91,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f52,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f112,plain,(
    m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(subsumption_resolution,[],[f111,f50])).

fof(f111,plain,
    ( m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f110,f51])).

fof(f110,plain,
    ( m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f96,f52])).

fof(f96,plain,
    ( m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f53,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m2_connsp_2(k2_struct_0(X0),X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m2_connsp_2(k2_struct_0(X0),X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m2_connsp_2(k2_struct_0(X0),X0,X1)
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
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

fof(f147,plain,(
    ! [X2] :
      ( ~ m2_connsp_2(X2,sK0,sK1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f146,f51])).

fof(f146,plain,(
    ! [X2] :
      ( ~ m2_connsp_2(X2,sK0,sK1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f106,f52])).

fof(f106,plain,(
    ! [X2] :
      ( ~ m2_connsp_2(X2,sK0,sK1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f53,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X2] :
          ( m2_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_connsp_2)).

fof(f512,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(sK0))
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f321,f501])).

fof(f321,plain,(
    k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))) ),
    inference(global_subsumption,[],[f292,f320])).

fof(f320,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))))
    | ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(resolution,[],[f286,f60])).

fof(f286,plain,(
    v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f285,f50])).

fof(f285,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f284,f51])).

fof(f284,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f244,f52])).

fof(f244,plain,
    ( v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f234,f71])).

fof(f292,plain,(
    l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f291,f50])).

fof(f291,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f290,f51])).

fof(f290,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f246,f52])).

fof(f246,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f234,f73])).

fof(f501,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ spl2_17 ),
    inference(backward_demodulation,[],[f271,f278])).

fof(f278,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl2_17
  <=> u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f271,plain,(
    k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f270,f50])).

fof(f270,plain,
    ( k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f269,f51])).

fof(f269,plain,
    ( k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f240,f52])).

fof(f240,plain,
    ( k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f234,f66])).

fof(f68,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f488,plain,
    ( spl2_16
    | ~ spl2_21 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | spl2_16
    | ~ spl2_21 ),
    inference(subsumption_resolution,[],[f486,f258])).

fof(f258,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | spl2_16 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl2_16
  <=> v3_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f486,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl2_21 ),
    inference(backward_demodulation,[],[f294,f336])).

fof(f336,plain,
    ( u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl2_21
  <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f294,plain,(
    v3_pre_topc(k1_tops_1(sK0,u1_struct_0(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f293,f51])).

fof(f293,plain,
    ( v3_pre_topc(k1_tops_1(sK0,u1_struct_0(sK0)),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f247,f52])).

fof(f247,plain,
    ( v3_pre_topc(k1_tops_1(sK0,u1_struct_0(sK0)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f234,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f466,plain,(
    spl2_20 ),
    inference(avatar_contradiction_clause,[],[f465])).

fof(f465,plain,
    ( $false
    | spl2_20 ),
    inference(subsumption_resolution,[],[f464,f234])).

fof(f464,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_20 ),
    inference(subsumption_resolution,[],[f462,f332])).

fof(f332,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k1_tops_1(sK0,u1_struct_0(sK0)))
    | spl2_20 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl2_20
  <=> r1_tarski(u1_struct_0(sK0),k1_tops_1(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f462,plain,
    ( r1_tarski(u1_struct_0(sK0),k1_tops_1(sK0,u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f281,f265])).

fof(f265,plain,(
    m2_connsp_2(u1_struct_0(sK0),sK0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f264,f92])).

fof(f264,plain,(
    m2_connsp_2(k2_struct_0(sK0),sK0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f263,f50])).

fof(f263,plain,
    ( m2_connsp_2(k2_struct_0(sK0),sK0,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f262,f51])).

fof(f262,plain,
    ( m2_connsp_2(k2_struct_0(sK0),sK0,u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f238,f52])).

fof(f238,plain,
    ( m2_connsp_2(k2_struct_0(sK0),sK0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f234,f64])).

% (28545)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f281,plain,(
    ! [X0] :
      ( ~ m2_connsp_2(u1_struct_0(sK0),sK0,X0)
      | r1_tarski(X0,k1_tops_1(sK0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f280,f51])).

fof(f280,plain,(
    ! [X0] :
      ( ~ m2_connsp_2(u1_struct_0(sK0),sK0,X0)
      | r1_tarski(X0,k1_tops_1(sK0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f242,f52])).

fof(f242,plain,(
    ! [X0] :
      ( ~ m2_connsp_2(u1_struct_0(sK0),sK0,X0)
      | r1_tarski(X0,k1_tops_1(sK0,u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f234,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_connsp_2(X2,X0,X1)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f337,plain,
    ( ~ spl2_20
    | spl2_21 ),
    inference(avatar_split_clause,[],[f328,f334,f330])).

fof(f328,plain,
    ( u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ r1_tarski(u1_struct_0(sK0),k1_tops_1(sK0,u1_struct_0(sK0))) ),
    inference(resolution,[],[f249,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f249,plain,(
    r1_tarski(k1_tops_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f235,f52])).

fof(f235,plain,
    ( r1_tarski(k1_tops_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f234,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f279,plain,
    ( spl2_17
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f274,f252,f276])).

fof(f252,plain,
    ( spl2_15
  <=> r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f274,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f273,f50])).

fof(f273,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f272,f51])).

fof(f272,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f241,f52])).

fof(f241,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f234,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f259,plain,
    ( spl2_15
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f250,f256,f252])).

fof(f250,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f236,f52])).

fof(f236,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f234,f62])).

fof(f130,plain,
    ( spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f121,f127,f123])).

fof(f121,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f120,f50])).

fof(f120,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f119,f51])).

fof(f119,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f99,f52])).

% (28552)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f99,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f53,f67])).

fof(f90,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f54,f86,f82])).

fof(f54,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f55,f86,f82])).

fof(f55,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:19:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (28558)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.49  % (28542)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (28542)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (28547)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (28547)Refutation not found, incomplete strategy% (28547)------------------------------
% 0.22/0.50  % (28547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28547)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (28547)Memory used [KB]: 10618
% 0.22/0.50  % (28547)Time elapsed: 0.095 s
% 0.22/0.50  % (28547)------------------------------
% 0.22/0.50  % (28547)------------------------------
% 0.22/0.51  % (28541)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f580,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f89,f90,f130,f259,f279,f337,f466,f488,f540,f544,f579])).
% 0.22/0.51  fof(f579,plain,(
% 0.22/0.51    spl2_2 | ~spl2_3),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f578])).
% 0.22/0.51  fof(f578,plain,(
% 0.22/0.51    $false | (spl2_2 | ~spl2_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f577,f88])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | spl2_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    spl2_2 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.51  fof(f577,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~spl2_3),
% 0.22/0.51    inference(forward_demodulation,[],[f349,f125])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | ~spl2_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f123])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    spl2_3 <=> u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.51  fof(f349,plain,(
% 0.22/0.51    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),
% 0.22/0.51    inference(forward_demodulation,[],[f348,f115])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f114,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.22/0.51    inference(negated_conjecture,[],[f16])).
% 0.22/0.51  fof(f16,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f113,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    v2_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f97,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f53,f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f348,plain,(
% 0.22/0.51    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),k5_tmap_1(sK0,sK1))),
% 0.22/0.51    inference(forward_demodulation,[],[f149,f118])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f117,f50])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f116,f51])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f98,f52])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f53,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1)))),
% 0.22/0.51    inference(global_subsumption,[],[f143,f148])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.22/0.51    inference(resolution,[],[f137,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  % (28543)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    v1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f136,f50])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    v1_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f135,f51])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    v1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f102,f52])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    v1_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f53,f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f142,f50])).
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    l1_pre_topc(k6_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f141,f51])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f104,f52])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f53,f73])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | l1_pre_topc(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f544,plain,(
% 0.22/0.51    spl2_4 | ~spl2_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f543,f82,f127])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    spl2_4 <=> r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    spl2_1 <=> v3_pre_topc(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.51  fof(f543,plain,(
% 0.22/0.51    ~v3_pre_topc(sK1,sK0) | r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f94,f52])).
% 0.22/0.51  % (28541)Refutation not found, incomplete strategy% (28541)------------------------------
% 0.22/0.51  % (28541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    ~v3_pre_topc(sK1,sK0) | r2_hidden(sK1,u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f53,f62])).
% 0.22/0.51  % (28541)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28541)Memory used [KB]: 10618
% 0.22/0.51  % (28541)Time elapsed: 0.091 s
% 0.22/0.51  % (28541)------------------------------
% 0.22/0.51  % (28541)------------------------------
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.22/0.51  fof(f540,plain,(
% 0.22/0.51    spl2_1 | ~spl2_2 | ~spl2_17),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f539])).
% 0.22/0.51  fof(f539,plain,(
% 0.22/0.51    $false | (spl2_1 | ~spl2_2 | ~spl2_17)),
% 0.22/0.51    inference(subsumption_resolution,[],[f538,f50])).
% 0.22/0.51  fof(f538,plain,(
% 0.22/0.51    v2_struct_0(sK0) | (spl2_1 | ~spl2_2 | ~spl2_17)),
% 0.22/0.51    inference(subsumption_resolution,[],[f537,f51])).
% 0.22/0.51  fof(f537,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl2_1 | ~spl2_2 | ~spl2_17)),
% 0.22/0.51    inference(subsumption_resolution,[],[f536,f52])).
% 0.22/0.51  fof(f536,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl2_1 | ~spl2_2 | ~spl2_17)),
% 0.22/0.51    inference(subsumption_resolution,[],[f535,f53])).
% 0.22/0.51  fof(f535,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl2_1 | ~spl2_2 | ~spl2_17)),
% 0.22/0.51    inference(subsumption_resolution,[],[f534,f109])).
% 1.15/0.51  fof(f109,plain,(
% 1.15/0.51    ~r2_hidden(sK1,u1_pre_topc(sK0)) | spl2_1),
% 1.15/0.51    inference(subsumption_resolution,[],[f108,f52])).
% 1.15/0.51  fof(f108,plain,(
% 1.15/0.51    ~r2_hidden(sK1,u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | spl2_1),
% 1.15/0.51    inference(subsumption_resolution,[],[f95,f84])).
% 1.15/0.51  fof(f84,plain,(
% 1.15/0.51    ~v3_pre_topc(sK1,sK0) | spl2_1),
% 1.15/0.51    inference(avatar_component_clause,[],[f82])).
% 1.15/0.51  fof(f95,plain,(
% 1.15/0.51    ~r2_hidden(sK1,u1_pre_topc(sK0)) | v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.15/0.51    inference(resolution,[],[f53,f63])).
% 1.15/0.51  fof(f63,plain,(
% 1.15/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.15/0.51    inference(cnf_transformation,[],[f45])).
% 1.15/0.51  fof(f534,plain,(
% 1.15/0.51    r2_hidden(sK1,u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl2_2 | ~spl2_17)),
% 1.15/0.51    inference(trivial_inequality_removal,[],[f533])).
% 1.15/0.51  fof(f533,plain,(
% 1.15/0.51    u1_pre_topc(sK0) != u1_pre_topc(sK0) | r2_hidden(sK1,u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl2_2 | ~spl2_17)),
% 1.15/0.51    inference(superposition,[],[f68,f528])).
% 1.15/0.51  fof(f528,plain,(
% 1.15/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | (~spl2_2 | ~spl2_17)),
% 1.15/0.51    inference(backward_demodulation,[],[f118,f527])).
% 1.15/0.51  fof(f527,plain,(
% 1.15/0.51    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,sK1)) | (~spl2_2 | ~spl2_17)),
% 1.15/0.51    inference(backward_demodulation,[],[f501,f514])).
% 1.15/0.51  fof(f514,plain,(
% 1.15/0.51    k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0)) | (~spl2_2 | ~spl2_17)),
% 1.15/0.51    inference(forward_demodulation,[],[f513,f87])).
% 1.15/0.51  fof(f87,plain,(
% 1.15/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~spl2_2),
% 1.15/0.51    inference(avatar_component_clause,[],[f86])).
% 1.15/0.51  fof(f513,plain,(
% 1.15/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK0)) | ~spl2_17),
% 1.15/0.51    inference(forward_demodulation,[],[f512,f268])).
% 1.15/0.51  fof(f268,plain,(
% 1.15/0.51    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 1.15/0.51    inference(subsumption_resolution,[],[f267,f50])).
% 1.15/0.51  fof(f267,plain,(
% 1.15/0.51    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.15/0.51    inference(subsumption_resolution,[],[f266,f51])).
% 1.15/0.51  fof(f266,plain,(
% 1.15/0.51    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.15/0.51    inference(subsumption_resolution,[],[f239,f52])).
% 1.15/0.51  fof(f239,plain,(
% 1.15/0.51    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.15/0.51    inference(resolution,[],[f234,f65])).
% 1.15/0.51  fof(f234,plain,(
% 1.15/0.51    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.15/0.51    inference(resolution,[],[f147,f162])).
% 1.15/0.51  fof(f162,plain,(
% 1.15/0.51    m2_connsp_2(u1_struct_0(sK0),sK0,sK1)),
% 1.15/0.51    inference(backward_demodulation,[],[f112,f92])).
% 1.15/0.51  fof(f92,plain,(
% 1.15/0.51    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.15/0.51    inference(resolution,[],[f91,f58])).
% 1.15/0.51  fof(f58,plain,(
% 1.15/0.51    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 1.15/0.51    inference(cnf_transformation,[],[f20])).
% 1.15/0.51  fof(f20,plain,(
% 1.15/0.51    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.15/0.51    inference(ennf_transformation,[],[f5])).
% 1.15/0.51  fof(f5,axiom,(
% 1.15/0.51    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 1.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.15/0.51  fof(f91,plain,(
% 1.15/0.51    l1_struct_0(sK0)),
% 1.15/0.51    inference(resolution,[],[f52,f59])).
% 1.15/0.51  fof(f59,plain,(
% 1.15/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.15/0.51    inference(cnf_transformation,[],[f21])).
% 1.15/0.51  fof(f21,plain,(
% 1.15/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.15/0.51    inference(ennf_transformation,[],[f7])).
% 1.15/0.51  fof(f7,axiom,(
% 1.15/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.15/0.51  fof(f112,plain,(
% 1.15/0.51    m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 1.15/0.51    inference(subsumption_resolution,[],[f111,f50])).
% 1.15/0.51  fof(f111,plain,(
% 1.15/0.51    m2_connsp_2(k2_struct_0(sK0),sK0,sK1) | v2_struct_0(sK0)),
% 1.15/0.51    inference(subsumption_resolution,[],[f110,f51])).
% 1.15/0.51  fof(f110,plain,(
% 1.15/0.51    m2_connsp_2(k2_struct_0(sK0),sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.15/0.51    inference(subsumption_resolution,[],[f96,f52])).
% 1.15/0.51  fof(f96,plain,(
% 1.15/0.51    m2_connsp_2(k2_struct_0(sK0),sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.15/0.51    inference(resolution,[],[f53,f64])).
% 1.15/0.51  fof(f64,plain,(
% 1.15/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m2_connsp_2(k2_struct_0(X0),X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.15/0.51    inference(cnf_transformation,[],[f27])).
% 1.15/0.51  fof(f27,plain,(
% 1.15/0.51    ! [X0] : (! [X1] : (m2_connsp_2(k2_struct_0(X0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.15/0.51    inference(flattening,[],[f26])).
% 1.15/0.51  fof(f26,plain,(
% 1.15/0.51    ! [X0] : (! [X1] : (m2_connsp_2(k2_struct_0(X0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.15/0.51    inference(ennf_transformation,[],[f12])).
% 1.15/0.51  fof(f12,axiom,(
% 1.15/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 1.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).
% 1.15/0.51  fof(f147,plain,(
% 1.15/0.51    ( ! [X2] : (~m2_connsp_2(X2,sK0,sK1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.15/0.51    inference(subsumption_resolution,[],[f146,f51])).
% 1.15/0.51  fof(f146,plain,(
% 1.15/0.51    ( ! [X2] : (~m2_connsp_2(X2,sK0,sK1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) )),
% 1.15/0.51    inference(subsumption_resolution,[],[f106,f52])).
% 1.15/0.51  fof(f106,plain,(
% 1.15/0.51    ( ! [X2] : (~m2_connsp_2(X2,sK0,sK1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 1.15/0.51    inference(resolution,[],[f53,f75])).
% 1.15/0.51  fof(f75,plain,(
% 1.15/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.15/0.51    inference(cnf_transformation,[],[f39])).
% 1.15/0.51  fof(f39,plain,(
% 1.15/0.51    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.15/0.51    inference(flattening,[],[f38])).
% 1.15/0.51  fof(f38,plain,(
% 1.15/0.51    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.15/0.51    inference(ennf_transformation,[],[f11])).
% 1.15/0.51  fof(f11,axiom,(
% 1.15/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X2] : (m2_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_connsp_2)).
% 1.15/0.51  fof(f512,plain,(
% 1.15/0.51    k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(sK0)) | ~spl2_17),
% 1.15/0.51    inference(forward_demodulation,[],[f321,f501])).
% 1.15/0.51  fof(f321,plain,(
% 1.15/0.51    k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))))),
% 1.15/0.51    inference(global_subsumption,[],[f292,f320])).
% 1.15/0.51  fof(f320,plain,(
% 1.15/0.51    k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))) | ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 1.15/0.51    inference(resolution,[],[f286,f60])).
% 1.15/0.51  fof(f286,plain,(
% 1.15/0.51    v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 1.15/0.51    inference(subsumption_resolution,[],[f285,f50])).
% 1.15/0.51  fof(f285,plain,(
% 1.15/0.51    v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.15/0.51    inference(subsumption_resolution,[],[f284,f51])).
% 1.15/0.51  fof(f284,plain,(
% 1.15/0.51    v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.15/0.51    inference(subsumption_resolution,[],[f244,f52])).
% 1.15/0.51  fof(f244,plain,(
% 1.15/0.51    v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.15/0.51    inference(resolution,[],[f234,f71])).
% 1.15/0.51  fof(f292,plain,(
% 1.15/0.51    l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 1.15/0.51    inference(subsumption_resolution,[],[f291,f50])).
% 1.15/0.51  fof(f291,plain,(
% 1.15/0.51    l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.15/0.51    inference(subsumption_resolution,[],[f290,f51])).
% 1.15/0.51  fof(f290,plain,(
% 1.15/0.51    l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.15/0.51    inference(subsumption_resolution,[],[f246,f52])).
% 1.15/0.51  fof(f246,plain,(
% 1.15/0.51    l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.15/0.51    inference(resolution,[],[f234,f73])).
% 1.15/0.51  fof(f501,plain,(
% 1.15/0.51    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | ~spl2_17),
% 1.15/0.51    inference(backward_demodulation,[],[f271,f278])).
% 1.15/0.51  fof(f278,plain,(
% 1.15/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) | ~spl2_17),
% 1.15/0.51    inference(avatar_component_clause,[],[f276])).
% 1.15/0.51  fof(f276,plain,(
% 1.15/0.51    spl2_17 <=> u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))),
% 1.15/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 1.15/0.51  fof(f271,plain,(
% 1.15/0.51    k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 1.15/0.51    inference(subsumption_resolution,[],[f270,f50])).
% 1.15/0.51  fof(f270,plain,(
% 1.15/0.51    k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.15/0.51    inference(subsumption_resolution,[],[f269,f51])).
% 1.15/0.51  fof(f269,plain,(
% 1.15/0.51    k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.15/0.51    inference(subsumption_resolution,[],[f240,f52])).
% 1.15/0.51  fof(f240,plain,(
% 1.15/0.51    k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.15/0.51    inference(resolution,[],[f234,f66])).
% 1.15/0.51  fof(f68,plain,(
% 1.15/0.51    ( ! [X0,X1] : (u1_pre_topc(X0) != k5_tmap_1(X0,X1) | r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.15/0.51    inference(cnf_transformation,[],[f46])).
% 1.15/0.51  fof(f46,plain,(
% 1.15/0.51    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.15/0.51    inference(nnf_transformation,[],[f31])).
% 1.15/0.51  fof(f31,plain,(
% 1.15/0.51    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.15/0.51    inference(flattening,[],[f30])).
% 1.15/0.51  fof(f30,plain,(
% 1.15/0.51    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.15/0.51    inference(ennf_transformation,[],[f14])).
% 1.15/0.51  fof(f14,axiom,(
% 1.15/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 1.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).
% 1.15/0.51  fof(f488,plain,(
% 1.15/0.51    spl2_16 | ~spl2_21),
% 1.15/0.51    inference(avatar_contradiction_clause,[],[f487])).
% 1.15/0.51  fof(f487,plain,(
% 1.15/0.51    $false | (spl2_16 | ~spl2_21)),
% 1.15/0.51    inference(subsumption_resolution,[],[f486,f258])).
% 1.15/0.51  fof(f258,plain,(
% 1.15/0.51    ~v3_pre_topc(u1_struct_0(sK0),sK0) | spl2_16),
% 1.15/0.51    inference(avatar_component_clause,[],[f256])).
% 1.15/0.51  fof(f256,plain,(
% 1.15/0.51    spl2_16 <=> v3_pre_topc(u1_struct_0(sK0),sK0)),
% 1.15/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.15/0.51  fof(f486,plain,(
% 1.15/0.51    v3_pre_topc(u1_struct_0(sK0),sK0) | ~spl2_21),
% 1.15/0.51    inference(backward_demodulation,[],[f294,f336])).
% 1.15/0.51  fof(f336,plain,(
% 1.15/0.51    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) | ~spl2_21),
% 1.15/0.51    inference(avatar_component_clause,[],[f334])).
% 1.15/0.51  fof(f334,plain,(
% 1.15/0.51    spl2_21 <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))),
% 1.15/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 1.15/0.51  fof(f294,plain,(
% 1.15/0.51    v3_pre_topc(k1_tops_1(sK0,u1_struct_0(sK0)),sK0)),
% 1.15/0.51    inference(subsumption_resolution,[],[f293,f51])).
% 1.15/0.51  fof(f293,plain,(
% 1.15/0.51    v3_pre_topc(k1_tops_1(sK0,u1_struct_0(sK0)),sK0) | ~v2_pre_topc(sK0)),
% 1.15/0.51    inference(subsumption_resolution,[],[f247,f52])).
% 1.15/0.51  fof(f247,plain,(
% 1.15/0.51    v3_pre_topc(k1_tops_1(sK0,u1_struct_0(sK0)),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.15/0.51    inference(resolution,[],[f234,f74])).
% 1.15/0.51  fof(f74,plain,(
% 1.15/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.15/0.51    inference(cnf_transformation,[],[f37])).
% 1.15/0.51  fof(f37,plain,(
% 1.15/0.51    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.15/0.51    inference(flattening,[],[f36])).
% 1.15/0.51  fof(f36,plain,(
% 1.15/0.51    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.15/0.51    inference(ennf_transformation,[],[f8])).
% 1.15/0.51  fof(f8,axiom,(
% 1.15/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.15/0.51  fof(f466,plain,(
% 1.15/0.51    spl2_20),
% 1.15/0.51    inference(avatar_contradiction_clause,[],[f465])).
% 1.15/0.51  fof(f465,plain,(
% 1.15/0.51    $false | spl2_20),
% 1.15/0.51    inference(subsumption_resolution,[],[f464,f234])).
% 1.15/0.51  fof(f464,plain,(
% 1.15/0.51    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_20),
% 1.15/0.51    inference(subsumption_resolution,[],[f462,f332])).
% 1.15/0.51  fof(f332,plain,(
% 1.15/0.51    ~r1_tarski(u1_struct_0(sK0),k1_tops_1(sK0,u1_struct_0(sK0))) | spl2_20),
% 1.15/0.51    inference(avatar_component_clause,[],[f330])).
% 1.15/0.51  fof(f330,plain,(
% 1.15/0.51    spl2_20 <=> r1_tarski(u1_struct_0(sK0),k1_tops_1(sK0,u1_struct_0(sK0)))),
% 1.15/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 1.15/0.51  fof(f462,plain,(
% 1.15/0.51    r1_tarski(u1_struct_0(sK0),k1_tops_1(sK0,u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.15/0.51    inference(resolution,[],[f281,f265])).
% 1.15/0.51  fof(f265,plain,(
% 1.15/0.51    m2_connsp_2(u1_struct_0(sK0),sK0,u1_struct_0(sK0))),
% 1.15/0.51    inference(forward_demodulation,[],[f264,f92])).
% 1.15/0.51  fof(f264,plain,(
% 1.15/0.51    m2_connsp_2(k2_struct_0(sK0),sK0,u1_struct_0(sK0))),
% 1.15/0.51    inference(subsumption_resolution,[],[f263,f50])).
% 1.15/0.51  fof(f263,plain,(
% 1.15/0.51    m2_connsp_2(k2_struct_0(sK0),sK0,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 1.15/0.51    inference(subsumption_resolution,[],[f262,f51])).
% 1.15/0.51  fof(f262,plain,(
% 1.15/0.51    m2_connsp_2(k2_struct_0(sK0),sK0,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.15/0.51    inference(subsumption_resolution,[],[f238,f52])).
% 1.15/0.51  fof(f238,plain,(
% 1.15/0.51    m2_connsp_2(k2_struct_0(sK0),sK0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.15/0.51    inference(resolution,[],[f234,f64])).
% 1.15/0.51  % (28545)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.15/0.51  fof(f281,plain,(
% 1.15/0.51    ( ! [X0] : (~m2_connsp_2(u1_struct_0(sK0),sK0,X0) | r1_tarski(X0,k1_tops_1(sK0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.15/0.51    inference(subsumption_resolution,[],[f280,f51])).
% 1.15/0.51  fof(f280,plain,(
% 1.15/0.51    ( ! [X0] : (~m2_connsp_2(u1_struct_0(sK0),sK0,X0) | r1_tarski(X0,k1_tops_1(sK0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) )),
% 1.15/0.51    inference(subsumption_resolution,[],[f242,f52])).
% 1.15/0.51  fof(f242,plain,(
% 1.15/0.51    ( ! [X0] : (~m2_connsp_2(u1_struct_0(sK0),sK0,X0) | r1_tarski(X0,k1_tops_1(sK0,u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 1.15/0.51    inference(resolution,[],[f234,f69])).
% 1.15/0.51  fof(f69,plain,(
% 1.15/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.15/0.51    inference(cnf_transformation,[],[f47])).
% 1.15/0.51  fof(f47,plain,(
% 1.15/0.51    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.15/0.51    inference(nnf_transformation,[],[f33])).
% 1.15/0.51  fof(f33,plain,(
% 1.15/0.51    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.15/0.51    inference(flattening,[],[f32])).
% 1.15/0.51  fof(f32,plain,(
% 1.15/0.51    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.15/0.51    inference(ennf_transformation,[],[f10])).
% 1.15/0.51  fof(f10,axiom,(
% 1.15/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).
% 1.15/0.51  fof(f337,plain,(
% 1.15/0.51    ~spl2_20 | spl2_21),
% 1.15/0.51    inference(avatar_split_clause,[],[f328,f334,f330])).
% 1.15/0.51  fof(f328,plain,(
% 1.15/0.51    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) | ~r1_tarski(u1_struct_0(sK0),k1_tops_1(sK0,u1_struct_0(sK0)))),
% 1.15/0.51    inference(resolution,[],[f249,f78])).
% 1.15/0.51  fof(f78,plain,(
% 1.15/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.15/0.51    inference(cnf_transformation,[],[f49])).
% 1.15/0.51  fof(f49,plain,(
% 1.15/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.15/0.51    inference(flattening,[],[f48])).
% 1.15/0.51  fof(f48,plain,(
% 1.15/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.15/0.51    inference(nnf_transformation,[],[f1])).
% 1.15/0.51  fof(f1,axiom,(
% 1.15/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.15/0.51  fof(f249,plain,(
% 1.15/0.51    r1_tarski(k1_tops_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 1.15/0.51    inference(subsumption_resolution,[],[f235,f52])).
% 1.15/0.51  fof(f235,plain,(
% 1.15/0.51    r1_tarski(k1_tops_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 1.15/0.51    inference(resolution,[],[f234,f61])).
% 1.15/0.51  fof(f61,plain,(
% 1.15/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 1.15/0.51    inference(cnf_transformation,[],[f24])).
% 1.15/0.51  fof(f24,plain,(
% 1.15/0.51    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.15/0.51    inference(ennf_transformation,[],[f9])).
% 1.15/0.51  fof(f9,axiom,(
% 1.15/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.15/0.51  fof(f279,plain,(
% 1.15/0.51    spl2_17 | ~spl2_15),
% 1.15/0.51    inference(avatar_split_clause,[],[f274,f252,f276])).
% 1.15/0.51  fof(f252,plain,(
% 1.15/0.51    spl2_15 <=> r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))),
% 1.15/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 1.15/0.51  fof(f274,plain,(
% 1.15/0.51    ~r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))),
% 1.15/0.51    inference(subsumption_resolution,[],[f273,f50])).
% 1.15/0.51  fof(f273,plain,(
% 1.15/0.51    ~r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 1.15/0.51    inference(subsumption_resolution,[],[f272,f51])).
% 1.15/0.51  fof(f272,plain,(
% 1.15/0.51    ~r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.15/0.51    inference(subsumption_resolution,[],[f241,f52])).
% 1.15/0.51  fof(f241,plain,(
% 1.15/0.51    ~r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.15/0.51    inference(resolution,[],[f234,f67])).
% 1.15/0.51  fof(f67,plain,(
% 1.15/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.15/0.51    inference(cnf_transformation,[],[f46])).
% 1.15/0.51  fof(f259,plain,(
% 1.15/0.51    spl2_15 | ~spl2_16),
% 1.15/0.51    inference(avatar_split_clause,[],[f250,f256,f252])).
% 1.15/0.51  fof(f250,plain,(
% 1.15/0.51    ~v3_pre_topc(u1_struct_0(sK0),sK0) | r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))),
% 1.15/0.51    inference(subsumption_resolution,[],[f236,f52])).
% 1.15/0.51  fof(f236,plain,(
% 1.15/0.51    ~v3_pre_topc(u1_struct_0(sK0),sK0) | r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 1.15/0.51    inference(resolution,[],[f234,f62])).
% 1.15/0.51  fof(f130,plain,(
% 1.15/0.51    spl2_3 | ~spl2_4),
% 1.15/0.51    inference(avatar_split_clause,[],[f121,f127,f123])).
% 1.15/0.51  fof(f121,plain,(
% 1.15/0.51    ~r2_hidden(sK1,u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 1.15/0.51    inference(subsumption_resolution,[],[f120,f50])).
% 1.15/0.51  fof(f120,plain,(
% 1.15/0.51    ~r2_hidden(sK1,u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | v2_struct_0(sK0)),
% 1.15/0.51    inference(subsumption_resolution,[],[f119,f51])).
% 1.15/0.51  fof(f119,plain,(
% 1.15/0.51    ~r2_hidden(sK1,u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.15/0.51    inference(subsumption_resolution,[],[f99,f52])).
% 1.15/0.51  % (28552)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.15/0.51  fof(f99,plain,(
% 1.15/0.51    ~r2_hidden(sK1,u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.15/0.51    inference(resolution,[],[f53,f67])).
% 1.15/0.51  fof(f90,plain,(
% 1.15/0.51    spl2_1 | spl2_2),
% 1.15/0.51    inference(avatar_split_clause,[],[f54,f86,f82])).
% 1.15/0.51  fof(f54,plain,(
% 1.15/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 1.15/0.51    inference(cnf_transformation,[],[f44])).
% 1.15/0.51  fof(f89,plain,(
% 1.15/0.51    ~spl2_1 | ~spl2_2),
% 1.15/0.51    inference(avatar_split_clause,[],[f55,f86,f82])).
% 1.15/0.51  fof(f55,plain,(
% 1.15/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.15/0.51    inference(cnf_transformation,[],[f44])).
% 1.15/0.51  % SZS output end Proof for theBenchmark
% 1.15/0.51  % (28542)------------------------------
% 1.15/0.51  % (28542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.51  % (28542)Termination reason: Refutation
% 1.15/0.51  
% 1.15/0.51  % (28542)Memory used [KB]: 10874
% 1.15/0.51  % (28542)Time elapsed: 0.092 s
% 1.15/0.51  % (28542)------------------------------
% 1.15/0.51  % (28542)------------------------------
% 1.15/0.51  % (28560)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.15/0.51  % (28556)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.15/0.51  % (28540)Success in time 0.148 s
%------------------------------------------------------------------------------
