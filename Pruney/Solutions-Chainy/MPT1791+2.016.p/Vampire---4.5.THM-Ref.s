%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 859 expanded)
%              Number of leaves         :   25 ( 241 expanded)
%              Depth                    :   20
%              Number of atoms          :  783 (5270 expanded)
%              Number of equality atoms :   71 (1097 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f701,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f95,f134,f137,f272,f369,f436,f442,f444,f460,f563,f661,f666,f700])).

fof(f700,plain,
    ( spl5_14
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f699])).

fof(f699,plain,
    ( $false
    | spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f698,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k6_tmap_1(sK3,sK4)
      | ~ v3_pre_topc(sK4,sK3) )
    & ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4)
      | v3_pre_topc(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f36,f38,f37])).

fof(f37,plain,
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
          ( ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k6_tmap_1(sK3,X1)
            | ~ v3_pre_topc(X1,sK3) )
          & ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,X1)
            | v3_pre_topc(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k6_tmap_1(sK3,X1)
          | ~ v3_pre_topc(X1,sK3) )
        & ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,X1)
          | v3_pre_topc(X1,sK3) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k6_tmap_1(sK3,sK4)
        | ~ v3_pre_topc(sK4,sK3) )
      & ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4)
        | v3_pre_topc(sK4,sK3) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

% (22882)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f698,plain,
    ( v2_struct_0(sK3)
    | spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f697,f53])).

fof(f53,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f697,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f696,f54])).

fof(f54,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f696,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f695,f55])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f39])).

fof(f695,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f694,f440])).

fof(f440,plain,
    ( r2_hidden(sK4,u1_pre_topc(sK3))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl5_16
  <=> r2_hidden(sK4,u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f694,plain,
    ( ~ r2_hidden(sK4,u1_pre_topc(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl5_14 ),
    inference(trivial_inequality_removal,[],[f693])).

fof(f693,plain,
    ( u1_pre_topc(sK3) != u1_pre_topc(sK3)
    | ~ r2_hidden(sK4,u1_pre_topc(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl5_14 ),
    inference(superposition,[],[f692,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f692,plain,
    ( u1_pre_topc(sK3) != k5_tmap_1(sK3,sK4)
    | spl5_14 ),
    inference(subsumption_resolution,[],[f691,f52])).

fof(f691,plain,
    ( u1_pre_topc(sK3) != k5_tmap_1(sK3,sK4)
    | v2_struct_0(sK3)
    | spl5_14 ),
    inference(subsumption_resolution,[],[f690,f53])).

fof(f690,plain,
    ( u1_pre_topc(sK3) != k5_tmap_1(sK3,sK4)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl5_14 ),
    inference(subsumption_resolution,[],[f689,f54])).

fof(f689,plain,
    ( u1_pre_topc(sK3) != k5_tmap_1(sK3,sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl5_14 ),
    inference(subsumption_resolution,[],[f688,f55])).

fof(f688,plain,
    ( u1_pre_topc(sK3) != k5_tmap_1(sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl5_14 ),
    inference(superposition,[],[f363,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f363,plain,
    ( u1_pre_topc(sK3) != u1_pre_topc(k6_tmap_1(sK3,sK4))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl5_14
  <=> u1_pre_topc(sK3) = u1_pre_topc(k6_tmap_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f666,plain,
    ( spl5_16
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f665,f362,f439])).

fof(f665,plain,
    ( r2_hidden(sK4,u1_pre_topc(sK3))
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f664,f52])).

fof(f664,plain,
    ( r2_hidden(sK4,u1_pre_topc(sK3))
    | v2_struct_0(sK3)
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f663,f53])).

fof(f663,plain,
    ( r2_hidden(sK4,u1_pre_topc(sK3))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f662,f54])).

fof(f662,plain,
    ( r2_hidden(sK4,u1_pre_topc(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f647,f55])).

fof(f647,plain,
    ( r2_hidden(sK4,u1_pre_topc(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl5_14 ),
    inference(trivial_inequality_removal,[],[f644])).

fof(f644,plain,
    ( u1_pre_topc(sK3) != u1_pre_topc(sK3)
    | r2_hidden(sK4,u1_pre_topc(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl5_14 ),
    inference(superposition,[],[f68,f630])).

fof(f630,plain,
    ( u1_pre_topc(sK3) = k5_tmap_1(sK3,sK4)
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f629,f52])).

fof(f629,plain,
    ( u1_pre_topc(sK3) = k5_tmap_1(sK3,sK4)
    | v2_struct_0(sK3)
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f628,f53])).

fof(f628,plain,
    ( u1_pre_topc(sK3) = k5_tmap_1(sK3,sK4)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f627,f54])).

fof(f627,plain,
    ( u1_pre_topc(sK3) = k5_tmap_1(sK3,sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f609,f55])).

fof(f609,plain,
    ( u1_pre_topc(sK3) = k5_tmap_1(sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl5_14 ),
    inference(superposition,[],[f364,f66])).

fof(f364,plain,
    ( u1_pre_topc(sK3) = u1_pre_topc(k6_tmap_1(sK3,sK4))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f362])).

fof(f68,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f661,plain,
    ( spl5_2
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f660,f362,f91])).

fof(f91,plain,
    ( spl5_2
  <=> g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f660,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4)
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f659,f52])).

fof(f659,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4)
    | v2_struct_0(sK3)
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f658,f53])).

fof(f658,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f657,f54])).

fof(f657,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f645,f55])).

fof(f645,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl5_14 ),
    inference(superposition,[],[f64,f630])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

% (22873)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f563,plain,
    ( ~ spl5_11
    | spl5_15 ),
    inference(avatar_contradiction_clause,[],[f562])).

fof(f562,plain,
    ( $false
    | ~ spl5_11
    | spl5_15 ),
    inference(subsumption_resolution,[],[f560,f473])).

fof(f473,plain,
    ( ~ v1_tops_2(k5_tmap_1(sK3,sK4),sK3)
    | spl5_15 ),
    inference(subsumption_resolution,[],[f472,f52])).

fof(f472,plain,
    ( ~ v1_tops_2(k5_tmap_1(sK3,sK4),sK3)
    | v2_struct_0(sK3)
    | spl5_15 ),
    inference(subsumption_resolution,[],[f471,f53])).

fof(f471,plain,
    ( ~ v1_tops_2(k5_tmap_1(sK3,sK4),sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl5_15 ),
    inference(subsumption_resolution,[],[f470,f54])).

fof(f470,plain,
    ( ~ v1_tops_2(k5_tmap_1(sK3,sK4),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl5_15 ),
    inference(subsumption_resolution,[],[f469,f55])).

fof(f469,plain,
    ( ~ v1_tops_2(k5_tmap_1(sK3,sK4),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl5_15 ),
    inference(superposition,[],[f368,f66])).

fof(f368,plain,
    ( ~ v1_tops_2(u1_pre_topc(k6_tmap_1(sK3,sK4)),sK3)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl5_15
  <=> v1_tops_2(u1_pre_topc(k6_tmap_1(sK3,sK4)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f560,plain,
    ( v1_tops_2(k5_tmap_1(sK3,sK4),sK3)
    | ~ spl5_11 ),
    inference(resolution,[],[f559,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v1_tops_2(X1,X0) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
          & v1_tops_2(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v1_tops_2(X1,X0) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
          & v1_tops_2(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & v1_tops_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f559,plain,
    ( sP0(sK3,k5_tmap_1(sK3,sK4))
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f558,f52])).

fof(f558,plain,
    ( sP0(sK3,k5_tmap_1(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f557,f53])).

fof(f557,plain,
    ( sP0(sK3,k5_tmap_1(sK3,sK4))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f555,f54])).

fof(f555,plain,
    ( sP0(sK3,k5_tmap_1(sK3,sK4))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl5_11 ),
    inference(resolution,[],[f341,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | sP0(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( sP0(X0,X1)
            | ~ sP1(X0,X1) )
          & ( sP1(X0,X1)
            | ~ sP0(X0,X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP0(X0,X1)
        <=> sP1(X0,X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f27,f31,f30])).

fof(f31,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_compts_1)).

fof(f341,plain,
    ( sP1(sK3,k5_tmap_1(sK3,sK4))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl5_11
  <=> sP1(sK3,k5_tmap_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f460,plain,
    ( spl5_11
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f459])).

fof(f459,plain,
    ( $false
    | spl5_11
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f458,f52])).

fof(f458,plain,
    ( v2_struct_0(sK3)
    | spl5_11
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f457,f53])).

fof(f457,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl5_11
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f456,f54])).

fof(f456,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl5_11
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f455,f55])).

fof(f455,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl5_11
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f451,f342])).

fof(f342,plain,
    ( ~ sP1(sK3,k5_tmap_1(sK3,sK4))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f340])).

fof(f451,plain,
    ( sP1(sK3,k5_tmap_1(sK3,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl5_13 ),
    inference(superposition,[],[f349,f66])).

fof(f349,plain,
    ( sP1(sK3,u1_pre_topc(k6_tmap_1(sK3,sK4)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl5_13
  <=> sP1(sK3,u1_pre_topc(k6_tmap_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f444,plain,
    ( spl5_16
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f443,f87,f439])).

fof(f87,plain,
    ( spl5_1
  <=> v3_pre_topc(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f443,plain,
    ( ~ v3_pre_topc(sK4,sK3)
    | r2_hidden(sK4,u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f106,f54])).

fof(f106,plain,
    ( ~ v3_pre_topc(sK4,sK3)
    | r2_hidden(sK4,u1_pre_topc(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f59,f55])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f442,plain,
    ( spl5_1
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f437,f439,f87])).

fof(f437,plain,
    ( ~ r2_hidden(sK4,u1_pre_topc(sK3))
    | v3_pre_topc(sK4,sK3) ),
    inference(subsumption_resolution,[],[f112,f54])).

fof(f112,plain,
    ( ~ r2_hidden(sK4,u1_pre_topc(sK3))
    | v3_pre_topc(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f60,f55])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f436,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | spl5_13 ),
    inference(subsumption_resolution,[],[f434,f129])).

fof(f129,plain,
    ( l1_pre_topc(k6_tmap_1(sK3,sK4))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl5_3
  <=> l1_pre_topc(k6_tmap_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f434,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK3,sK4))
    | ~ spl5_2
    | spl5_13 ),
    inference(subsumption_resolution,[],[f433,f350])).

fof(f350,plain,
    ( ~ sP1(sK3,u1_pre_topc(k6_tmap_1(sK3,sK4)))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f348])).

fof(f433,plain,
    ( sP1(sK3,u1_pre_topc(k6_tmap_1(sK3,sK4)))
    | ~ l1_pre_topc(k6_tmap_1(sK3,sK4))
    | ~ spl5_2 ),
    inference(resolution,[],[f427,f150])).

fof(f150,plain,(
    ! [X0] :
      ( sP0(X0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f98,f149])).

fof(f149,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f148,f84])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
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

fof(f148,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0))
      | v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0))
      | v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f62,f58])).

fof(f58,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(f98,plain,(
    ! [X0] :
      ( sP0(X0,u1_pre_topc(X0))
      | ~ v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f74,f58])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | sP0(X0,X1)
      | ~ v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f427,plain,
    ( ! [X1] :
        ( ~ sP0(k6_tmap_1(sK3,sK4),X1)
        | sP1(sK3,X1) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f423,f72])).

fof(f423,plain,
    ( ! [X1] :
        ( sP1(sK3,X1)
        | ~ v1_tops_2(X1,k6_tmap_1(sK3,sK4))
        | ~ sP0(k6_tmap_1(sK3,sK4),X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f377,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f377,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK3,sK4)))))
        | sP1(sK3,X0)
        | ~ v1_tops_2(X0,k6_tmap_1(sK3,sK4)) )
    | ~ spl5_2 ),
    inference(superposition,[],[f71,f92])).

fof(f92,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | sP1(X0,X1)
      | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
          & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
          & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f369,plain,
    ( spl5_14
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f360,f262,f132,f91,f366,f348,f362])).

fof(f132,plain,
    ( spl5_4
  <=> ! [X5] :
        ( r1_tarski(X5,u1_pre_topc(k6_tmap_1(sK3,sK4)))
        | ~ sP1(sK3,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f262,plain,
    ( spl5_10
  <=> sP1(sK3,u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f360,plain,
    ( ~ v1_tops_2(u1_pre_topc(k6_tmap_1(sK3,sK4)),sK3)
    | ~ sP1(sK3,u1_pre_topc(k6_tmap_1(sK3,sK4)))
    | u1_pre_topc(sK3) = u1_pre_topc(k6_tmap_1(sK3,sK4))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f358,f263])).

fof(f263,plain,
    ( sP1(sK3,u1_pre_topc(sK3))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f262])).

fof(f358,plain,
    ( ~ v1_tops_2(u1_pre_topc(k6_tmap_1(sK3,sK4)),sK3)
    | ~ sP1(sK3,u1_pre_topc(k6_tmap_1(sK3,sK4)))
    | u1_pre_topc(sK3) = u1_pre_topc(k6_tmap_1(sK3,sK4))
    | ~ sP1(sK3,u1_pre_topc(sK3))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f253,f138])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_pre_topc(k6_tmap_1(sK3,sK4)),X0)
        | u1_pre_topc(k6_tmap_1(sK3,sK4)) = X0
        | ~ sP1(sK3,X0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f133,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f133,plain,
    ( ! [X5] :
        ( r1_tarski(X5,u1_pre_topc(k6_tmap_1(sK3,sK4)))
        | ~ sP1(sK3,X5) )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f253,plain,
    ( ! [X1] :
        ( r1_tarski(X1,u1_pre_topc(sK3))
        | ~ v1_tops_2(X1,sK3)
        | ~ sP1(sK3,X1) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f250,f54])).

fof(f250,plain,
    ( ! [X1] :
        ( ~ sP1(sK3,X1)
        | ~ v1_tops_2(X1,sK3)
        | r1_tarski(X1,u1_pre_topc(sK3))
        | ~ l1_pre_topc(sK3) )
    | ~ spl5_2 ),
    inference(resolution,[],[f248,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X1,X0)
      | r1_tarski(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f248,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
        | ~ sP1(sK3,X0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f247,f52])).

fof(f247,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
        | ~ sP1(sK3,X0)
        | v2_struct_0(sK3) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f246,f53])).

fof(f246,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
        | ~ sP1(sK3,X0)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f245,f54])).

fof(f245,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
        | ~ sP1(sK3,X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f231,f55])).

fof(f231,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
        | ~ sP1(sK3,X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl5_2 ),
    inference(superposition,[],[f104,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f104,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK3,sK4)))))
        | ~ sP1(sK3,X0) )
    | ~ spl5_2 ),
    inference(superposition,[],[f70,f92])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f272,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | spl5_10 ),
    inference(subsumption_resolution,[],[f270,f54])).

fof(f270,plain,
    ( ~ l1_pre_topc(sK3)
    | spl5_10 ),
    inference(resolution,[],[f269,f150])).

fof(f269,plain,
    ( ~ sP0(sK3,u1_pre_topc(sK3))
    | spl5_10 ),
    inference(subsumption_resolution,[],[f268,f52])).

fof(f268,plain,
    ( ~ sP0(sK3,u1_pre_topc(sK3))
    | v2_struct_0(sK3)
    | spl5_10 ),
    inference(subsumption_resolution,[],[f267,f53])).

fof(f267,plain,
    ( ~ sP0(sK3,u1_pre_topc(sK3))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl5_10 ),
    inference(subsumption_resolution,[],[f266,f54])).

fof(f266,plain,
    ( ~ sP0(sK3,u1_pre_topc(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl5_10 ),
    inference(resolution,[],[f264,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ sP0(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f264,plain,
    ( ~ sP1(sK3,u1_pre_topc(sK3))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f262])).

fof(f137,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f135,f118])).

fof(f118,plain,(
    sP2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f117,f52])).

fof(f117,plain,
    ( sP2(sK4,sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f116,f53])).

fof(f116,plain,
    ( sP2(sK4,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f115,f54])).

fof(f115,plain,
    ( sP2(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f80,f55])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f29,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

% (22876)Refutation not found, incomplete strategy% (22876)------------------------------
% (22876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22876)Termination reason: Refutation not found, incomplete strategy

% (22876)Memory used [KB]: 6140
% (22876)Time elapsed: 0.120 s
% (22876)------------------------------
% (22876)------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f135,plain,
    ( ~ sP2(sK4,sK3)
    | spl5_3 ),
    inference(resolution,[],[f130,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X1,X0))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X1,X0))
        & v2_pre_topc(k6_tmap_1(X1,X0))
        & v1_pre_topc(k6_tmap_1(X1,X0)) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f130,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK3,sK4))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f134,plain,
    ( ~ spl5_3
    | spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f126,f91,f132,f128])).

fof(f126,plain,
    ( ! [X5] :
        ( r1_tarski(X5,u1_pre_topc(k6_tmap_1(sK3,sK4)))
        | ~ l1_pre_topc(k6_tmap_1(sK3,sK4))
        | ~ sP1(sK3,X5) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f122,f97])).

fof(f97,plain,
    ( ! [X0] :
        ( v1_tops_2(X0,k6_tmap_1(sK3,sK4))
        | ~ sP1(sK3,X0) )
    | ~ spl5_2 ),
    inference(superposition,[],[f69,f92])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f122,plain,
    ( ! [X5] :
        ( ~ v1_tops_2(X5,k6_tmap_1(sK3,sK4))
        | r1_tarski(X5,u1_pre_topc(k6_tmap_1(sK3,sK4)))
        | ~ l1_pre_topc(k6_tmap_1(sK3,sK4))
        | ~ sP1(sK3,X5) )
    | ~ spl5_2 ),
    inference(resolution,[],[f61,f104])).

fof(f95,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f56,f91,f87])).

fof(f56,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4)
    | v3_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f94,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f57,f91,f87])).

fof(f57,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k6_tmap_1(sK3,sK4)
    | ~ v3_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:18:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (22867)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (22869)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (22868)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (22884)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (22876)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (22866)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (22883)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (22878)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (22886)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (22872)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (22863)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (22867)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (22889)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (22885)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (22870)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (22864)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (22875)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (22863)Refutation not found, incomplete strategy% (22863)------------------------------
% 0.21/0.52  % (22863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22870)Refutation not found, incomplete strategy% (22870)------------------------------
% 0.21/0.52  % (22870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22869)Refutation not found, incomplete strategy% (22869)------------------------------
% 0.21/0.52  % (22869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22869)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22869)Memory used [KB]: 10618
% 0.21/0.52  % (22869)Time elapsed: 0.096 s
% 0.21/0.52  % (22869)------------------------------
% 0.21/0.52  % (22869)------------------------------
% 0.21/0.52  % (22874)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (22868)Refutation not found, incomplete strategy% (22868)------------------------------
% 0.21/0.52  % (22868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22868)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22868)Memory used [KB]: 6140
% 0.21/0.52  % (22868)Time elapsed: 0.104 s
% 0.21/0.52  % (22868)------------------------------
% 0.21/0.52  % (22868)------------------------------
% 0.21/0.52  % (22870)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22870)Memory used [KB]: 1663
% 0.21/0.52  % (22870)Time elapsed: 0.066 s
% 0.21/0.52  % (22870)------------------------------
% 0.21/0.52  % (22870)------------------------------
% 0.21/0.52  % (22880)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (22865)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (22871)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (22877)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (22881)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (22863)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22863)Memory used [KB]: 10618
% 0.21/0.53  % (22863)Time elapsed: 0.105 s
% 0.21/0.53  % (22863)------------------------------
% 0.21/0.53  % (22863)------------------------------
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f701,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f94,f95,f134,f137,f272,f369,f436,f442,f444,f460,f563,f661,f666,f700])).
% 0.21/0.53  fof(f700,plain,(
% 0.21/0.53    spl5_14 | ~spl5_16),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f699])).
% 0.21/0.53  fof(f699,plain,(
% 0.21/0.53    $false | (spl5_14 | ~spl5_16)),
% 0.21/0.53    inference(subsumption_resolution,[],[f698,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ~v2_struct_0(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ((g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k6_tmap_1(sK3,sK4) | ~v3_pre_topc(sK4,sK3)) & (g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4) | v3_pre_topc(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f36,f38,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k6_tmap_1(sK3,X1) | ~v3_pre_topc(X1,sK3)) & (g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,X1) | v3_pre_topc(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ? [X1] : ((g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k6_tmap_1(sK3,X1) | ~v3_pre_topc(X1,sK3)) & (g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,X1) | v3_pre_topc(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) => ((g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k6_tmap_1(sK3,sK4) | ~v3_pre_topc(sK4,sK3)) & (g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4) | v3_pre_topc(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  % (22882)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).
% 0.21/0.53  fof(f698,plain,(
% 0.21/0.53    v2_struct_0(sK3) | (spl5_14 | ~spl5_16)),
% 0.21/0.53    inference(subsumption_resolution,[],[f697,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    v2_pre_topc(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f697,plain,(
% 0.21/0.53    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl5_14 | ~spl5_16)),
% 0.21/0.53    inference(subsumption_resolution,[],[f696,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    l1_pre_topc(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f696,plain,(
% 0.21/0.53    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl5_14 | ~spl5_16)),
% 0.21/0.53    inference(subsumption_resolution,[],[f695,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f695,plain,(
% 0.21/0.53    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl5_14 | ~spl5_16)),
% 0.21/0.53    inference(subsumption_resolution,[],[f694,f440])).
% 0.21/0.53  fof(f440,plain,(
% 0.21/0.53    r2_hidden(sK4,u1_pre_topc(sK3)) | ~spl5_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f439])).
% 0.21/0.53  fof(f439,plain,(
% 0.21/0.53    spl5_16 <=> r2_hidden(sK4,u1_pre_topc(sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.53  fof(f694,plain,(
% 0.21/0.53    ~r2_hidden(sK4,u1_pre_topc(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl5_14),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f693])).
% 0.21/0.53  fof(f693,plain,(
% 0.21/0.53    u1_pre_topc(sK3) != u1_pre_topc(sK3) | ~r2_hidden(sK4,u1_pre_topc(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl5_14),
% 0.21/0.53    inference(superposition,[],[f692,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).
% 0.21/0.53  fof(f692,plain,(
% 0.21/0.53    u1_pre_topc(sK3) != k5_tmap_1(sK3,sK4) | spl5_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f691,f52])).
% 0.21/0.53  fof(f691,plain,(
% 0.21/0.53    u1_pre_topc(sK3) != k5_tmap_1(sK3,sK4) | v2_struct_0(sK3) | spl5_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f690,f53])).
% 0.21/0.53  fof(f690,plain,(
% 0.21/0.53    u1_pre_topc(sK3) != k5_tmap_1(sK3,sK4) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl5_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f689,f54])).
% 0.21/0.53  fof(f689,plain,(
% 0.21/0.53    u1_pre_topc(sK3) != k5_tmap_1(sK3,sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl5_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f688,f55])).
% 0.21/0.53  fof(f688,plain,(
% 0.21/0.53    u1_pre_topc(sK3) != k5_tmap_1(sK3,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl5_14),
% 0.21/0.53    inference(superposition,[],[f363,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.21/0.53  fof(f363,plain,(
% 0.21/0.53    u1_pre_topc(sK3) != u1_pre_topc(k6_tmap_1(sK3,sK4)) | spl5_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f362])).
% 0.21/0.53  fof(f362,plain,(
% 0.21/0.53    spl5_14 <=> u1_pre_topc(sK3) = u1_pre_topc(k6_tmap_1(sK3,sK4))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.53  fof(f666,plain,(
% 0.21/0.53    spl5_16 | ~spl5_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f665,f362,f439])).
% 0.21/0.53  fof(f665,plain,(
% 0.21/0.53    r2_hidden(sK4,u1_pre_topc(sK3)) | ~spl5_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f664,f52])).
% 0.21/0.53  fof(f664,plain,(
% 0.21/0.53    r2_hidden(sK4,u1_pre_topc(sK3)) | v2_struct_0(sK3) | ~spl5_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f663,f53])).
% 0.21/0.53  fof(f663,plain,(
% 0.21/0.53    r2_hidden(sK4,u1_pre_topc(sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl5_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f662,f54])).
% 0.21/0.53  fof(f662,plain,(
% 0.21/0.53    r2_hidden(sK4,u1_pre_topc(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl5_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f647,f55])).
% 0.21/0.53  fof(f647,plain,(
% 0.21/0.53    r2_hidden(sK4,u1_pre_topc(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl5_14),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f644])).
% 0.21/0.53  fof(f644,plain,(
% 0.21/0.53    u1_pre_topc(sK3) != u1_pre_topc(sK3) | r2_hidden(sK4,u1_pre_topc(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl5_14),
% 0.21/0.53    inference(superposition,[],[f68,f630])).
% 0.21/0.53  fof(f630,plain,(
% 0.21/0.53    u1_pre_topc(sK3) = k5_tmap_1(sK3,sK4) | ~spl5_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f629,f52])).
% 0.21/0.53  fof(f629,plain,(
% 0.21/0.53    u1_pre_topc(sK3) = k5_tmap_1(sK3,sK4) | v2_struct_0(sK3) | ~spl5_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f628,f53])).
% 0.21/0.53  fof(f628,plain,(
% 0.21/0.53    u1_pre_topc(sK3) = k5_tmap_1(sK3,sK4) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl5_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f627,f54])).
% 0.21/0.53  fof(f627,plain,(
% 0.21/0.53    u1_pre_topc(sK3) = k5_tmap_1(sK3,sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl5_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f609,f55])).
% 0.21/0.53  fof(f609,plain,(
% 0.21/0.53    u1_pre_topc(sK3) = k5_tmap_1(sK3,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl5_14),
% 0.21/0.53    inference(superposition,[],[f364,f66])).
% 0.21/0.53  fof(f364,plain,(
% 0.21/0.53    u1_pre_topc(sK3) = u1_pre_topc(k6_tmap_1(sK3,sK4)) | ~spl5_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f362])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X0,X1] : (u1_pre_topc(X0) != k5_tmap_1(X0,X1) | r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f661,plain,(
% 0.21/0.53    spl5_2 | ~spl5_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f660,f362,f91])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    spl5_2 <=> g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.53  fof(f660,plain,(
% 0.21/0.53    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4) | ~spl5_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f659,f52])).
% 0.21/0.53  fof(f659,plain,(
% 0.21/0.53    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4) | v2_struct_0(sK3) | ~spl5_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f658,f53])).
% 0.21/0.53  fof(f658,plain,(
% 0.21/0.53    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl5_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f657,f54])).
% 0.21/0.53  fof(f657,plain,(
% 0.21/0.53    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl5_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f645,f55])).
% 0.21/0.53  fof(f645,plain,(
% 0.21/0.53    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl5_14),
% 0.21/0.53    inference(superposition,[],[f64,f630])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).
% 0.21/0.53  % (22873)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  fof(f563,plain,(
% 0.21/0.53    ~spl5_11 | spl5_15),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f562])).
% 0.21/0.53  fof(f562,plain,(
% 0.21/0.53    $false | (~spl5_11 | spl5_15)),
% 0.21/0.53    inference(subsumption_resolution,[],[f560,f473])).
% 0.21/0.53  fof(f473,plain,(
% 0.21/0.53    ~v1_tops_2(k5_tmap_1(sK3,sK4),sK3) | spl5_15),
% 0.21/0.53    inference(subsumption_resolution,[],[f472,f52])).
% 0.21/0.53  fof(f472,plain,(
% 0.21/0.53    ~v1_tops_2(k5_tmap_1(sK3,sK4),sK3) | v2_struct_0(sK3) | spl5_15),
% 0.21/0.53    inference(subsumption_resolution,[],[f471,f53])).
% 0.21/0.53  fof(f471,plain,(
% 0.21/0.53    ~v1_tops_2(k5_tmap_1(sK3,sK4),sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl5_15),
% 0.21/0.53    inference(subsumption_resolution,[],[f470,f54])).
% 0.21/0.53  fof(f470,plain,(
% 0.21/0.53    ~v1_tops_2(k5_tmap_1(sK3,sK4),sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl5_15),
% 0.21/0.53    inference(subsumption_resolution,[],[f469,f55])).
% 0.21/0.53  fof(f469,plain,(
% 0.21/0.53    ~v1_tops_2(k5_tmap_1(sK3,sK4),sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl5_15),
% 0.21/0.53    inference(superposition,[],[f368,f66])).
% 0.21/0.53  fof(f368,plain,(
% 0.21/0.53    ~v1_tops_2(u1_pre_topc(k6_tmap_1(sK3,sK4)),sK3) | spl5_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f366])).
% 0.21/0.53  fof(f366,plain,(
% 0.21/0.53    spl5_15 <=> v1_tops_2(u1_pre_topc(k6_tmap_1(sK3,sK4)),sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.53  fof(f560,plain,(
% 0.21/0.53    v1_tops_2(k5_tmap_1(sK3,sK4),sK3) | ~spl5_11),
% 0.21/0.53    inference(resolution,[],[f559,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sP0(X0,X1) | v1_tops_2(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ! [X0,X1] : ((sP0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) | ~sP0(X0,X1)))),
% 0.21/0.53    inference(flattening,[],[f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ! [X0,X1] : ((sP0(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) | ~sP0(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : (sP0(X0,X1) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f559,plain,(
% 0.21/0.53    sP0(sK3,k5_tmap_1(sK3,sK4)) | ~spl5_11),
% 0.21/0.53    inference(subsumption_resolution,[],[f558,f52])).
% 0.21/0.53  fof(f558,plain,(
% 0.21/0.53    sP0(sK3,k5_tmap_1(sK3,sK4)) | v2_struct_0(sK3) | ~spl5_11),
% 0.21/0.53    inference(subsumption_resolution,[],[f557,f53])).
% 0.21/0.53  fof(f557,plain,(
% 0.21/0.53    sP0(sK3,k5_tmap_1(sK3,sK4)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl5_11),
% 0.21/0.53    inference(subsumption_resolution,[],[f555,f54])).
% 0.21/0.53  fof(f555,plain,(
% 0.21/0.53    sP0(sK3,k5_tmap_1(sK3,sK4)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl5_11),
% 0.21/0.53    inference(resolution,[],[f341,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sP1(X0,X1) | sP0(X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((sP0(X0,X1) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~sP0(X0,X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (sP0(X0,X1) <=> sP1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(definition_folding,[],[f27,f31,f30])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : (sP1(X0,X1) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_compts_1)).
% 0.21/0.53  fof(f341,plain,(
% 0.21/0.53    sP1(sK3,k5_tmap_1(sK3,sK4)) | ~spl5_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f340])).
% 0.21/0.53  fof(f340,plain,(
% 0.21/0.53    spl5_11 <=> sP1(sK3,k5_tmap_1(sK3,sK4))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.53  fof(f460,plain,(
% 0.21/0.53    spl5_11 | ~spl5_13),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f459])).
% 0.21/0.53  fof(f459,plain,(
% 0.21/0.53    $false | (spl5_11 | ~spl5_13)),
% 0.21/0.53    inference(subsumption_resolution,[],[f458,f52])).
% 0.21/0.53  fof(f458,plain,(
% 0.21/0.53    v2_struct_0(sK3) | (spl5_11 | ~spl5_13)),
% 0.21/0.53    inference(subsumption_resolution,[],[f457,f53])).
% 0.21/0.53  fof(f457,plain,(
% 0.21/0.53    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl5_11 | ~spl5_13)),
% 0.21/0.53    inference(subsumption_resolution,[],[f456,f54])).
% 0.21/0.53  fof(f456,plain,(
% 0.21/0.53    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl5_11 | ~spl5_13)),
% 0.21/0.53    inference(subsumption_resolution,[],[f455,f55])).
% 0.21/0.53  fof(f455,plain,(
% 0.21/0.53    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (spl5_11 | ~spl5_13)),
% 0.21/0.53    inference(subsumption_resolution,[],[f451,f342])).
% 0.21/0.53  fof(f342,plain,(
% 0.21/0.53    ~sP1(sK3,k5_tmap_1(sK3,sK4)) | spl5_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f340])).
% 0.21/0.53  fof(f451,plain,(
% 0.21/0.53    sP1(sK3,k5_tmap_1(sK3,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl5_13),
% 0.21/0.53    inference(superposition,[],[f349,f66])).
% 0.21/0.53  fof(f349,plain,(
% 0.21/0.53    sP1(sK3,u1_pre_topc(k6_tmap_1(sK3,sK4))) | ~spl5_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f348])).
% 0.21/0.53  fof(f348,plain,(
% 0.21/0.53    spl5_13 <=> sP1(sK3,u1_pre_topc(k6_tmap_1(sK3,sK4)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.53  fof(f444,plain,(
% 0.21/0.53    spl5_16 | ~spl5_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f443,f87,f439])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    spl5_1 <=> v3_pre_topc(sK4,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.53  fof(f443,plain,(
% 0.21/0.53    ~v3_pre_topc(sK4,sK3) | r2_hidden(sK4,u1_pre_topc(sK3))),
% 0.21/0.53    inference(subsumption_resolution,[],[f106,f54])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ~v3_pre_topc(sK4,sK3) | r2_hidden(sK4,u1_pre_topc(sK3)) | ~l1_pre_topc(sK3)),
% 0.21/0.53    inference(resolution,[],[f59,f55])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.21/0.53  fof(f442,plain,(
% 0.21/0.53    spl5_1 | ~spl5_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f437,f439,f87])).
% 0.21/0.53  fof(f437,plain,(
% 0.21/0.53    ~r2_hidden(sK4,u1_pre_topc(sK3)) | v3_pre_topc(sK4,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f112,f54])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    ~r2_hidden(sK4,u1_pre_topc(sK3)) | v3_pre_topc(sK4,sK3) | ~l1_pre_topc(sK3)),
% 0.21/0.53    inference(resolution,[],[f60,f55])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f436,plain,(
% 0.21/0.53    ~spl5_2 | ~spl5_3 | spl5_13),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f435])).
% 0.21/0.53  fof(f435,plain,(
% 0.21/0.53    $false | (~spl5_2 | ~spl5_3 | spl5_13)),
% 0.21/0.53    inference(subsumption_resolution,[],[f434,f129])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    l1_pre_topc(k6_tmap_1(sK3,sK4)) | ~spl5_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f128])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    spl5_3 <=> l1_pre_topc(k6_tmap_1(sK3,sK4))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.53  fof(f434,plain,(
% 0.21/0.53    ~l1_pre_topc(k6_tmap_1(sK3,sK4)) | (~spl5_2 | spl5_13)),
% 0.21/0.53    inference(subsumption_resolution,[],[f433,f350])).
% 0.21/0.53  fof(f350,plain,(
% 0.21/0.53    ~sP1(sK3,u1_pre_topc(k6_tmap_1(sK3,sK4))) | spl5_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f348])).
% 0.21/0.53  fof(f433,plain,(
% 0.21/0.53    sP1(sK3,u1_pre_topc(k6_tmap_1(sK3,sK4))) | ~l1_pre_topc(k6_tmap_1(sK3,sK4)) | ~spl5_2),
% 0.21/0.53    inference(resolution,[],[f427,f150])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    ( ! [X0] : (sP0(X0,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f98,f149])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    ( ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f148,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) | v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f144])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(u1_pre_topc(X0),u1_pre_topc(X0)) | v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(resolution,[],[f62,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X0] : (sP0(X0,u1_pre_topc(X0)) | ~v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(resolution,[],[f74,f58])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | sP0(X0,X1) | ~v1_tops_2(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f46])).
% 0.21/0.53  fof(f427,plain,(
% 0.21/0.53    ( ! [X1] : (~sP0(k6_tmap_1(sK3,sK4),X1) | sP1(sK3,X1)) ) | ~spl5_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f423,f72])).
% 0.21/0.53  fof(f423,plain,(
% 0.21/0.53    ( ! [X1] : (sP1(sK3,X1) | ~v1_tops_2(X1,k6_tmap_1(sK3,sK4)) | ~sP0(k6_tmap_1(sK3,sK4),X1)) ) | ~spl5_2),
% 0.21/0.53    inference(resolution,[],[f377,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f46])).
% 0.21/0.53  fof(f377,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK3,sK4))))) | sP1(sK3,X0) | ~v1_tops_2(X0,k6_tmap_1(sK3,sK4))) ) | ~spl5_2),
% 0.21/0.53    inference(superposition,[],[f71,f92])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4) | ~spl5_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f91])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | sP1(X0,X1) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ! [X0,X1] : ((sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~sP1(X0,X1)))),
% 0.21/0.53    inference(flattening,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X0,X1] : ((sP1(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~sP1(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f31])).
% 0.21/0.53  fof(f369,plain,(
% 0.21/0.53    spl5_14 | ~spl5_13 | ~spl5_15 | ~spl5_2 | ~spl5_4 | ~spl5_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f360,f262,f132,f91,f366,f348,f362])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    spl5_4 <=> ! [X5] : (r1_tarski(X5,u1_pre_topc(k6_tmap_1(sK3,sK4))) | ~sP1(sK3,X5))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.53  fof(f262,plain,(
% 0.21/0.53    spl5_10 <=> sP1(sK3,u1_pre_topc(sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.53  fof(f360,plain,(
% 0.21/0.53    ~v1_tops_2(u1_pre_topc(k6_tmap_1(sK3,sK4)),sK3) | ~sP1(sK3,u1_pre_topc(k6_tmap_1(sK3,sK4))) | u1_pre_topc(sK3) = u1_pre_topc(k6_tmap_1(sK3,sK4)) | (~spl5_2 | ~spl5_4 | ~spl5_10)),
% 0.21/0.53    inference(subsumption_resolution,[],[f358,f263])).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    sP1(sK3,u1_pre_topc(sK3)) | ~spl5_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f262])).
% 0.21/0.53  fof(f358,plain,(
% 0.21/0.53    ~v1_tops_2(u1_pre_topc(k6_tmap_1(sK3,sK4)),sK3) | ~sP1(sK3,u1_pre_topc(k6_tmap_1(sK3,sK4))) | u1_pre_topc(sK3) = u1_pre_topc(k6_tmap_1(sK3,sK4)) | ~sP1(sK3,u1_pre_topc(sK3)) | (~spl5_2 | ~spl5_4)),
% 0.21/0.53    inference(resolution,[],[f253,f138])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(u1_pre_topc(k6_tmap_1(sK3,sK4)),X0) | u1_pre_topc(k6_tmap_1(sK3,sK4)) = X0 | ~sP1(sK3,X0)) ) | ~spl5_4),
% 0.21/0.53    inference(resolution,[],[f133,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f51])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    ( ! [X5] : (r1_tarski(X5,u1_pre_topc(k6_tmap_1(sK3,sK4))) | ~sP1(sK3,X5)) ) | ~spl5_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f132])).
% 0.21/0.53  fof(f253,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,u1_pre_topc(sK3)) | ~v1_tops_2(X1,sK3) | ~sP1(sK3,X1)) ) | ~spl5_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f250,f54])).
% 0.21/0.53  fof(f250,plain,(
% 0.21/0.53    ( ! [X1] : (~sP1(sK3,X1) | ~v1_tops_2(X1,sK3) | r1_tarski(X1,u1_pre_topc(sK3)) | ~l1_pre_topc(sK3)) ) | ~spl5_2),
% 0.21/0.53    inference(resolution,[],[f248,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0) | r1_tarski(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f41])).
% 0.21/0.53  fof(f248,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) | ~sP1(sK3,X0)) ) | ~spl5_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f247,f52])).
% 0.21/0.53  fof(f247,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) | ~sP1(sK3,X0) | v2_struct_0(sK3)) ) | ~spl5_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f246,f53])).
% 0.21/0.53  fof(f246,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) | ~sP1(sK3,X0) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl5_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f245,f54])).
% 0.21/0.53  fof(f245,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) | ~sP1(sK3,X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl5_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f231,f55])).
% 0.21/0.53  fof(f231,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) | ~sP1(sK3,X0) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl5_2),
% 0.21/0.53    inference(superposition,[],[f104,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK3,sK4))))) | ~sP1(sK3,X0)) ) | ~spl5_2),
% 0.21/0.53    inference(superposition,[],[f70,f92])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~sP1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f272,plain,(
% 0.21/0.53    spl5_10),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f271])).
% 0.21/0.53  fof(f271,plain,(
% 0.21/0.53    $false | spl5_10),
% 0.21/0.53    inference(subsumption_resolution,[],[f270,f54])).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    ~l1_pre_topc(sK3) | spl5_10),
% 0.21/0.53    inference(resolution,[],[f269,f150])).
% 0.21/0.53  fof(f269,plain,(
% 0.21/0.53    ~sP0(sK3,u1_pre_topc(sK3)) | spl5_10),
% 0.21/0.53    inference(subsumption_resolution,[],[f268,f52])).
% 0.21/0.53  fof(f268,plain,(
% 0.21/0.53    ~sP0(sK3,u1_pre_topc(sK3)) | v2_struct_0(sK3) | spl5_10),
% 0.21/0.53    inference(subsumption_resolution,[],[f267,f53])).
% 0.21/0.53  fof(f267,plain,(
% 0.21/0.53    ~sP0(sK3,u1_pre_topc(sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl5_10),
% 0.21/0.53    inference(subsumption_resolution,[],[f266,f54])).
% 0.21/0.53  fof(f266,plain,(
% 0.21/0.53    ~sP0(sK3,u1_pre_topc(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl5_10),
% 0.21/0.53    inference(resolution,[],[f264,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP1(X0,X1) | ~sP0(X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f264,plain,(
% 0.21/0.53    ~sP1(sK3,u1_pre_topc(sK3)) | spl5_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f262])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    spl5_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f136])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    $false | spl5_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f135,f118])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    sP2(sK4,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f117,f52])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    sP2(sK4,sK3) | v2_struct_0(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f116,f53])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    sP2(sK4,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f115,f54])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    sP2(sK4,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.53    inference(resolution,[],[f80,f55])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP2(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(definition_folding,[],[f29,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X1,X0] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~sP2(X1,X0))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  % (22876)Refutation not found, incomplete strategy% (22876)------------------------------
% 0.21/0.53  % (22876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22876)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22876)Memory used [KB]: 6140
% 0.21/0.53  % (22876)Time elapsed: 0.120 s
% 0.21/0.53  % (22876)------------------------------
% 0.21/0.53  % (22876)------------------------------
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    ~sP2(sK4,sK3) | spl5_3),
% 0.21/0.53    inference(resolution,[],[f130,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X1,X0)) | ~sP2(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X1,X0)) & v2_pre_topc(k6_tmap_1(X1,X0)) & v1_pre_topc(k6_tmap_1(X1,X0))) | ~sP2(X0,X1))),
% 0.21/0.53    inference(rectify,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ! [X1,X0] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~sP2(X1,X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f33])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ~l1_pre_topc(k6_tmap_1(sK3,sK4)) | spl5_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f128])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    ~spl5_3 | spl5_4 | ~spl5_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f126,f91,f132,f128])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ( ! [X5] : (r1_tarski(X5,u1_pre_topc(k6_tmap_1(sK3,sK4))) | ~l1_pre_topc(k6_tmap_1(sK3,sK4)) | ~sP1(sK3,X5)) ) | ~spl5_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f122,f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X0] : (v1_tops_2(X0,k6_tmap_1(sK3,sK4)) | ~sP1(sK3,X0)) ) | ~spl5_2),
% 0.21/0.53    inference(superposition,[],[f69,f92])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ( ! [X5] : (~v1_tops_2(X5,k6_tmap_1(sK3,sK4)) | r1_tarski(X5,u1_pre_topc(k6_tmap_1(sK3,sK4))) | ~l1_pre_topc(k6_tmap_1(sK3,sK4)) | ~sP1(sK3,X5)) ) | ~spl5_2),
% 0.21/0.53    inference(resolution,[],[f61,f104])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    spl5_1 | spl5_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f56,f91,f87])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k6_tmap_1(sK3,sK4) | v3_pre_topc(sK4,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ~spl5_1 | ~spl5_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f57,f91,f87])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k6_tmap_1(sK3,sK4) | ~v3_pre_topc(sK4,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (22867)------------------------------
% 0.21/0.53  % (22867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22867)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (22867)Memory used [KB]: 6396
% 0.21/0.53  % (22867)Time elapsed: 0.110 s
% 0.21/0.53  % (22867)------------------------------
% 0.21/0.53  % (22867)------------------------------
% 0.21/0.53  % (22874)Refutation not found, incomplete strategy% (22874)------------------------------
% 0.21/0.53  % (22874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22874)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22874)Memory used [KB]: 10618
% 0.21/0.53  % (22874)Time elapsed: 0.118 s
% 0.21/0.53  % (22874)------------------------------
% 0.21/0.53  % (22874)------------------------------
% 0.21/0.53  % (22859)Success in time 0.17 s
%------------------------------------------------------------------------------
