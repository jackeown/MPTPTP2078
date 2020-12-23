%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:32 EST 2020

% Result     : Theorem 4.14s
% Output     : Refutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :  234 (1410 expanded)
%              Number of leaves         :   36 ( 393 expanded)
%              Depth                    :   30
%              Number of atoms          :  994 (12200 expanded)
%              Number of equality atoms :  134 (2026 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5714,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f237,f306,f696,f698,f744,f1131,f1351,f1660,f1665,f1826,f2207,f4885,f5683,f5705,f5713])).

fof(f5713,plain,
    ( spl4_98
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_99 ),
    inference(avatar_split_clause,[],[f5712,f4883,f694,f235,f4880])).

fof(f4880,plain,
    ( spl4_98
  <=> v1_tsep_1(sK1,k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).

fof(f235,plain,
    ( spl4_2
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f694,plain,
    ( spl4_5
  <=> m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f4883,plain,
    ( spl4_99
  <=> u1_struct_0(sK1) = sK2(k8_tmap_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).

fof(f5712,plain,
    ( v1_tsep_1(sK1,k8_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f5711,f230])).

fof(f230,plain,(
    l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f229,f106])).

fof(f106,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_tsep_1(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
      | ( m1_pre_topc(sK1,sK0)
        & v1_tsep_1(sK1,sK0) ) )
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f85,f87,f86])).

fof(f86,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
              | ~ m1_pre_topc(X1,X0)
              | ~ v1_tsep_1(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
              | ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) ) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1)
            | ~ m1_pre_topc(X1,sK0)
            | ~ v1_tsep_1(X1,sK0) )
          & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1)
            | ( m1_pre_topc(X1,sK0)
              & v1_tsep_1(X1,sK0) ) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,
    ( ? [X1] :
        ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1)
          | ~ m1_pre_topc(X1,sK0)
          | ~ v1_tsep_1(X1,sK0) )
        & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1)
          | ( m1_pre_topc(X1,sK0)
            & v1_tsep_1(X1,sK0) ) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_tsep_1(sK1,sK0) )
      & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
        | ( m1_pre_topc(sK1,sK0)
          & v1_tsep_1(sK1,sK0) ) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).

fof(f229,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f228,f107])).

fof(f107,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f88])).

fof(f228,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f206,f108])).

fof(f108,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f88])).

fof(f206,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f110,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f110,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f88])).

fof(f5711,plain,
    ( v1_tsep_1(sK1,k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f5710,f2221])).

fof(f2221,plain,
    ( m1_pre_topc(sK1,k8_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(superposition,[],[f695,f236])).

fof(f236,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f235])).

fof(f695,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f694])).

fof(f5710,plain,
    ( v1_tsep_1(sK1,k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_99 ),
    inference(subsumption_resolution,[],[f5709,f1205])).

fof(f1205,plain,(
    v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1204,f210])).

fof(f210,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f195,f108])).

fof(f195,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f110,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

% (4051)Time limit reached!
% (4051)------------------------------
% (4051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4035)Time limit reached!
% (4035)------------------------------
% (4035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4035)Termination reason: Time limit

% (4035)Memory used [KB]: 14839
% (4035)Time elapsed: 0.505 s
% (4035)------------------------------
% (4035)------------------------------
fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f1204,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1203,f218])).

fof(f218,plain,(
    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f217,f106])).

fof(f217,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f216,f107])).

fof(f216,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f215,f108])).

fof(f215,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f200,f109])).

fof(f109,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f88])).

fof(f200,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f110,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).

fof(f1203,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1))))
    | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1202,f106])).

fof(f1202,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1))))
    | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1201,f107])).

fof(f1201,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1))))
    | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1200,f108])).

fof(f1200,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1))))
    | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1199,f210])).

fof(f1199,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1))))
    | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f177,f454])).

fof(f454,plain,(
    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f453,f106])).

fof(f453,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f452,f107])).

fof(f452,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f451,f108])).

fof(f451,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f450,f110])).

fof(f450,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f449,f224])).

fof(f224,plain,(
    v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f223,f106])).

fof(f223,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f222,f107])).

fof(f222,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f204,f108])).

fof(f204,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f110,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f449,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f448,f227])).

fof(f227,plain,(
    v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f226,f106])).

fof(f226,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f225,f107])).

fof(f225,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f205,f108])).

fof(f205,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f110,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f448,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f427,f230])).

fof(f427,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f210,f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f175])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f136])).

fof(f136,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK3(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK3(X0,X1,X2)
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f97,f98])).

fof(f98,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK3(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK3(X0,X1,X2)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
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
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

fof(f177,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | v3_pre_topc(X2,k6_tmap_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
      | X1 != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
             => ( X1 = X2
               => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).

fof(f5709,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))
    | v1_tsep_1(sK1,k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK1,k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_99 ),
    inference(superposition,[],[f129,f4884])).

fof(f4884,plain,
    ( u1_struct_0(sK1) = sK2(k8_tmap_1(sK0,sK1),sK1)
    | ~ spl4_99 ),
    inference(avatar_component_clause,[],[f4883])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK2(X0,X1),X0)
      | v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ( ~ v3_pre_topc(sK2(X0,X1),X0)
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f91,f92])).

fof(f92,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0,X1),X0)
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).

% (4051)Termination reason: Time limit
fof(f5705,plain,
    ( spl4_16
    | ~ spl4_2
    | ~ spl4_98
    | ~ spl4_115 ),
    inference(avatar_split_clause,[],[f5703,f5681,f4880,f235,f1122])).

% (4039)Time limit reached!
% (4039)------------------------------
% (4039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4039)Termination reason: Time limit

fof(f1122,plain,
    ( spl4_16
  <=> v2_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f5681,plain,
    ( spl4_115
  <=> ! [X1] :
        ( ~ m1_pre_topc(sK0,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_tsep_1(sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_115])])).

% (4039)Memory used [KB]: 8955
% (4039)Time elapsed: 0.507 s
% (4039)------------------------------
% (4039)------------------------------
fof(f5703,plain,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_98
    | ~ spl4_115 ),
    inference(subsumption_resolution,[],[f5702,f2219])).

fof(f2219,plain,
    ( m1_pre_topc(sK0,k8_tmap_1(sK0,sK1))
    | ~ spl4_2 ),
    inference(superposition,[],[f280,f236])).

fof(f280,plain,(
    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f279,f108])).

fof(f279,plain,
    ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f261])).

fof(f261,plain,
    ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f191,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f191,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f108,f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f5702,plain,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK0,k8_tmap_1(sK0,sK1))
    | ~ spl4_98
    | ~ spl4_115 ),
    inference(subsumption_resolution,[],[f5701,f230])).

fof(f5701,plain,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK0,k8_tmap_1(sK0,sK1))
    | ~ spl4_98
    | ~ spl4_115 ),
    inference(subsumption_resolution,[],[f5700,f227])).

fof(f5700,plain,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ m1_pre_topc(sK0,k8_tmap_1(sK0,sK1))
    | ~ spl4_98
    | ~ spl4_115 ),
    inference(resolution,[],[f4881,f5682])).

fof(f5682,plain,
    ( ! [X1] :
        ( ~ v1_tsep_1(sK1,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK0,X1) )
    | ~ spl4_115 ),
    inference(avatar_component_clause,[],[f5681])).

fof(f4881,plain,
    ( v1_tsep_1(sK1,k8_tmap_1(sK0,sK1))
    | ~ spl4_98 ),
    inference(avatar_component_clause,[],[f4880])).

fof(f5683,plain,
    ( spl4_115
    | spl4_1 ),
    inference(avatar_split_clause,[],[f1353,f232,f5681])).

fof(f232,plain,
    ( spl4_1
  <=> v1_tsep_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1353,plain,(
    ! [X1] :
      ( v1_tsep_1(sK1,sK0)
      | ~ m1_pre_topc(sK0,X1)
      | ~ v1_tsep_1(sK1,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f1352,f202])).

fof(f202,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK0,X0)
      | m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f110,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f1352,plain,(
    ! [X1] :
      ( v1_tsep_1(sK1,sK0)
      | ~ m1_pre_topc(sK0,X1)
      | ~ m1_pre_topc(sK1,X1)
      | ~ v1_tsep_1(sK1,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f747,f106])).

fof(f747,plain,(
    ! [X1] :
      ( v1_tsep_1(sK1,sK0)
      | ~ m1_pre_topc(sK0,X1)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(sK1,X1)
      | ~ v1_tsep_1(sK1,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f440,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | v1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).

fof(f440,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f210,f169])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f4885,plain,
    ( spl4_98
    | spl4_99
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f2261,f694,f235,f4883,f4880])).

fof(f2261,plain,
    ( u1_struct_0(sK1) = sK2(k8_tmap_1(sK0,sK1),sK1)
    | v1_tsep_1(sK1,k8_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f2244,f230])).

fof(f2244,plain,
    ( u1_struct_0(sK1) = sK2(k8_tmap_1(sK0,sK1),sK1)
    | v1_tsep_1(sK1,k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f2221,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f93])).

% (4052)Time limit reached!
% (4052)------------------------------
% (4052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4052)Termination reason: Time limit
% (4052)Termination phase: Saturation

% (4052)Memory used [KB]: 4477
% (4052)Time elapsed: 0.500 s
% (4052)------------------------------
% (4052)------------------------------
fof(f2207,plain,
    ( spl4_2
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f2206])).

fof(f2206,plain,
    ( $false
    | spl4_2
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f2202,f305])).

fof(f305,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f235])).

fof(f2202,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ spl4_30 ),
    inference(superposition,[],[f345,f1825])).

fof(f1825,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f1824])).

fof(f1824,plain,
    ( spl4_30
  <=> u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f345,plain,(
    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f344,f218])).

fof(f344,plain,(
    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f343,f230])).

fof(f343,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f224,f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f1826,plain,
    ( ~ spl4_23
    | spl4_30 ),
    inference(avatar_split_clause,[],[f468,f1824,f1348])).

fof(f1348,plain,
    ( spl4_23
  <=> r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f468,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f467,f447])).

fof(f447,plain,(
    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f446,f106])).

fof(f446,plain,
    ( u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f445,f107])).

fof(f445,plain,
    ( u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f444,f108])).

fof(f444,plain,
    ( u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f443,f109])).

fof(f443,plain,
    ( u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f426,f110])).

fof(f426,plain,
    ( u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f210,f178])).

% (4049)Time limit reached!
% (4049)------------------------------
% (4049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f178,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f467,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f466,f106])).

fof(f466,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f465,f107])).

fof(f465,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f434,f108])).

fof(f434,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f210,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
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
    inference(nnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f1665,plain,
    ( ~ spl4_16
    | spl4_17 ),
    inference(avatar_contradiction_clause,[],[f1664])).

fof(f1664,plain,
    ( $false
    | ~ spl4_16
    | spl4_17 ),
    inference(subsumption_resolution,[],[f1663,f1126])).

fof(f1126,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f1125])).

fof(f1125,plain,
    ( spl4_17
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f1663,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f1662,f218])).

fof(f1662,plain,
    ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f1661,f364])).

fof(f364,plain,(
    l1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f230,f116])).

fof(f116,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f1661,plain,
    ( ~ l1_struct_0(k8_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ spl4_16 ),
    inference(resolution,[],[f1123,f155])).

fof(f155,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f1123,plain,
    ( v2_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f1122])).

fof(f1660,plain,(
    ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f1659])).

fof(f1659,plain,
    ( $false
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f1658,f106])).

fof(f1658,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f1655,f192])).

fof(f192,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f108,f116])).

fof(f1655,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_17 ),
    inference(resolution,[],[f1327,f135])).

fof(f135,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f1327,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f1125])).

fof(f1351,plain,
    ( spl4_23
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f455,f1129,f1348])).

fof(f1129,plain,
    ( spl4_18
  <=> v3_pre_topc(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f455,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f430,f108])).

fof(f430,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f210,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f1131,plain,
    ( ~ spl4_1
    | spl4_18 ),
    inference(avatar_split_clause,[],[f742,f1129,f232])).

fof(f742,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f741,f108])).

fof(f741,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f428,f110])).

fof(f428,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f210,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f744,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f743])).

fof(f743,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f304,f110])).

fof(f304,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl4_3
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f698,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f697])).

fof(f697,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f692,f209])).

fof(f209,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f194,f108])).

fof(f194,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f110,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f692,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f691])).

fof(f691,plain,
    ( spl4_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f696,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f208,f694,f691])).

fof(f208,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f193,f108])).

fof(f193,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f110,f120])).

fof(f306,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f113,f235,f258,f232])).

fof(f113,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f88])).

fof(f237,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f111,f235,f232])).

fof(f111,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (4055)lrs+1011_4:1_av=off:fsr=off:irw=on:nwc=1:stl=30:sd=4:ss=axioms:st=1.5:sp=reverse_arity_12 on theBenchmark
% 0.22/0.51  % (4033)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_3 on theBenchmark
% 0.22/0.51  % (4046)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_4 on theBenchmark
% 0.22/0.52  % (4035)dis+1011_10_aac=none:add=large:afp=10000:afq=1.1:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=6:newcnf=on:nwc=2.5:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (4036)ott+1002_2_av=off:bd=preordered:irw=on:lma=on:nm=64:nwc=10:sp=reverse_arity:updr=off_22 on theBenchmark
% 0.22/0.52  % (4043)lrs+1003_2_acc=on:afp=4000:afq=2.0:amm=sco:bd=off:ccuc=small_ones:fsr=off:fde=unused:gsp=input_only:nm=64:newcnf=on:nwc=2.5:nicw=on:stl=30:urr=ec_only_8 on theBenchmark
% 0.22/0.52  % (4048)lrs+1002_3_aac=none:acc=on:add=off:afp=4000:afq=1.1:amm=sco:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=32:newcnf=on:nwc=1.1:nicw=on:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=occurrence:updr=off_24 on theBenchmark
% 0.22/0.52  % (4034)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (4031)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.53  % (4044)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_14 on theBenchmark
% 0.22/0.53  % (4030)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_3 on theBenchmark
% 0.22/0.53  % (4060)lrs+10_6_aac=none:acc=model:add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bd=off:ccuc=small_ones:irw=on:lcm=reverse:nm=0:nwc=1:nicw=on:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (4051)ott+1004_12_awrs=converge:awrsf=64:aac=none:afr=on:afp=4000:afq=1.4:amm=sco:anc=none:bs=on:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=on:lma=on:nwc=5:nicw=on:sas=z3:sos=all:sac=on:sp=occurrence:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (4052)dis+11_28_av=off:fsr=off:irw=on:lcm=predicate:nm=2:newcnf=on:nwc=5:sp=occurrence:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (4032)ott+1010_5:4_av=off:bd=off:fde=none:irw=on:lma=on:nm=32:nwc=2.5:sd=2:ss=axioms:st=3.0:urr=on_5 on theBenchmark
% 0.22/0.54  % (4047)dis+11_3:1_add=off:afr=on:afp=100000:afq=1.2:amm=off:anc=none:bd=off:bs=unit_only:irw=on:lcm=predicate:lma=on:nm=2:nwc=1:sd=2:ss=axioms:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 0.22/0.54  % (4058)dis+1003_64_add=off:afr=on:afp=100000:afq=1.1:anc=none:cond=fast:fde=none:irw=on:nm=6:newcnf=on:nwc=1.3:uhcvi=on_5 on theBenchmark
% 0.22/0.54  % (4045)ott+1_8_av=off:bd=off:bs=on:cond=on:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:lwlo=on:nwc=1:sos=on_10 on theBenchmark
% 0.22/0.54  % (4048)Refutation not found, incomplete strategy% (4048)------------------------------
% 0.22/0.54  % (4048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4048)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4048)Memory used [KB]: 10874
% 0.22/0.54  % (4048)Time elapsed: 0.130 s
% 0.22/0.54  % (4048)------------------------------
% 0.22/0.54  % (4048)------------------------------
% 0.22/0.54  % (4061)ott+11_8_amm=off:anc=none:bsr=on:cond=on:irw=on:nm=2:nwc=1.1:ss=axioms:st=2.0:sac=on_1 on theBenchmark
% 0.22/0.55  % (4050)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_36 on theBenchmark
% 0.22/0.55  % (4040)dis-3_5_av=off:cond=on:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1:sos=on:sp=reverse_arity_3 on theBenchmark
% 0.22/0.55  % (4049)dis+1010_4_afp=10000:afq=1.2:anc=none:irw=on:lma=on:nm=64:nwc=10:sas=z3:sac=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (4056)dis+11_5_av=off:bd=off:bs=unit_only:bsr=on:cond=on:lcm=reverse:nm=0:nwc=1.2_5 on theBenchmark
% 0.22/0.55  % (4037)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_16 on theBenchmark
% 0.22/0.55  % (4057)ott+1002_128_av=off:bd=off:bs=on:bsr=on:cond=on:fsr=off:nm=6:newcnf=on:nwc=1:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (4053)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_72 on theBenchmark
% 0.22/0.56  % (4039)dis+11_4_afr=on:afp=1000:afq=1.4:amm=off:anc=none:lcm=reverse:lma=on:lwlo=on:nm=6:newcnf=on:nwc=1:sd=2:ss=axioms:st=2.0:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (4041)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_5 on theBenchmark
% 1.59/0.57  % (4054)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.59/0.58  % (4038)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_4 on theBenchmark
% 2.16/0.68  % (4161)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_4 on theBenchmark
% 3.15/0.82  % (4061)Time limit reached!
% 3.15/0.82  % (4061)------------------------------
% 3.15/0.82  % (4061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.82  % (4061)Termination reason: Time limit
% 3.15/0.82  
% 3.15/0.82  % (4061)Memory used [KB]: 7803
% 3.15/0.82  % (4061)Time elapsed: 0.408 s
% 3.15/0.82  % (4061)------------------------------
% 3.15/0.82  % (4061)------------------------------
% 3.15/0.84  % (4047)Time limit reached!
% 3.15/0.84  % (4047)------------------------------
% 3.15/0.84  % (4047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.84  % (4047)Termination reason: Time limit
% 3.15/0.84  
% 3.15/0.84  % (4047)Memory used [KB]: 7675
% 3.15/0.84  % (4047)Time elapsed: 0.425 s
% 3.15/0.84  % (4047)------------------------------
% 3.15/0.84  % (4047)------------------------------
% 3.91/0.87  % (4030)Refutation not found, incomplete strategy% (4030)------------------------------
% 3.91/0.87  % (4030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.91/0.87  % (4030)Termination reason: Refutation not found, incomplete strategy
% 3.91/0.87  
% 3.91/0.87  % (4030)Memory used [KB]: 8059
% 3.91/0.87  % (4030)Time elapsed: 0.451 s
% 3.91/0.87  % (4030)------------------------------
% 3.91/0.87  % (4030)------------------------------
% 4.14/0.91  % (4037)Refutation found. Thanks to Tanya!
% 4.14/0.91  % SZS status Theorem for theBenchmark
% 4.14/0.92  % SZS output start Proof for theBenchmark
% 4.14/0.92  fof(f5714,plain,(
% 4.14/0.92    $false),
% 4.14/0.92    inference(avatar_sat_refutation,[],[f237,f306,f696,f698,f744,f1131,f1351,f1660,f1665,f1826,f2207,f4885,f5683,f5705,f5713])).
% 4.14/0.92  fof(f5713,plain,(
% 4.14/0.92    spl4_98 | ~spl4_2 | ~spl4_5 | ~spl4_99),
% 4.14/0.92    inference(avatar_split_clause,[],[f5712,f4883,f694,f235,f4880])).
% 4.14/0.92  fof(f4880,plain,(
% 4.14/0.92    spl4_98 <=> v1_tsep_1(sK1,k8_tmap_1(sK0,sK1))),
% 4.14/0.92    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).
% 4.14/0.92  fof(f235,plain,(
% 4.14/0.92    spl4_2 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 4.14/0.92    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 4.14/0.92  fof(f694,plain,(
% 4.14/0.92    spl4_5 <=> m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 4.14/0.92    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 4.14/0.92  fof(f4883,plain,(
% 4.14/0.92    spl4_99 <=> u1_struct_0(sK1) = sK2(k8_tmap_1(sK0,sK1),sK1)),
% 4.14/0.92    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).
% 4.14/0.92  fof(f5712,plain,(
% 4.14/0.92    v1_tsep_1(sK1,k8_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_5 | ~spl4_99)),
% 4.14/0.92    inference(subsumption_resolution,[],[f5711,f230])).
% 4.14/0.92  fof(f230,plain,(
% 4.14/0.92    l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 4.14/0.92    inference(subsumption_resolution,[],[f229,f106])).
% 4.14/0.92  fof(f106,plain,(
% 4.14/0.92    ~v2_struct_0(sK0)),
% 4.14/0.92    inference(cnf_transformation,[],[f88])).
% 4.14/0.92  fof(f88,plain,(
% 4.14/0.92    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 4.14/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f85,f87,f86])).
% 4.14/0.92  fof(f86,plain,(
% 4.14/0.92    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 4.14/0.92    introduced(choice_axiom,[])).
% 4.14/0.92  fof(f87,plain,(
% 4.14/0.92    ? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,X1) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,X1) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 4.14/0.92    introduced(choice_axiom,[])).
% 4.14/0.92  fof(f85,plain,(
% 4.14/0.92    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.14/0.92    inference(flattening,[],[f84])).
% 4.14/0.92  fof(f84,plain,(
% 4.14/0.92    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.14/0.92    inference(nnf_transformation,[],[f36])).
% 4.14/0.92  fof(f36,plain,(
% 4.14/0.92    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.14/0.92    inference(flattening,[],[f35])).
% 4.14/0.92  fof(f35,plain,(
% 4.14/0.92    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 4.14/0.92    inference(ennf_transformation,[],[f34])).
% 4.14/0.92  fof(f34,negated_conjecture,(
% 4.14/0.92    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 4.14/0.92    inference(negated_conjecture,[],[f33])).
% 4.14/0.92  fof(f33,conjecture,(
% 4.14/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 4.14/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).
% 4.14/0.92  fof(f229,plain,(
% 4.14/0.92    l1_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 4.14/0.92    inference(subsumption_resolution,[],[f228,f107])).
% 4.14/0.92  fof(f107,plain,(
% 4.14/0.92    v2_pre_topc(sK0)),
% 4.14/0.92    inference(cnf_transformation,[],[f88])).
% 4.14/0.92  fof(f228,plain,(
% 4.14/0.92    l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.92    inference(subsumption_resolution,[],[f206,f108])).
% 4.14/0.92  fof(f108,plain,(
% 4.14/0.92    l1_pre_topc(sK0)),
% 4.14/0.92    inference(cnf_transformation,[],[f88])).
% 4.14/0.92  fof(f206,plain,(
% 4.14/0.92    l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.92    inference(resolution,[],[f110,f162])).
% 4.14/0.92  fof(f162,plain,(
% 4.14/0.92    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.14/0.92    inference(cnf_transformation,[],[f79])).
% 4.14/0.92  fof(f79,plain,(
% 4.14/0.92    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.14/0.92    inference(flattening,[],[f78])).
% 4.14/0.92  fof(f78,plain,(
% 4.14/0.92    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.14/0.92    inference(ennf_transformation,[],[f21])).
% 4.14/0.92  fof(f21,axiom,(
% 4.14/0.92    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 4.14/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 4.14/0.92  fof(f110,plain,(
% 4.14/0.92    m1_pre_topc(sK1,sK0)),
% 4.14/0.92    inference(cnf_transformation,[],[f88])).
% 4.14/0.92  fof(f5711,plain,(
% 4.14/0.92    v1_tsep_1(sK1,k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_5 | ~spl4_99)),
% 4.14/0.92    inference(subsumption_resolution,[],[f5710,f2221])).
% 4.14/0.92  fof(f2221,plain,(
% 4.14/0.92    m1_pre_topc(sK1,k8_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_5)),
% 4.14/0.92    inference(superposition,[],[f695,f236])).
% 4.14/0.92  fof(f236,plain,(
% 4.14/0.92    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | ~spl4_2),
% 4.14/0.92    inference(avatar_component_clause,[],[f235])).
% 4.14/0.92  fof(f695,plain,(
% 4.14/0.92    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl4_5),
% 4.14/0.92    inference(avatar_component_clause,[],[f694])).
% 4.14/0.92  fof(f5710,plain,(
% 4.14/0.92    v1_tsep_1(sK1,k8_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl4_99),
% 4.14/0.92    inference(subsumption_resolution,[],[f5709,f1205])).
% 4.14/0.92  fof(f1205,plain,(
% 4.14/0.92    v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))),
% 4.14/0.92    inference(subsumption_resolution,[],[f1204,f210])).
% 4.14/0.92  fof(f210,plain,(
% 4.14/0.92    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.14/0.92    inference(subsumption_resolution,[],[f195,f108])).
% 4.14/0.92  fof(f195,plain,(
% 4.14/0.92    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 4.14/0.92    inference(resolution,[],[f110,f123])).
% 4.14/0.92  fof(f123,plain,(
% 4.14/0.92    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.14/0.92    inference(cnf_transformation,[],[f45])).
% 4.14/0.92  % (4051)Time limit reached!
% 4.14/0.92  % (4051)------------------------------
% 4.14/0.92  % (4051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.14/0.92  % (4035)Time limit reached!
% 4.14/0.92  % (4035)------------------------------
% 4.14/0.92  % (4035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.14/0.92  % (4035)Termination reason: Time limit
% 4.14/0.92  
% 4.14/0.92  % (4035)Memory used [KB]: 14839
% 4.14/0.92  % (4035)Time elapsed: 0.505 s
% 4.14/0.92  % (4035)------------------------------
% 4.14/0.92  % (4035)------------------------------
% 4.14/0.92  fof(f45,plain,(
% 4.14/0.92    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.14/0.92    inference(ennf_transformation,[],[f29])).
% 4.14/0.92  fof(f29,axiom,(
% 4.14/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.14/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 4.14/0.92  fof(f1204,plain,(
% 4.14/0.92    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))),
% 4.14/0.92    inference(forward_demodulation,[],[f1203,f218])).
% 4.14/0.92  fof(f218,plain,(
% 4.14/0.92    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 4.14/0.92    inference(subsumption_resolution,[],[f217,f106])).
% 4.14/0.92  fof(f217,plain,(
% 4.14/0.92    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 4.14/0.92    inference(subsumption_resolution,[],[f216,f107])).
% 4.14/0.92  fof(f216,plain,(
% 4.14/0.92    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.92    inference(subsumption_resolution,[],[f215,f108])).
% 4.14/0.92  fof(f215,plain,(
% 4.14/0.92    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.92    inference(subsumption_resolution,[],[f200,f109])).
% 4.14/0.92  fof(f109,plain,(
% 4.14/0.92    ~v2_struct_0(sK1)),
% 4.14/0.92    inference(cnf_transformation,[],[f88])).
% 4.14/0.92  fof(f200,plain,(
% 4.14/0.92    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.92    inference(resolution,[],[f110,f145])).
% 4.14/0.92  fof(f145,plain,(
% 4.14/0.92    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.14/0.92    inference(cnf_transformation,[],[f64])).
% 4.14/0.92  fof(f64,plain,(
% 4.14/0.92    ! [X0] : (! [X1] : ((! [X2] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.14/0.92    inference(flattening,[],[f63])).
% 4.14/0.92  fof(f63,plain,(
% 4.14/0.92    ! [X0] : (! [X1] : ((! [X2] : ((u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.14/0.92    inference(ennf_transformation,[],[f25])).
% 4.14/0.92  fof(f25,axiom,(
% 4.14/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))))),
% 4.14/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).
% 4.14/0.92  fof(f1203,plain,(
% 4.14/0.92    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1)))) | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1))),
% 4.14/0.92    inference(subsumption_resolution,[],[f1202,f106])).
% 4.14/0.92  fof(f1202,plain,(
% 4.14/0.92    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1)))) | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 4.14/0.92    inference(subsumption_resolution,[],[f1201,f107])).
% 4.14/0.92  fof(f1201,plain,(
% 4.14/0.92    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1)))) | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.92    inference(subsumption_resolution,[],[f1200,f108])).
% 4.14/0.92  fof(f1200,plain,(
% 4.14/0.92    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1)))) | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.92    inference(subsumption_resolution,[],[f1199,f210])).
% 4.14/0.92  fof(f1199,plain,(
% 4.14/0.92    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK0,sK1)))) | v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.92    inference(superposition,[],[f177,f454])).
% 4.14/0.92  fof(f454,plain,(
% 4.14/0.92    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 4.14/0.92    inference(subsumption_resolution,[],[f453,f106])).
% 4.14/0.92  fof(f453,plain,(
% 4.14/0.92    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 4.14/0.92    inference(subsumption_resolution,[],[f452,f107])).
% 4.14/0.92  fof(f452,plain,(
% 4.14/0.92    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.92    inference(subsumption_resolution,[],[f451,f108])).
% 4.14/0.92  fof(f451,plain,(
% 4.14/0.92    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.92    inference(subsumption_resolution,[],[f450,f110])).
% 4.14/0.92  fof(f450,plain,(
% 4.14/0.92    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.92    inference(subsumption_resolution,[],[f449,f224])).
% 4.14/0.92  fof(f224,plain,(
% 4.14/0.92    v1_pre_topc(k8_tmap_1(sK0,sK1))),
% 4.14/0.92    inference(subsumption_resolution,[],[f223,f106])).
% 4.14/0.92  fof(f223,plain,(
% 4.14/0.92    v1_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 4.14/0.92    inference(subsumption_resolution,[],[f222,f107])).
% 4.14/0.92  fof(f222,plain,(
% 4.14/0.92    v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.92    inference(subsumption_resolution,[],[f204,f108])).
% 4.14/0.92  fof(f204,plain,(
% 4.14/0.92    v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.92    inference(resolution,[],[f110,f160])).
% 4.14/0.92  fof(f160,plain,(
% 4.14/0.92    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.14/0.92    inference(cnf_transformation,[],[f79])).
% 4.14/0.92  fof(f449,plain,(
% 4.14/0.92    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.92    inference(subsumption_resolution,[],[f448,f227])).
% 4.14/0.92  fof(f227,plain,(
% 4.14/0.92    v2_pre_topc(k8_tmap_1(sK0,sK1))),
% 4.14/0.92    inference(subsumption_resolution,[],[f226,f106])).
% 4.14/0.92  fof(f226,plain,(
% 4.14/0.92    v2_pre_topc(k8_tmap_1(sK0,sK1)) | v2_struct_0(sK0)),
% 4.14/0.92    inference(subsumption_resolution,[],[f225,f107])).
% 4.14/0.92  fof(f225,plain,(
% 4.14/0.92    v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.92    inference(subsumption_resolution,[],[f205,f108])).
% 4.14/0.92  fof(f205,plain,(
% 4.14/0.92    v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.92    inference(resolution,[],[f110,f161])).
% 4.14/0.92  fof(f161,plain,(
% 4.14/0.92    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.14/0.92    inference(cnf_transformation,[],[f79])).
% 4.14/0.92  fof(f448,plain,(
% 4.14/0.92    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.92    inference(subsumption_resolution,[],[f427,f230])).
% 4.14/0.92  fof(f427,plain,(
% 4.14/0.92    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.92    inference(resolution,[],[f210,f176])).
% 4.14/0.92  fof(f176,plain,(
% 4.14/0.92    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.14/0.92    inference(equality_resolution,[],[f175])).
% 4.14/0.92  fof(f175,plain,(
% 4.14/0.92    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.14/0.92    inference(equality_resolution,[],[f136])).
% 4.14/0.92  fof(f136,plain,(
% 4.14/0.92    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.14/0.92    inference(cnf_transformation,[],[f99])).
% 4.14/0.92  fof(f99,plain,(
% 4.14/0.92    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK3(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK3(X0,X1,X2) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.14/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f97,f98])).
% 4.14/0.92  fof(f98,plain,(
% 4.14/0.92    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK3(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK3(X0,X1,X2) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.14/0.92    introduced(choice_axiom,[])).
% 4.14/0.92  fof(f97,plain,(
% 4.14/0.92    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.14/0.92    inference(rectify,[],[f96])).
% 4.14/0.92  fof(f96,plain,(
% 4.14/0.92    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.14/0.92    inference(nnf_transformation,[],[f56])).
% 4.14/0.92  fof(f56,plain,(
% 4.14/0.92    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.14/0.92    inference(flattening,[],[f55])).
% 4.14/0.92  fof(f55,plain,(
% 4.14/0.92    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.14/0.92    inference(ennf_transformation,[],[f18])).
% 4.14/0.92  fof(f18,axiom,(
% 4.14/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 4.14/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).
% 4.14/0.92  fof(f177,plain,(
% 4.14/0.92    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2)))) | v3_pre_topc(X2,k6_tmap_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.14/0.92    inference(equality_resolution,[],[f144])).
% 4.14/0.92  fof(f144,plain,(
% 4.14/0.92    ( ! [X2,X0,X1] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.14/0.92    inference(cnf_transformation,[],[f62])).
% 4.14/0.92  fof(f62,plain,(
% 4.14/0.92    ! [X0] : (! [X1] : (! [X2] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.14/0.92    inference(flattening,[],[f61])).
% 4.14/0.92  fof(f61,plain,(
% 4.14/0.92    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.14/0.92    inference(ennf_transformation,[],[f24])).
% 4.14/0.92  fof(f24,axiom,(
% 4.14/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) => (X1 = X2 => v3_pre_topc(X2,k6_tmap_1(X0,X1))))))),
% 4.14/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).
% 4.14/0.92  fof(f5709,plain,(
% 4.14/0.92    ~v3_pre_topc(u1_struct_0(sK1),k8_tmap_1(sK0,sK1)) | v1_tsep_1(sK1,k8_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK1,k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl4_99),
% 4.14/0.92    inference(superposition,[],[f129,f4884])).
% 4.14/0.92  fof(f4884,plain,(
% 4.14/0.92    u1_struct_0(sK1) = sK2(k8_tmap_1(sK0,sK1),sK1) | ~spl4_99),
% 4.14/0.92    inference(avatar_component_clause,[],[f4883])).
% 4.14/0.92  fof(f129,plain,(
% 4.14/0.92    ( ! [X0,X1] : (~v3_pre_topc(sK2(X0,X1),X0) | v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.14/0.92    inference(cnf_transformation,[],[f93])).
% 4.14/0.92  fof(f93,plain,(
% 4.14/0.92    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.14/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f91,f92])).
% 4.14/0.92  fof(f92,plain,(
% 4.14/0.92    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.14/0.92    introduced(choice_axiom,[])).
% 4.14/0.92  fof(f91,plain,(
% 4.14/0.92    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.14/0.92    inference(rectify,[],[f90])).
% 4.14/0.92  fof(f90,plain,(
% 4.14/0.92    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.14/0.92    inference(nnf_transformation,[],[f48])).
% 4.14/0.92  fof(f48,plain,(
% 4.14/0.92    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.14/0.92    inference(flattening,[],[f47])).
% 4.14/0.92  fof(f47,plain,(
% 4.14/0.92    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.14/0.92    inference(ennf_transformation,[],[f19])).
% 4.14/0.93  fof(f19,axiom,(
% 4.14/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 4.14/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).
% 4.14/0.93  % (4051)Termination reason: Time limit
% 4.14/0.93  fof(f5705,plain,(
% 4.14/0.93    spl4_16 | ~spl4_2 | ~spl4_98 | ~spl4_115),
% 4.14/0.93    inference(avatar_split_clause,[],[f5703,f5681,f4880,f235,f1122])).
% 4.14/0.93  % (4039)Time limit reached!
% 4.14/0.93  % (4039)------------------------------
% 4.14/0.93  % (4039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.14/0.93  % (4039)Termination reason: Time limit
% 4.14/0.93  
% 4.14/0.93  fof(f1122,plain,(
% 4.14/0.93    spl4_16 <=> v2_struct_0(k8_tmap_1(sK0,sK1))),
% 4.14/0.93    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 4.14/0.93  fof(f5681,plain,(
% 4.14/0.93    spl4_115 <=> ! [X1] : (~m1_pre_topc(sK0,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_tsep_1(sK1,X1))),
% 4.14/0.93    introduced(avatar_definition,[new_symbols(naming,[spl4_115])])).
% 4.14/0.93  % (4039)Memory used [KB]: 8955
% 4.14/0.93  % (4039)Time elapsed: 0.507 s
% 4.14/0.93  % (4039)------------------------------
% 4.14/0.93  % (4039)------------------------------
% 4.14/0.93  fof(f5703,plain,(
% 4.14/0.93    v2_struct_0(k8_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_98 | ~spl4_115)),
% 4.14/0.93    inference(subsumption_resolution,[],[f5702,f2219])).
% 4.14/0.93  fof(f2219,plain,(
% 4.14/0.93    m1_pre_topc(sK0,k8_tmap_1(sK0,sK1)) | ~spl4_2),
% 4.14/0.93    inference(superposition,[],[f280,f236])).
% 4.14/0.93  fof(f280,plain,(
% 4.14/0.93    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 4.14/0.93    inference(subsumption_resolution,[],[f279,f108])).
% 4.14/0.93  fof(f279,plain,(
% 4.14/0.93    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0)),
% 4.14/0.93    inference(duplicate_literal_removal,[],[f261])).
% 4.14/0.93  fof(f261,plain,(
% 4.14/0.93    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK0)),
% 4.14/0.93    inference(resolution,[],[f191,f120])).
% 4.14/0.93  fof(f120,plain,(
% 4.14/0.93    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 4.14/0.93    inference(cnf_transformation,[],[f89])).
% 4.14/0.93  fof(f89,plain,(
% 4.14/0.93    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.14/0.93    inference(nnf_transformation,[],[f43])).
% 4.14/0.93  fof(f43,plain,(
% 4.14/0.93    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 4.14/0.93    inference(ennf_transformation,[],[f17])).
% 4.14/0.93  fof(f17,axiom,(
% 4.14/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 4.14/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 4.14/0.93  fof(f191,plain,(
% 4.14/0.93    m1_pre_topc(sK0,sK0)),
% 4.14/0.93    inference(resolution,[],[f108,f117])).
% 4.14/0.93  fof(f117,plain,(
% 4.14/0.93    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 4.14/0.93    inference(cnf_transformation,[],[f38])).
% 4.14/0.93  fof(f38,plain,(
% 4.14/0.93    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 4.14/0.93    inference(ennf_transformation,[],[f30])).
% 4.14/0.93  fof(f30,axiom,(
% 4.14/0.93    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 4.14/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 4.14/0.93  fof(f5702,plain,(
% 4.14/0.93    v2_struct_0(k8_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK0,k8_tmap_1(sK0,sK1)) | (~spl4_98 | ~spl4_115)),
% 4.14/0.93    inference(subsumption_resolution,[],[f5701,f230])).
% 4.14/0.93  fof(f5701,plain,(
% 4.14/0.93    v2_struct_0(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK0,k8_tmap_1(sK0,sK1)) | (~spl4_98 | ~spl4_115)),
% 4.14/0.93    inference(subsumption_resolution,[],[f5700,f227])).
% 4.14/0.93  fof(f5700,plain,(
% 4.14/0.93    v2_struct_0(k8_tmap_1(sK0,sK1)) | ~v2_pre_topc(k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~m1_pre_topc(sK0,k8_tmap_1(sK0,sK1)) | (~spl4_98 | ~spl4_115)),
% 4.14/0.93    inference(resolution,[],[f4881,f5682])).
% 4.14/0.93  fof(f5682,plain,(
% 4.14/0.93    ( ! [X1] : (~v1_tsep_1(sK1,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK0,X1)) ) | ~spl4_115),
% 4.14/0.93    inference(avatar_component_clause,[],[f5681])).
% 4.14/0.93  fof(f4881,plain,(
% 4.14/0.93    v1_tsep_1(sK1,k8_tmap_1(sK0,sK1)) | ~spl4_98),
% 4.14/0.93    inference(avatar_component_clause,[],[f4880])).
% 4.14/0.93  fof(f5683,plain,(
% 4.14/0.93    spl4_115 | spl4_1),
% 4.14/0.93    inference(avatar_split_clause,[],[f1353,f232,f5681])).
% 4.14/0.93  fof(f232,plain,(
% 4.14/0.93    spl4_1 <=> v1_tsep_1(sK1,sK0)),
% 4.14/0.93    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 4.14/0.93  fof(f1353,plain,(
% 4.14/0.93    ( ! [X1] : (v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK0,X1) | ~v1_tsep_1(sK1,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 4.14/0.93    inference(subsumption_resolution,[],[f1352,f202])).
% 4.14/0.93  fof(f202,plain,(
% 4.14/0.93    ( ! [X0] : (~m1_pre_topc(sK0,X0) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.14/0.93    inference(resolution,[],[f110,f152])).
% 4.14/0.93  fof(f152,plain,(
% 4.14/0.93    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.14/0.93    inference(cnf_transformation,[],[f72])).
% 4.14/0.93  fof(f72,plain,(
% 4.14/0.93    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.14/0.93    inference(flattening,[],[f71])).
% 4.14/0.93  fof(f71,plain,(
% 4.14/0.93    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.14/0.93    inference(ennf_transformation,[],[f32])).
% 4.14/0.93  fof(f32,axiom,(
% 4.14/0.93    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 4.14/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 4.14/0.93  fof(f1352,plain,(
% 4.14/0.93    ( ! [X1] : (v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK0,X1) | ~m1_pre_topc(sK1,X1) | ~v1_tsep_1(sK1,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 4.14/0.93    inference(subsumption_resolution,[],[f747,f106])).
% 4.14/0.93  fof(f747,plain,(
% 4.14/0.93    ( ! [X1] : (v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK0,X1) | v2_struct_0(sK0) | ~m1_pre_topc(sK1,X1) | ~v1_tsep_1(sK1,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 4.14/0.93    inference(resolution,[],[f440,f147])).
% 4.14/0.93  fof(f147,plain,(
% 4.14/0.93    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | v1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.14/0.93    inference(cnf_transformation,[],[f66])).
% 4.14/0.93  fof(f66,plain,(
% 4.14/0.93    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.14/0.93    inference(flattening,[],[f65])).
% 4.14/0.93  fof(f65,plain,(
% 4.14/0.93    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.14/0.93    inference(ennf_transformation,[],[f28])).
% 4.14/0.93  fof(f28,axiom,(
% 4.14/0.93    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 4.14/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).
% 4.14/0.93  fof(f440,plain,(
% 4.14/0.93    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 4.14/0.93    inference(resolution,[],[f210,f169])).
% 4.14/0.93  fof(f169,plain,(
% 4.14/0.93    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 4.14/0.93    inference(cnf_transformation,[],[f105])).
% 4.14/0.93  fof(f105,plain,(
% 4.14/0.93    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.14/0.93    inference(nnf_transformation,[],[f5])).
% 4.14/0.93  fof(f5,axiom,(
% 4.14/0.93    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.14/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 4.14/0.93  fof(f4885,plain,(
% 4.14/0.93    spl4_98 | spl4_99 | ~spl4_2 | ~spl4_5),
% 4.14/0.93    inference(avatar_split_clause,[],[f2261,f694,f235,f4883,f4880])).
% 4.14/0.93  fof(f2261,plain,(
% 4.14/0.93    u1_struct_0(sK1) = sK2(k8_tmap_1(sK0,sK1),sK1) | v1_tsep_1(sK1,k8_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_5)),
% 4.14/0.93    inference(subsumption_resolution,[],[f2244,f230])).
% 4.14/0.93  fof(f2244,plain,(
% 4.14/0.93    u1_struct_0(sK1) = sK2(k8_tmap_1(sK0,sK1),sK1) | v1_tsep_1(sK1,k8_tmap_1(sK0,sK1)) | ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_5)),
% 4.14/0.93    inference(resolution,[],[f2221,f128])).
% 4.14/0.93  fof(f128,plain,(
% 4.14/0.93    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | v1_tsep_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.14/0.93    inference(cnf_transformation,[],[f93])).
% 4.14/0.93  % (4052)Time limit reached!
% 4.14/0.93  % (4052)------------------------------
% 4.14/0.93  % (4052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.14/0.93  % (4052)Termination reason: Time limit
% 4.14/0.93  % (4052)Termination phase: Saturation
% 4.14/0.93  
% 4.14/0.93  % (4052)Memory used [KB]: 4477
% 4.14/0.93  % (4052)Time elapsed: 0.500 s
% 4.14/0.93  % (4052)------------------------------
% 4.14/0.93  % (4052)------------------------------
% 4.14/0.93  fof(f2207,plain,(
% 4.14/0.93    spl4_2 | ~spl4_30),
% 4.14/0.93    inference(avatar_contradiction_clause,[],[f2206])).
% 4.14/0.93  fof(f2206,plain,(
% 4.14/0.93    $false | (spl4_2 | ~spl4_30)),
% 4.14/0.93    inference(subsumption_resolution,[],[f2202,f305])).
% 4.14/0.93  fof(f305,plain,(
% 4.14/0.93    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | spl4_2),
% 4.14/0.93    inference(avatar_component_clause,[],[f235])).
% 4.14/0.93  fof(f2202,plain,(
% 4.14/0.93    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | ~spl4_30),
% 4.14/0.93    inference(superposition,[],[f345,f1825])).
% 4.14/0.93  fof(f1825,plain,(
% 4.14/0.93    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl4_30),
% 4.14/0.93    inference(avatar_component_clause,[],[f1824])).
% 4.14/0.93  fof(f1824,plain,(
% 4.14/0.93    spl4_30 <=> u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))),
% 4.14/0.93    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 4.14/0.93  fof(f345,plain,(
% 4.14/0.93    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1)))),
% 4.14/0.93    inference(forward_demodulation,[],[f344,f218])).
% 4.14/0.93  fof(f344,plain,(
% 4.14/0.93    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))),
% 4.14/0.93    inference(subsumption_resolution,[],[f343,f230])).
% 4.14/0.93  fof(f343,plain,(
% 4.14/0.93    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) | ~l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 4.14/0.93    inference(resolution,[],[f224,f118])).
% 4.14/0.93  fof(f118,plain,(
% 4.14/0.93    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 4.14/0.93    inference(cnf_transformation,[],[f40])).
% 4.14/0.93  fof(f40,plain,(
% 4.14/0.93    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 4.14/0.93    inference(flattening,[],[f39])).
% 4.14/0.93  fof(f39,plain,(
% 4.14/0.93    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 4.14/0.93    inference(ennf_transformation,[],[f7])).
% 4.14/0.93  fof(f7,axiom,(
% 4.14/0.93    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 4.14/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 4.14/0.93  fof(f1826,plain,(
% 4.14/0.93    ~spl4_23 | spl4_30),
% 4.14/0.93    inference(avatar_split_clause,[],[f468,f1824,f1348])).
% 4.14/0.93  fof(f1348,plain,(
% 4.14/0.93    spl4_23 <=> r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 4.14/0.93    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 4.14/0.93  fof(f468,plain,(
% 4.14/0.93    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) | ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 4.14/0.93    inference(forward_demodulation,[],[f467,f447])).
% 4.14/0.93  fof(f447,plain,(
% 4.14/0.93    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))),
% 4.14/0.93    inference(subsumption_resolution,[],[f446,f106])).
% 4.14/0.93  fof(f446,plain,(
% 4.14/0.93    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 4.14/0.93    inference(subsumption_resolution,[],[f445,f107])).
% 4.14/0.93  fof(f445,plain,(
% 4.14/0.93    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.93    inference(subsumption_resolution,[],[f444,f108])).
% 4.14/0.93  fof(f444,plain,(
% 4.14/0.93    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.93    inference(subsumption_resolution,[],[f443,f109])).
% 4.14/0.93  fof(f443,plain,(
% 4.14/0.93    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.93    inference(subsumption_resolution,[],[f426,f110])).
% 4.14/0.93  fof(f426,plain,(
% 4.14/0.93    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.93    inference(resolution,[],[f210,f178])).
% 4.14/0.93  % (4049)Time limit reached!
% 4.14/0.93  % (4049)------------------------------
% 4.14/0.93  % (4049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.14/0.93  fof(f178,plain,(
% 4.14/0.93    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.14/0.93    inference(equality_resolution,[],[f146])).
% 4.14/0.93  fof(f146,plain,(
% 4.14/0.93    ( ! [X2,X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.14/0.93    inference(cnf_transformation,[],[f64])).
% 4.14/0.93  fof(f467,plain,(
% 4.14/0.93    ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1))),
% 4.14/0.93    inference(subsumption_resolution,[],[f466,f106])).
% 4.14/0.93  fof(f466,plain,(
% 4.14/0.93    ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 4.14/0.93    inference(subsumption_resolution,[],[f465,f107])).
% 4.14/0.93  fof(f465,plain,(
% 4.14/0.93    ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.93    inference(subsumption_resolution,[],[f434,f108])).
% 4.14/0.93  fof(f434,plain,(
% 4.14/0.93    ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 4.14/0.93    inference(resolution,[],[f210,f142])).
% 4.14/0.93  fof(f142,plain,(
% 4.14/0.93    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.14/0.93    inference(cnf_transformation,[],[f100])).
% 4.14/0.93  fof(f100,plain,(
% 4.14/0.93    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.14/0.93    inference(nnf_transformation,[],[f60])).
% 4.14/0.93  fof(f60,plain,(
% 4.14/0.93    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.14/0.93    inference(flattening,[],[f59])).
% 4.14/0.93  fof(f59,plain,(
% 4.14/0.93    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.14/0.93    inference(ennf_transformation,[],[f22])).
% 4.14/0.93  fof(f22,axiom,(
% 4.14/0.93    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 4.14/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).
% 4.14/0.93  fof(f1665,plain,(
% 4.14/0.93    ~spl4_16 | spl4_17),
% 4.14/0.93    inference(avatar_contradiction_clause,[],[f1664])).
% 4.14/0.93  fof(f1664,plain,(
% 4.14/0.93    $false | (~spl4_16 | spl4_17)),
% 4.14/0.93    inference(subsumption_resolution,[],[f1663,f1126])).
% 4.14/0.93  fof(f1126,plain,(
% 4.14/0.93    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_17),
% 4.14/0.93    inference(avatar_component_clause,[],[f1125])).
% 4.14/0.93  fof(f1125,plain,(
% 4.14/0.93    spl4_17 <=> v1_xboole_0(u1_struct_0(sK0))),
% 4.14/0.93    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 4.14/0.93  fof(f1663,plain,(
% 4.14/0.93    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_16),
% 4.14/0.93    inference(forward_demodulation,[],[f1662,f218])).
% 4.14/0.93  fof(f1662,plain,(
% 4.14/0.93    v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) | ~spl4_16),
% 4.14/0.93    inference(subsumption_resolution,[],[f1661,f364])).
% 4.14/0.93  fof(f364,plain,(
% 4.14/0.93    l1_struct_0(k8_tmap_1(sK0,sK1))),
% 4.14/0.93    inference(resolution,[],[f230,f116])).
% 4.14/0.93  fof(f116,plain,(
% 4.14/0.93    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 4.14/0.93    inference(cnf_transformation,[],[f37])).
% 4.14/0.93  fof(f37,plain,(
% 4.14/0.93    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.14/0.93    inference(ennf_transformation,[],[f10])).
% 4.14/0.93  fof(f10,axiom,(
% 4.14/0.93    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.14/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 4.14/0.93  fof(f1661,plain,(
% 4.14/0.93    ~l1_struct_0(k8_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) | ~spl4_16),
% 4.14/0.93    inference(resolution,[],[f1123,f155])).
% 4.14/0.93  fof(f155,plain,(
% 4.14/0.93    ( ! [X0] : (~v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))) )),
% 4.14/0.93    inference(cnf_transformation,[],[f76])).
% 4.14/0.93  fof(f76,plain,(
% 4.14/0.93    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 4.14/0.93    inference(flattening,[],[f75])).
% 4.14/0.93  fof(f75,plain,(
% 4.14/0.93    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 4.14/0.93    inference(ennf_transformation,[],[f12])).
% 4.14/0.93  fof(f12,axiom,(
% 4.14/0.93    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 4.14/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).
% 4.14/0.93  fof(f1123,plain,(
% 4.14/0.93    v2_struct_0(k8_tmap_1(sK0,sK1)) | ~spl4_16),
% 4.14/0.93    inference(avatar_component_clause,[],[f1122])).
% 4.14/0.93  fof(f1660,plain,(
% 4.14/0.93    ~spl4_17),
% 4.14/0.93    inference(avatar_contradiction_clause,[],[f1659])).
% 4.14/0.93  fof(f1659,plain,(
% 4.14/0.93    $false | ~spl4_17),
% 4.14/0.93    inference(subsumption_resolution,[],[f1658,f106])).
% 4.14/0.93  fof(f1658,plain,(
% 4.14/0.93    v2_struct_0(sK0) | ~spl4_17),
% 4.14/0.93    inference(subsumption_resolution,[],[f1655,f192])).
% 4.14/0.93  fof(f192,plain,(
% 4.14/0.93    l1_struct_0(sK0)),
% 4.14/0.93    inference(resolution,[],[f108,f116])).
% 4.14/0.93  fof(f1655,plain,(
% 4.14/0.93    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl4_17),
% 4.14/0.93    inference(resolution,[],[f1327,f135])).
% 4.14/0.93  fof(f135,plain,(
% 4.14/0.93    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 4.14/0.93    inference(cnf_transformation,[],[f54])).
% 4.14/0.93  fof(f54,plain,(
% 4.14/0.93    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 4.14/0.93    inference(flattening,[],[f53])).
% 4.14/0.93  fof(f53,plain,(
% 4.14/0.93    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 4.14/0.93    inference(ennf_transformation,[],[f13])).
% 4.14/0.93  fof(f13,axiom,(
% 4.14/0.93    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 4.14/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 4.14/0.93  fof(f1327,plain,(
% 4.14/0.93    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_17),
% 4.14/0.93    inference(avatar_component_clause,[],[f1125])).
% 4.14/0.93  fof(f1351,plain,(
% 4.14/0.93    spl4_23 | ~spl4_18),
% 4.14/0.93    inference(avatar_split_clause,[],[f455,f1129,f1348])).
% 4.14/0.93  fof(f1129,plain,(
% 4.14/0.93    spl4_18 <=> v3_pre_topc(u1_struct_0(sK1),sK0)),
% 4.14/0.93    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 4.14/0.93  fof(f455,plain,(
% 4.14/0.93    ~v3_pre_topc(u1_struct_0(sK1),sK0) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 4.14/0.93    inference(subsumption_resolution,[],[f430,f108])).
% 4.14/0.93  fof(f430,plain,(
% 4.14/0.93    ~v3_pre_topc(u1_struct_0(sK1),sK0) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 4.14/0.93    inference(resolution,[],[f210,f131])).
% 4.14/0.93  fof(f131,plain,(
% 4.14/0.93    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 4.14/0.93    inference(cnf_transformation,[],[f94])).
% 4.14/0.93  fof(f94,plain,(
% 4.14/0.93    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.14/0.93    inference(nnf_transformation,[],[f50])).
% 4.14/0.93  fof(f50,plain,(
% 4.14/0.93    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.14/0.93    inference(ennf_transformation,[],[f9])).
% 4.14/0.93  fof(f9,axiom,(
% 4.14/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 4.14/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 4.14/0.93  fof(f1131,plain,(
% 4.14/0.93    ~spl4_1 | spl4_18),
% 4.14/0.93    inference(avatar_split_clause,[],[f742,f1129,f232])).
% 4.14/0.93  fof(f742,plain,(
% 4.14/0.93    v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK1,sK0)),
% 4.14/0.93    inference(subsumption_resolution,[],[f741,f108])).
% 4.14/0.93  fof(f741,plain,(
% 4.14/0.93    v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 4.14/0.93    inference(subsumption_resolution,[],[f428,f110])).
% 4.14/0.93  fof(f428,plain,(
% 4.14/0.93    v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 4.14/0.93    inference(resolution,[],[f210,f172])).
% 4.14/0.93  fof(f172,plain,(
% 4.14/0.93    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.14/0.93    inference(equality_resolution,[],[f126])).
% 4.14/0.93  fof(f126,plain,(
% 4.14/0.93    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.14/0.93    inference(cnf_transformation,[],[f93])).
% 4.14/0.93  fof(f744,plain,(
% 4.14/0.93    spl4_3),
% 4.14/0.93    inference(avatar_contradiction_clause,[],[f743])).
% 4.14/0.93  fof(f743,plain,(
% 4.14/0.93    $false | spl4_3),
% 4.14/0.93    inference(subsumption_resolution,[],[f304,f110])).
% 4.14/0.93  fof(f304,plain,(
% 4.14/0.93    ~m1_pre_topc(sK1,sK0) | spl4_3),
% 4.14/0.93    inference(avatar_component_clause,[],[f258])).
% 4.14/0.93  fof(f258,plain,(
% 4.14/0.93    spl4_3 <=> m1_pre_topc(sK1,sK0)),
% 4.14/0.93    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 4.14/0.93  fof(f698,plain,(
% 4.14/0.93    spl4_4),
% 4.14/0.93    inference(avatar_contradiction_clause,[],[f697])).
% 4.14/0.93  fof(f697,plain,(
% 4.14/0.93    $false | spl4_4),
% 4.14/0.93    inference(subsumption_resolution,[],[f692,f209])).
% 4.14/0.93  fof(f209,plain,(
% 4.14/0.93    l1_pre_topc(sK1)),
% 4.14/0.93    inference(subsumption_resolution,[],[f194,f108])).
% 4.14/0.93  fof(f194,plain,(
% 4.14/0.93    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 4.14/0.93    inference(resolution,[],[f110,f122])).
% 4.14/0.93  fof(f122,plain,(
% 4.14/0.93    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 4.14/0.93    inference(cnf_transformation,[],[f44])).
% 4.14/0.93  fof(f44,plain,(
% 4.14/0.93    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.14/0.93    inference(ennf_transformation,[],[f11])).
% 4.14/0.93  fof(f11,axiom,(
% 4.14/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 4.14/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 4.14/0.93  fof(f692,plain,(
% 4.14/0.93    ~l1_pre_topc(sK1) | spl4_4),
% 4.14/0.93    inference(avatar_component_clause,[],[f691])).
% 4.14/0.93  fof(f691,plain,(
% 4.14/0.93    spl4_4 <=> l1_pre_topc(sK1)),
% 4.14/0.93    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 4.14/0.93  fof(f696,plain,(
% 4.14/0.93    ~spl4_4 | spl4_5),
% 4.14/0.93    inference(avatar_split_clause,[],[f208,f694,f691])).
% 4.14/0.93  fof(f208,plain,(
% 4.14/0.93    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK1)),
% 4.14/0.93    inference(subsumption_resolution,[],[f193,f108])).
% 4.14/0.93  fof(f193,plain,(
% 4.14/0.93    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 4.14/0.93    inference(resolution,[],[f110,f120])).
% 4.14/0.93  fof(f306,plain,(
% 4.14/0.93    ~spl4_1 | ~spl4_3 | ~spl4_2),
% 4.14/0.93    inference(avatar_split_clause,[],[f113,f235,f258,f232])).
% 4.14/0.93  fof(f113,plain,(
% 4.14/0.93    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)),
% 4.14/0.93    inference(cnf_transformation,[],[f88])).
% 4.14/0.93  fof(f237,plain,(
% 4.14/0.93    spl4_1 | spl4_2),
% 4.14/0.93    inference(avatar_split_clause,[],[f111,f235,f232])).
% 4.14/0.93  fof(f111,plain,(
% 4.14/0.93    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | v1_tsep_1(sK1,sK0)),
% 4.14/0.93    inference(cnf_transformation,[],[f88])).
% 4.14/0.93  % SZS output end Proof for theBenchmark
% 4.14/0.93  % (4037)------------------------------
% 4.14/0.93  % (4037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.14/0.93  % (4037)Termination reason: Refutation
% 4.14/0.93  
% 4.14/0.93  % (4037)Memory used [KB]: 13560
% 4.14/0.93  % (4037)Time elapsed: 0.504 s
% 4.14/0.93  % (4037)------------------------------
% 4.14/0.93  % (4037)------------------------------
% 4.14/0.93  % (4049)Termination reason: Time limit
% 4.14/0.93  % (4049)Termination phase: Saturation
% 4.14/0.93  
% 4.14/0.93  % (4049)Memory used [KB]: 2686
% 4.14/0.93  % (4049)Time elapsed: 0.500 s
% 4.14/0.93  % (4049)------------------------------
% 4.14/0.93  % (4049)------------------------------
% 4.14/0.93  
% 4.14/0.93  % (4051)Memory used [KB]: 7675
% 4.14/0.93  % (4051)Time elapsed: 0.510 s
% 4.14/0.93  % (4051)------------------------------
% 4.14/0.93  % (4051)------------------------------
% 4.14/0.93  % (4029)Success in time 0.564 s
% 4.43/0.93  % (4034)Time limit reached!
% 4.43/0.93  % (4034)------------------------------
% 4.43/0.93  % (4034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
%------------------------------------------------------------------------------
