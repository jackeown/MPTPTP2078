%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 754 expanded)
%              Number of leaves         :   21 ( 173 expanded)
%              Depth                    :   20
%              Number of atoms          :  537 (4039 expanded)
%              Number of equality atoms :   27 ( 410 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f626,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f82,f83,f293,f296,f308,f328,f481,f586,f588,f590,f600,f610,f625])).

fof(f625,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_21 ),
    inference(avatar_contradiction_clause,[],[f624])).

fof(f624,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_21 ),
    inference(subsumption_resolution,[],[f623,f226])).

fof(f226,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK1),sK0)
    | spl3_21 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl3_21
  <=> v3_pre_topc(k2_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f623,plain,
    ( v3_pre_topc(k2_struct_0(sK1),sK0)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f622,f91])).

fof(f91,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f40,f88])).

fof(f88,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f41,f37])).

fof(f37,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

% (19655)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                 => ( ( m1_pre_topc(X1,X0)
                      & v1_tsep_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tmap_1)).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f622,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f621,f66])).

fof(f66,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_1
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f621,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f70,f233])).

fof(f233,plain,(
    ! [X2] :
      ( ~ v1_tsep_1(X2,sK0)
      | v3_pre_topc(u1_struct_0(X2),sK0)
      | ~ m1_pre_topc(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f230,f39])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f230,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK0)
      | v3_pre_topc(u1_struct_0(X2),sK0)
      | ~ v1_tsep_1(X2,sK0)
      | ~ m1_pre_topc(X2,sK0) ) ),
    inference(resolution,[],[f86,f38])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(subsumption_resolution,[],[f61,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f70,plain,
    ( v1_tsep_1(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_2
  <=> v1_tsep_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f610,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f609])).

fof(f609,plain,
    ( $false
    | ~ spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f75,f606])).

fof(f606,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f179,f66])).

fof(f179,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f176,f93])).

fof(f93,plain,(
    sK2 = g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(backward_demodulation,[],[f35,f91])).

fof(f35,plain,(
    sK2 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f176,plain,
    ( m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f117,f91])).

fof(f117,plain,(
    ! [X2] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),sK0)
      | ~ m1_pre_topc(X2,sK0) ) ),
    inference(resolution,[],[f43,f39])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f75,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_3
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f600,plain,
    ( ~ spl3_3
    | ~ spl3_21
    | spl3_4
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f599,f301,f77,f224,f73])).

fof(f77,plain,
    ( spl3_4
  <=> v1_tsep_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f301,plain,
    ( spl3_26
  <=> k2_struct_0(sK2) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f599,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | spl3_4
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f535,f79])).

fof(f79,plain,
    ( ~ v1_tsep_1(sK2,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f535,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v1_tsep_1(sK2,sK0)
    | ~ spl3_26 ),
    inference(superposition,[],[f212,f482])).

fof(f482,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK1)
    | ~ spl3_26 ),
    inference(backward_demodulation,[],[f90,f303])).

fof(f303,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK1)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f301])).

% (19654)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f90,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f40,f87])).

fof(f87,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f41,f34])).

fof(f34,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f212,plain,(
    ! [X2] :
      ( ~ v3_pre_topc(u1_struct_0(X2),sK0)
      | ~ m1_pre_topc(X2,sK0)
      | v1_tsep_1(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f209,f39])).

fof(f209,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X2,sK0)
      | ~ v3_pre_topc(u1_struct_0(X2),sK0)
      | v1_tsep_1(X2,sK0) ) ),
    inference(resolution,[],[f85,f38])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f60,f42])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v3_pre_topc(X2,X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f590,plain,
    ( spl3_2
    | ~ spl3_21
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f589,f73,f224,f69])).

fof(f589,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK1),sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f220,f584])).

fof(f584,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f583,f39])).

fof(f583,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK1,sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f582,f74])).

fof(f74,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f582,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(sK1,X1) ) ),
    inference(forward_demodulation,[],[f581,f93])).

% (19661)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f581,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | m1_pre_topc(sK1,X1)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(subsumption_resolution,[],[f580,f34])).

fof(f580,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(sK1,X1)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(forward_demodulation,[],[f579,f93])).

fof(f579,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(sK1,X1)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(subsumption_resolution,[],[f578,f33])).

fof(f33,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f578,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(sK1,X1)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(forward_demodulation,[],[f577,f93])).

fof(f577,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(sK1,X1)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(subsumption_resolution,[],[f576,f37])).

fof(f576,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(sK1)
      | m1_pre_topc(sK1,X1)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(subsumption_resolution,[],[f574,f36])).

fof(f36,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f574,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | m1_pre_topc(sK1,X1)
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1) ) ),
    inference(superposition,[],[f58,f91])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f220,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(superposition,[],[f212,f91])).

fof(f588,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_21
    | ~ spl3_26 ),
    inference(avatar_contradiction_clause,[],[f587])).

fof(f587,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_21
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f226,f494])).

fof(f494,plain,
    ( v3_pre_topc(k2_struct_0(sK1),sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_26 ),
    inference(backward_demodulation,[],[f236,f303])).

fof(f236,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f235,f90])).

fof(f235,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f234,f74])).

fof(f234,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f233,f78])).

fof(f78,plain,
    ( v1_tsep_1(sK2,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f586,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f585])).

fof(f585,plain,
    ( $false
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f584,f67])).

fof(f67,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f481,plain,
    ( spl3_27
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f480])).

fof(f480,plain,
    ( $false
    | spl3_27
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f479,f307])).

fof(f307,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl3_27
  <=> r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f479,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1))
    | ~ spl3_28 ),
    inference(resolution,[],[f478,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f478,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f477,f33])).

fof(f477,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ v2_pre_topc(sK2)
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f476,f34])).

fof(f476,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f474,f318])).

fof(f318,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl3_28
  <=> m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f474,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[],[f469,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f469,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f468,f91])).

fof(f468,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ v3_pre_topc(X1,sK2)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f467,f90])).

fof(f467,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(X1,sK2)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f466,f93])).

fof(f466,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))))
      | ~ v3_pre_topc(X1,sK2)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f465,f91])).

fof(f465,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f464,f93])).

fof(f464,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f463,f91])).

fof(f463,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f457,f37])).

fof(f457,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK1)
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(resolution,[],[f49,f36])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).

fof(f328,plain,(
    spl3_28 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | spl3_28 ),
    inference(subsumption_resolution,[],[f326,f62])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f326,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2))
    | spl3_28 ),
    inference(resolution,[],[f319,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f319,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))
    | spl3_28 ),
    inference(avatar_component_clause,[],[f317])).

fof(f308,plain,
    ( spl3_26
    | ~ spl3_27
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f299,f290,f305,f301])).

fof(f290,plain,
    ( spl3_25
  <=> m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f299,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1))
    | k2_struct_0(sK2) = k2_struct_0(sK1)
    | ~ spl3_25 ),
    inference(resolution,[],[f298,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f298,plain,
    ( r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ spl3_25 ),
    inference(resolution,[],[f292,f57])).

fof(f292,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f290])).

fof(f296,plain,(
    spl3_24 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl3_24 ),
    inference(subsumption_resolution,[],[f294,f62])).

fof(f294,plain,
    ( ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(sK1))
    | spl3_24 ),
    inference(resolution,[],[f288,f56])).

fof(f288,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1)))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl3_24
  <=> m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f293,plain,
    ( ~ spl3_24
    | spl3_25 ),
    inference(avatar_split_clause,[],[f284,f290,f286])).

fof(f284,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f283,f36])).

fof(f283,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f282,f37])).

fof(f282,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f277,f46])).

fof(f277,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK1)
      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f276,f91])).

fof(f276,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f275,f90])).

fof(f275,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f274,f93])).

% (19651)Refutation not found, incomplete strategy% (19651)------------------------------
% (19651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f274,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))))
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f273,f91])).

fof(f273,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f268,f37])).

fof(f268,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK1)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(resolution,[],[f52,f36])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f29,f73,f65])).

fof(f29,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f82,plain,
    ( spl3_2
    | spl3_4 ),
    inference(avatar_split_clause,[],[f30,f77,f69])).

fof(f30,plain,
    ( v1_tsep_1(sK2,sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f32,f77,f73,f69,f65])).

fof(f32,plain,
    ( ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:32:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (19650)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (19657)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (19670)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.50  % (19650)Refutation not found, incomplete strategy% (19650)------------------------------
% 0.21/0.50  % (19650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19667)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (19665)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (19653)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (19666)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (19659)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (19658)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (19648)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (19647)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (19652)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (19667)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (19658)Refutation not found, incomplete strategy% (19658)------------------------------
% 0.21/0.51  % (19658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19652)Refutation not found, incomplete strategy% (19652)------------------------------
% 0.21/0.51  % (19652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19652)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19652)Memory used [KB]: 1663
% 0.21/0.51  % (19652)Time elapsed: 0.097 s
% 0.21/0.51  % (19652)------------------------------
% 0.21/0.51  % (19652)------------------------------
% 0.21/0.51  % (19650)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19650)Memory used [KB]: 6140
% 0.21/0.51  % (19650)Time elapsed: 0.088 s
% 0.21/0.51  % (19650)------------------------------
% 0.21/0.51  % (19650)------------------------------
% 0.21/0.52  % (19649)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (19645)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (19656)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (19646)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (19651)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (19645)Refutation not found, incomplete strategy% (19645)------------------------------
% 0.21/0.52  % (19645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19645)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19645)Memory used [KB]: 10618
% 0.21/0.52  % (19645)Time elapsed: 0.109 s
% 0.21/0.52  % (19645)------------------------------
% 0.21/0.52  % (19645)------------------------------
% 0.21/0.52  % (19664)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (19663)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f626,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f80,f82,f83,f293,f296,f308,f328,f481,f586,f588,f590,f600,f610,f625])).
% 0.21/0.53  fof(f625,plain,(
% 0.21/0.53    ~spl3_1 | ~spl3_2 | spl3_21),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f624])).
% 0.21/0.53  fof(f624,plain,(
% 0.21/0.53    $false | (~spl3_1 | ~spl3_2 | spl3_21)),
% 0.21/0.53    inference(subsumption_resolution,[],[f623,f226])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    ~v3_pre_topc(k2_struct_0(sK1),sK0) | spl3_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f224])).
% 0.21/0.53  fof(f224,plain,(
% 0.21/0.53    spl3_21 <=> v3_pre_topc(k2_struct_0(sK1),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.53  fof(f623,plain,(
% 0.21/0.53    v3_pre_topc(k2_struct_0(sK1),sK0) | (~spl3_1 | ~spl3_2)),
% 0.21/0.53    inference(forward_demodulation,[],[f622,f91])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.53    inference(resolution,[],[f40,f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    l1_struct_0(sK1)),
% 0.21/0.53    inference(resolution,[],[f41,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    l1_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  % (19655)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tmap_1)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.53  fof(f622,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK1),sK0) | (~spl3_1 | ~spl3_2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f621,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    m1_pre_topc(sK1,sK0) | ~spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    spl3_1 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f621,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK1),sK0) | ~m1_pre_topc(sK1,sK0) | ~spl3_2),
% 0.21/0.53    inference(resolution,[],[f70,f233])).
% 0.21/0.53  fof(f233,plain,(
% 0.21/0.53    ( ! [X2] : (~v1_tsep_1(X2,sK0) | v3_pre_topc(u1_struct_0(X2),sK0) | ~m1_pre_topc(X2,sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f230,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f230,plain,(
% 0.21/0.53    ( ! [X2] : (~l1_pre_topc(sK0) | v3_pre_topc(u1_struct_0(X2),sK0) | ~v1_tsep_1(X2,sK0) | ~m1_pre_topc(X2,sK0)) )),
% 0.21/0.53    inference(resolution,[],[f86,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f61,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    v1_tsep_1(sK1,sK0) | ~spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    spl3_2 <=> v1_tsep_1(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.53  fof(f610,plain,(
% 0.21/0.53    ~spl3_1 | spl3_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f609])).
% 0.21/0.53  fof(f609,plain,(
% 0.21/0.53    $false | (~spl3_1 | spl3_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f75,f606])).
% 0.21/0.53  fof(f606,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK0) | ~spl3_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f179,f66])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f176,f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    sK2 = g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.53    inference(backward_demodulation,[],[f35,f91])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    sK2 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),sK0) | ~m1_pre_topc(sK1,sK0)),
% 0.21/0.53    inference(superposition,[],[f117,f91])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ( ! [X2] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),sK0) | ~m1_pre_topc(X2,sK0)) )),
% 0.21/0.53    inference(resolution,[],[f43,f39])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ~m1_pre_topc(sK2,sK0) | spl3_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    spl3_3 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.53  fof(f600,plain,(
% 0.21/0.53    ~spl3_3 | ~spl3_21 | spl3_4 | ~spl3_26),
% 0.21/0.53    inference(avatar_split_clause,[],[f599,f301,f77,f224,f73])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    spl3_4 <=> v1_tsep_1(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.53  fof(f301,plain,(
% 0.21/0.53    spl3_26 <=> k2_struct_0(sK2) = k2_struct_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.53  fof(f599,plain,(
% 0.21/0.53    ~v3_pre_topc(k2_struct_0(sK1),sK0) | ~m1_pre_topc(sK2,sK0) | (spl3_4 | ~spl3_26)),
% 0.21/0.53    inference(subsumption_resolution,[],[f535,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ~v1_tsep_1(sK2,sK0) | spl3_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f77])).
% 0.21/0.53  fof(f535,plain,(
% 0.21/0.53    ~v3_pre_topc(k2_struct_0(sK1),sK0) | ~m1_pre_topc(sK2,sK0) | v1_tsep_1(sK2,sK0) | ~spl3_26),
% 0.21/0.53    inference(superposition,[],[f212,f482])).
% 0.21/0.53  fof(f482,plain,(
% 0.21/0.53    u1_struct_0(sK2) = k2_struct_0(sK1) | ~spl3_26),
% 0.21/0.53    inference(backward_demodulation,[],[f90,f303])).
% 0.21/0.53  fof(f303,plain,(
% 0.21/0.53    k2_struct_0(sK2) = k2_struct_0(sK1) | ~spl3_26),
% 0.21/0.53    inference(avatar_component_clause,[],[f301])).
% 0.21/0.53  % (19654)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f40,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    l1_struct_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f41,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    l1_pre_topc(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    ( ! [X2] : (~v3_pre_topc(u1_struct_0(X2),sK0) | ~m1_pre_topc(X2,sK0) | v1_tsep_1(X2,sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f209,f39])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    ( ! [X2] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X2,sK0) | ~v3_pre_topc(u1_struct_0(X2),sK0) | v1_tsep_1(X2,sK0)) )),
% 0.21/0.53    inference(resolution,[],[f85,f38])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f60,f42])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v3_pre_topc(X2,X0) | v1_tsep_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f590,plain,(
% 0.21/0.53    spl3_2 | ~spl3_21 | ~spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f589,f73,f224,f69])).
% 0.21/0.53  fof(f589,plain,(
% 0.21/0.53    ~v3_pre_topc(k2_struct_0(sK1),sK0) | v1_tsep_1(sK1,sK0) | ~spl3_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f220,f584])).
% 0.21/0.53  fof(f584,plain,(
% 0.21/0.53    m1_pre_topc(sK1,sK0) | ~spl3_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f583,f39])).
% 0.21/0.53  fof(f583,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | m1_pre_topc(sK1,sK0) | ~spl3_3),
% 0.21/0.53    inference(resolution,[],[f582,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK0) | ~spl3_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f73])).
% 0.21/0.53  fof(f582,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | m1_pre_topc(sK1,X1)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f581,f93])).
% 0.21/0.53  % (19661)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  fof(f581,plain,(
% 0.21/0.53    ( ! [X1] : (~l1_pre_topc(X1) | m1_pre_topc(sK1,X1) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f580,f34])).
% 0.21/0.53  fof(f580,plain,(
% 0.21/0.53    ( ! [X1] : (~l1_pre_topc(sK2) | ~l1_pre_topc(X1) | m1_pre_topc(sK1,X1) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f579,f93])).
% 0.21/0.53  fof(f579,plain,(
% 0.21/0.53    ( ! [X1] : (~l1_pre_topc(X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(sK1,X1) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f578,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    v2_pre_topc(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f578,plain,(
% 0.21/0.53    ( ! [X1] : (~v2_pre_topc(sK2) | ~l1_pre_topc(X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(sK1,X1) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f577,f93])).
% 0.21/0.53  fof(f577,plain,(
% 0.21/0.53    ( ! [X1] : (~v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(sK1,X1) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f576,f37])).
% 0.21/0.53  fof(f576,plain,(
% 0.21/0.53    ( ! [X1] : (~v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | m1_pre_topc(sK1,X1) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f574,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    v2_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f574,plain,(
% 0.21/0.53    ( ! [X1] : (~v2_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | m1_pre_topc(sK1,X1) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)),X1)) )),
% 0.21/0.53    inference(superposition,[],[f58,f91])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    ~v3_pre_topc(k2_struct_0(sK1),sK0) | ~m1_pre_topc(sK1,sK0) | v1_tsep_1(sK1,sK0)),
% 0.21/0.53    inference(superposition,[],[f212,f91])).
% 0.21/0.53  fof(f588,plain,(
% 0.21/0.53    ~spl3_3 | ~spl3_4 | spl3_21 | ~spl3_26),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f587])).
% 0.21/0.53  fof(f587,plain,(
% 0.21/0.53    $false | (~spl3_3 | ~spl3_4 | spl3_21 | ~spl3_26)),
% 0.21/0.53    inference(subsumption_resolution,[],[f226,f494])).
% 0.21/0.53  fof(f494,plain,(
% 0.21/0.53    v3_pre_topc(k2_struct_0(sK1),sK0) | (~spl3_3 | ~spl3_4 | ~spl3_26)),
% 0.21/0.53    inference(backward_demodulation,[],[f236,f303])).
% 0.21/0.53  fof(f236,plain,(
% 0.21/0.53    v3_pre_topc(k2_struct_0(sK2),sK0) | (~spl3_3 | ~spl3_4)),
% 0.21/0.53    inference(forward_demodulation,[],[f235,f90])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK2),sK0) | (~spl3_3 | ~spl3_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f234,f74])).
% 0.21/0.53  fof(f234,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK2),sK0) | ~m1_pre_topc(sK2,sK0) | ~spl3_4),
% 0.21/0.53    inference(resolution,[],[f233,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    v1_tsep_1(sK2,sK0) | ~spl3_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f77])).
% 0.21/0.53  fof(f586,plain,(
% 0.21/0.53    spl3_1 | ~spl3_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f585])).
% 0.21/0.53  fof(f585,plain,(
% 0.21/0.53    $false | (spl3_1 | ~spl3_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f584,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ~m1_pre_topc(sK1,sK0) | spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f65])).
% 0.21/0.53  fof(f481,plain,(
% 0.21/0.53    spl3_27 | ~spl3_28),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f480])).
% 0.21/0.53  fof(f480,plain,(
% 0.21/0.53    $false | (spl3_27 | ~spl3_28)),
% 0.21/0.53    inference(subsumption_resolution,[],[f479,f307])).
% 0.21/0.53  fof(f307,plain,(
% 0.21/0.53    ~r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) | spl3_27),
% 0.21/0.53    inference(avatar_component_clause,[],[f305])).
% 0.21/0.53  fof(f305,plain,(
% 0.21/0.53    spl3_27 <=> r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.53  fof(f479,plain,(
% 0.21/0.53    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) | ~spl3_28),
% 0.21/0.53    inference(resolution,[],[f478,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f478,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) | ~spl3_28),
% 0.21/0.53    inference(subsumption_resolution,[],[f477,f33])).
% 0.21/0.53  fof(f477,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) | ~v2_pre_topc(sK2) | ~spl3_28),
% 0.21/0.53    inference(subsumption_resolution,[],[f476,f34])).
% 0.21/0.53  fof(f476,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~spl3_28),
% 0.21/0.53    inference(subsumption_resolution,[],[f474,f318])).
% 0.21/0.53  fof(f318,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) | ~spl3_28),
% 0.21/0.53    inference(avatar_component_clause,[],[f317])).
% 0.21/0.53  fof(f317,plain,(
% 0.21/0.53    spl3_28 <=> m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.53  fof(f474,plain,(
% 0.21/0.53    ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 0.21/0.53    inference(resolution,[],[f469,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.21/0.53  fof(f469,plain,(
% 0.21/0.53    ( ! [X1] : (~v3_pre_topc(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f468,f91])).
% 0.21/0.53  fof(f468,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | ~v3_pre_topc(X1,sK2) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f467,f90])).
% 0.21/0.53  fof(f467,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(X1,sK2) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f466,f93])).
% 0.21/0.53  fof(f466,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) | ~v3_pre_topc(X1,sK2) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f465,f91])).
% 0.21/0.53  fof(f465,plain,(
% 0.21/0.53    ( ! [X1] : (~v3_pre_topc(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f464,f93])).
% 0.21/0.53  fof(f464,plain,(
% 0.21/0.53    ( ! [X1] : (~v3_pre_topc(X1,g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f463,f91])).
% 0.21/0.53  fof(f463,plain,(
% 0.21/0.53    ( ! [X1] : (~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f457,f37])).
% 0.21/0.53  fof(f457,plain,(
% 0.21/0.53    ( ! [X1] : (~l1_pre_topc(sK1) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(resolution,[],[f49,f36])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).
% 0.21/0.53  fof(f328,plain,(
% 0.21/0.53    spl3_28),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f327])).
% 0.21/0.53  fof(f327,plain,(
% 0.21/0.53    $false | spl3_28),
% 0.21/0.53    inference(subsumption_resolution,[],[f326,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f326,plain,(
% 0.21/0.53    ~r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) | spl3_28),
% 0.21/0.53    inference(resolution,[],[f319,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f319,plain,(
% 0.21/0.53    ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) | spl3_28),
% 0.21/0.53    inference(avatar_component_clause,[],[f317])).
% 0.21/0.53  fof(f308,plain,(
% 0.21/0.53    spl3_26 | ~spl3_27 | ~spl3_25),
% 0.21/0.53    inference(avatar_split_clause,[],[f299,f290,f305,f301])).
% 0.21/0.53  fof(f290,plain,(
% 0.21/0.53    spl3_25 <=> m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.53  fof(f299,plain,(
% 0.21/0.53    ~r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) | k2_struct_0(sK2) = k2_struct_0(sK1) | ~spl3_25),
% 0.21/0.53    inference(resolution,[],[f298,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f298,plain,(
% 0.21/0.53    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) | ~spl3_25),
% 0.21/0.53    inference(resolution,[],[f292,f57])).
% 0.21/0.53  fof(f292,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) | ~spl3_25),
% 0.21/0.53    inference(avatar_component_clause,[],[f290])).
% 0.21/0.53  fof(f296,plain,(
% 0.21/0.53    spl3_24),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f295])).
% 0.21/0.53  fof(f295,plain,(
% 0.21/0.53    $false | spl3_24),
% 0.21/0.53    inference(subsumption_resolution,[],[f294,f62])).
% 0.21/0.53  fof(f294,plain,(
% 0.21/0.53    ~r1_tarski(k2_struct_0(sK1),k2_struct_0(sK1)) | spl3_24),
% 0.21/0.53    inference(resolution,[],[f288,f56])).
% 0.21/0.53  fof(f288,plain,(
% 0.21/0.53    ~m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) | spl3_24),
% 0.21/0.53    inference(avatar_component_clause,[],[f286])).
% 0.21/0.53  fof(f286,plain,(
% 0.21/0.53    spl3_24 <=> m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    ~spl3_24 | spl3_25),
% 0.21/0.53    inference(avatar_split_clause,[],[f284,f290,f286])).
% 0.21/0.53  fof(f284,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f283,f36])).
% 0.21/0.53  fof(f283,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) | ~v2_pre_topc(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f282,f37])).
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.21/0.53    inference(resolution,[],[f277,f46])).
% 0.21/0.53  fof(f277,plain,(
% 0.21/0.53    ( ! [X1] : (~v3_pre_topc(X1,sK1) | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f276,f91])).
% 0.21/0.53  fof(f276,plain,(
% 0.21/0.53    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f275,f90])).
% 0.21/0.53  fof(f275,plain,(
% 0.21/0.53    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f274,f93])).
% 0.21/0.53  % (19651)Refutation not found, incomplete strategy% (19651)------------------------------
% 0.21/0.53  % (19651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  fof(f274,plain,(
% 0.21/0.53    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f273,f91])).
% 0.21/0.53  fof(f273,plain,(
% 0.21/0.53    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f268,f37])).
% 0.21/0.53  fof(f268,plain,(
% 0.21/0.53    ( ! [X1] : (~l1_pre_topc(sK1) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.53    inference(resolution,[],[f52,f36])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    spl3_1 | spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f29,f73,f65])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    spl3_2 | spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f30,f77,f69])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    v1_tsep_1(sK2,sK0) | v1_tsep_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f32,f77,f73,f69,f65])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ~v1_tsep_1(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (19667)------------------------------
% 0.21/0.53  % (19667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19667)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (19667)Memory used [KB]: 11001
% 0.21/0.53  % (19667)Time elapsed: 0.067 s
% 0.21/0.53  % (19667)------------------------------
% 0.21/0.53  % (19667)------------------------------
% 0.21/0.53  % (19651)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19651)Memory used [KB]: 10618
% 0.21/0.53  % (19651)Time elapsed: 0.093 s
% 0.21/0.53  % (19651)------------------------------
% 0.21/0.53  % (19651)------------------------------
% 0.21/0.53  % (19644)Success in time 0.172 s
%------------------------------------------------------------------------------
