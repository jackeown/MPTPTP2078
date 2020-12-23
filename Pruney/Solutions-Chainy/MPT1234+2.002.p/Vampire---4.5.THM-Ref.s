%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 154 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :    7
%              Number of atoms          :  292 ( 445 expanded)
%              Number of equality atoms :   20 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f310,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f49,f53,f57,f61,f65,f73,f118,f157,f166,f212,f216,f259,f303,f309])).

fof(f309,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_34
    | ~ spl2_45 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_34
    | ~ spl2_45 ),
    inference(subsumption_resolution,[],[f307,f211])).

fof(f211,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl2_34
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f307,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_45 ),
    inference(subsumption_resolution,[],[f306,f39])).

fof(f39,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f306,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_1
    | ~ spl2_8
    | ~ spl2_45 ),
    inference(subsumption_resolution,[],[f304,f34])).

fof(f34,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_1
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f304,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_8
    | ~ spl2_45 ),
    inference(resolution,[],[f302,f64])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
        | r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X1,X2)
        | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f302,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl2_45
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f303,plain,
    ( spl2_45
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_16
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f298,f256,f105,f47,f42,f300])).

fof(f42,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f47,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( r1_tarski(X1,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f105,plain,
    ( spl2_16
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f256,plain,
    ( spl2_40
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f298,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_16
    | ~ spl2_40 ),
    inference(subsumption_resolution,[],[f297,f44])).

fof(f44,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f297,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | ~ spl2_16
    | ~ spl2_40 ),
    inference(subsumption_resolution,[],[f296,f106])).

fof(f106,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f296,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | ~ spl2_40 ),
    inference(superposition,[],[f48,f258])).

fof(f258,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f256])).

fof(f48,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f259,plain,
    ( spl2_40
    | ~ spl2_7
    | ~ spl2_25
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f254,f192,f163,f59,f256])).

fof(f59,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f163,plain,
    ( spl2_25
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f192,plain,
    ( spl2_30
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f254,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_7
    | ~ spl2_25
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f245,f165])).

fof(f165,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f163])).

fof(f245,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_7
    | ~ spl2_30 ),
    inference(resolution,[],[f193,f60])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f193,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f192])).

fof(f216,plain,
    ( ~ spl2_3
    | ~ spl2_10
    | ~ spl2_16
    | spl2_30 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_16
    | spl2_30 ),
    inference(subsumption_resolution,[],[f214,f44])).

fof(f214,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_10
    | ~ spl2_16
    | spl2_30 ),
    inference(subsumption_resolution,[],[f213,f106])).

fof(f213,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_10
    | spl2_30 ),
    inference(resolution,[],[f194,f72])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f194,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_30 ),
    inference(avatar_component_clause,[],[f192])).

fof(f212,plain,
    ( ~ spl2_30
    | spl2_34
    | ~ spl2_6
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f186,f163,f55,f209,f192])).

fof(f55,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f186,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_6
    | ~ spl2_25 ),
    inference(superposition,[],[f56,f165])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f166,plain,
    ( spl2_25
    | ~ spl2_2
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f158,f155,f37,f163])).

fof(f155,plain,
    ( spl2_24
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f158,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_2
    | ~ spl2_24 ),
    inference(resolution,[],[f156,f39])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f155])).

fof(f157,plain,
    ( spl2_24
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f153,f51,f42,f155])).

fof(f51,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(resolution,[],[f52,f44])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f118,plain,
    ( ~ spl2_2
    | ~ spl2_6
    | spl2_16 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_6
    | spl2_16 ),
    inference(subsumption_resolution,[],[f116,f39])).

fof(f116,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_6
    | spl2_16 ),
    inference(resolution,[],[f107,f56])).

fof(f107,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f73,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f30,f71])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f65,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f61,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f57,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f53,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f49,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f24,f47])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f45,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_tops_1(X0,X1),X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_tops_1(sK0,X1),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k1_tops_1(sK0,X1),X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_tops_1(X0,X1),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f40,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f22,f37])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f23,f32])).

fof(f23,plain,(
    ~ r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:50:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (5476)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (5477)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.42  % (5479)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.43  % (5480)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.44  % (5476)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f310,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f35,f40,f45,f49,f53,f57,f61,f65,f73,f118,f157,f166,f212,f216,f259,f303,f309])).
% 0.22/0.44  fof(f309,plain,(
% 0.22/0.44    spl2_1 | ~spl2_2 | ~spl2_8 | ~spl2_34 | ~spl2_45),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f308])).
% 0.22/0.44  fof(f308,plain,(
% 0.22/0.44    $false | (spl2_1 | ~spl2_2 | ~spl2_8 | ~spl2_34 | ~spl2_45)),
% 0.22/0.44    inference(subsumption_resolution,[],[f307,f211])).
% 0.22/0.44  fof(f211,plain,(
% 0.22/0.44    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_34),
% 0.22/0.44    inference(avatar_component_clause,[],[f209])).
% 0.22/0.44  fof(f209,plain,(
% 0.22/0.44    spl2_34 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.22/0.44  fof(f307,plain,(
% 0.22/0.44    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl2_1 | ~spl2_2 | ~spl2_8 | ~spl2_45)),
% 0.22/0.44    inference(subsumption_resolution,[],[f306,f39])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.44  fof(f306,plain,(
% 0.22/0.44    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl2_1 | ~spl2_8 | ~spl2_45)),
% 0.22/0.44    inference(subsumption_resolution,[],[f304,f34])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | spl2_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f32])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    spl2_1 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.44  fof(f304,plain,(
% 0.22/0.44    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_8 | ~spl2_45)),
% 0.22/0.44    inference(resolution,[],[f302,f64])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f63])).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    spl2_8 <=> ! [X1,X0,X2] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.44  fof(f302,plain,(
% 0.22/0.44    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | ~spl2_45),
% 0.22/0.44    inference(avatar_component_clause,[],[f300])).
% 0.22/0.44  fof(f300,plain,(
% 0.22/0.44    spl2_45 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.22/0.44  fof(f303,plain,(
% 0.22/0.44    spl2_45 | ~spl2_3 | ~spl2_4 | ~spl2_16 | ~spl2_40),
% 0.22/0.44    inference(avatar_split_clause,[],[f298,f256,f105,f47,f42,f300])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    spl2_3 <=> l1_pre_topc(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    spl2_4 <=> ! [X1,X0] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.44  fof(f105,plain,(
% 0.22/0.44    spl2_16 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.44  fof(f256,plain,(
% 0.22/0.44    spl2_40 <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.22/0.44  fof(f298,plain,(
% 0.22/0.44    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_4 | ~spl2_16 | ~spl2_40)),
% 0.22/0.44    inference(subsumption_resolution,[],[f297,f44])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    l1_pre_topc(sK0) | ~spl2_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f42])).
% 0.22/0.44  fof(f297,plain,(
% 0.22/0.44    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0) | (~spl2_4 | ~spl2_16 | ~spl2_40)),
% 0.22/0.44    inference(subsumption_resolution,[],[f296,f106])).
% 0.22/0.44  fof(f106,plain,(
% 0.22/0.44    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_16),
% 0.22/0.44    inference(avatar_component_clause,[],[f105])).
% 0.22/0.44  fof(f296,plain,(
% 0.22/0.44    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_4 | ~spl2_40)),
% 0.22/0.44    inference(superposition,[],[f48,f258])).
% 0.22/0.44  fof(f258,plain,(
% 0.22/0.44    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~spl2_40),
% 0.22/0.44    inference(avatar_component_clause,[],[f256])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f47])).
% 0.22/0.44  fof(f259,plain,(
% 0.22/0.44    spl2_40 | ~spl2_7 | ~spl2_25 | ~spl2_30),
% 0.22/0.44    inference(avatar_split_clause,[],[f254,f192,f163,f59,f256])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    spl2_7 <=> ! [X1,X0] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.44  fof(f163,plain,(
% 0.22/0.44    spl2_25 <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.22/0.44  fof(f192,plain,(
% 0.22/0.44    spl2_30 <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.22/0.44  fof(f254,plain,(
% 0.22/0.44    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | (~spl2_7 | ~spl2_25 | ~spl2_30)),
% 0.22/0.44    inference(forward_demodulation,[],[f245,f165])).
% 0.22/0.44  fof(f165,plain,(
% 0.22/0.44    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl2_25),
% 0.22/0.44    inference(avatar_component_clause,[],[f163])).
% 0.22/0.44  fof(f245,plain,(
% 0.22/0.44    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) | (~spl2_7 | ~spl2_30)),
% 0.22/0.44    inference(resolution,[],[f193,f60])).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) ) | ~spl2_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f59])).
% 0.22/0.44  fof(f193,plain,(
% 0.22/0.44    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_30),
% 0.22/0.44    inference(avatar_component_clause,[],[f192])).
% 0.22/0.44  fof(f216,plain,(
% 0.22/0.44    ~spl2_3 | ~spl2_10 | ~spl2_16 | spl2_30),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f215])).
% 0.22/0.44  fof(f215,plain,(
% 0.22/0.44    $false | (~spl2_3 | ~spl2_10 | ~spl2_16 | spl2_30)),
% 0.22/0.44    inference(subsumption_resolution,[],[f214,f44])).
% 0.22/0.44  fof(f214,plain,(
% 0.22/0.44    ~l1_pre_topc(sK0) | (~spl2_10 | ~spl2_16 | spl2_30)),
% 0.22/0.44    inference(subsumption_resolution,[],[f213,f106])).
% 0.22/0.44  fof(f213,plain,(
% 0.22/0.44    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_10 | spl2_30)),
% 0.22/0.44    inference(resolution,[],[f194,f72])).
% 0.22/0.44  fof(f72,plain,(
% 0.22/0.44    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_10),
% 0.22/0.44    inference(avatar_component_clause,[],[f71])).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    spl2_10 <=> ! [X1,X0] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.44  fof(f194,plain,(
% 0.22/0.44    ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_30),
% 0.22/0.44    inference(avatar_component_clause,[],[f192])).
% 0.22/0.44  fof(f212,plain,(
% 0.22/0.44    ~spl2_30 | spl2_34 | ~spl2_6 | ~spl2_25),
% 0.22/0.44    inference(avatar_split_clause,[],[f186,f163,f55,f209,f192])).
% 0.22/0.44  fof(f55,plain,(
% 0.22/0.44    spl2_6 <=> ! [X1,X0] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.44  fof(f186,plain,(
% 0.22/0.44    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_6 | ~spl2_25)),
% 0.22/0.44    inference(superposition,[],[f56,f165])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f55])).
% 0.22/0.44  fof(f166,plain,(
% 0.22/0.44    spl2_25 | ~spl2_2 | ~spl2_24),
% 0.22/0.44    inference(avatar_split_clause,[],[f158,f155,f37,f163])).
% 0.22/0.44  fof(f155,plain,(
% 0.22/0.44    spl2_24 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.22/0.44  fof(f158,plain,(
% 0.22/0.44    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_2 | ~spl2_24)),
% 0.22/0.44    inference(resolution,[],[f156,f39])).
% 0.22/0.44  fof(f156,plain,(
% 0.22/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | ~spl2_24),
% 0.22/0.44    inference(avatar_component_clause,[],[f155])).
% 0.22/0.44  fof(f157,plain,(
% 0.22/0.44    spl2_24 | ~spl2_3 | ~spl2_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f153,f51,f42,f155])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    spl2_5 <=> ! [X1,X0] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.44  fof(f153,plain,(
% 0.22/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | (~spl2_3 | ~spl2_5)),
% 0.22/0.44    inference(resolution,[],[f52,f44])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) ) | ~spl2_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f51])).
% 0.22/0.44  fof(f118,plain,(
% 0.22/0.44    ~spl2_2 | ~spl2_6 | spl2_16),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f117])).
% 0.22/0.44  fof(f117,plain,(
% 0.22/0.44    $false | (~spl2_2 | ~spl2_6 | spl2_16)),
% 0.22/0.44    inference(subsumption_resolution,[],[f116,f39])).
% 0.22/0.44  fof(f116,plain,(
% 0.22/0.44    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_6 | spl2_16)),
% 0.22/0.44    inference(resolution,[],[f107,f56])).
% 0.22/0.44  fof(f107,plain,(
% 0.22/0.44    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_16),
% 0.22/0.44    inference(avatar_component_clause,[],[f105])).
% 0.22/0.44  fof(f73,plain,(
% 0.22/0.44    spl2_10),
% 0.22/0.44    inference(avatar_split_clause,[],[f30,f71])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(flattening,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    spl2_8),
% 0.22/0.44    inference(avatar_split_clause,[],[f29,f63])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(nnf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    spl2_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f27,f59])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    spl2_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f26,f55])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    spl2_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f25,f51])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    spl2_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f24,f47])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    spl2_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f21,f42])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    l1_pre_topc(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    (~r1_tarski(k1_tops_1(sK0,sK1),sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f18,f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : (~r1_tarski(k1_tops_1(X0,X1),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k1_tops_1(sK0,X1),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ? [X1] : (~r1_tarski(k1_tops_1(sK0,X1),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k1_tops_1(sK0,sK1),sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : (~r1_tarski(k1_tops_1(X0,X1),X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,negated_conjecture,(
% 0.22/0.44    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.22/0.44    inference(negated_conjecture,[],[f7])).
% 0.22/0.44  fof(f7,conjecture,(
% 0.22/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    spl2_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f22,f37])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ~spl2_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f23,f32])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ~r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (5476)------------------------------
% 0.22/0.44  % (5476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (5476)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (5476)Memory used [KB]: 10746
% 0.22/0.44  % (5476)Time elapsed: 0.011 s
% 0.22/0.44  % (5476)------------------------------
% 0.22/0.44  % (5476)------------------------------
% 0.22/0.44  % (5470)Success in time 0.08 s
%------------------------------------------------------------------------------
