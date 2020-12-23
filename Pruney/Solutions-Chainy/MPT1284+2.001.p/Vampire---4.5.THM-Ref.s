%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 480 expanded)
%              Number of leaves         :   41 ( 220 expanded)
%              Depth                    :   15
%              Number of atoms          :  691 (2520 expanded)
%              Number of equality atoms :   33 (  98 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f594,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f104,f109,f114,f123,f124,f125,f147,f163,f178,f183,f188,f198,f213,f281,f328,f333,f367,f372,f521,f547,f548,f578,f593])).

fof(f593,plain,
    ( ~ spl4_3
    | ~ spl4_5
    | ~ spl4_13
    | ~ spl4_16
    | ~ spl4_24
    | ~ spl4_25
    | spl4_26
    | ~ spl4_35 ),
    inference(avatar_contradiction_clause,[],[f592])).

fof(f592,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_13
    | ~ spl4_16
    | ~ spl4_24
    | ~ spl4_25
    | spl4_26
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f591,f371])).

fof(f371,plain,
    ( sK3 != k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f369])).

fof(f369,plain,
    ( spl4_26
  <=> sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f591,plain,
    ( sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_13
    | ~ spl4_16
    | ~ spl4_24
    | ~ spl4_25
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f586,f582])).

fof(f582,plain,
    ( r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_13
    | ~ spl4_16
    | ~ spl4_24
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f580,f551])).

fof(f551,plain,
    ( sK3 = k2_pre_topc(sK1,sK3)
    | ~ spl4_13
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f170,f332])).

fof(f332,plain,
    ( r1_tarski(k2_pre_topc(sK1,sK3),sK3)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl4_24
  <=> r1_tarski(k2_pre_topc(sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f170,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,sK3),sK3)
    | sK3 = k2_pre_topc(sK1,sK3)
    | ~ spl4_13 ),
    inference(resolution,[],[f162,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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

fof(f162,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl4_13
  <=> r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f580,plain,
    ( r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k2_pre_topc(sK1,sK3))
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_16
    | ~ spl4_35 ),
    inference(unit_resulting_resolution,[],[f84,f94,f182,f577,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f577,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),sK3)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f575])).

fof(f575,plain,
    ( spl4_35
  <=> r1_tarski(k1_tops_1(sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f182,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl4_16
  <=> m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f94,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f84,plain,
    ( l1_pre_topc(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_3
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f586,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3)
    | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | ~ spl4_25 ),
    inference(resolution,[],[f366,f68])).

fof(f366,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f364])).

fof(f364,plain,
    ( spl4_25
  <=> r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f578,plain,
    ( spl4_35
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f562,f330,f160,f106,f92,f82,f575])).

fof(f106,plain,
    ( spl4_8
  <=> v4_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

% (10530)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f562,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),sK3)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f559,f551])).

fof(f559,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f84,f94,f108,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v4_tops_1(X1,X0)
      | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

fof(f108,plain,
    ( v4_tops_1(sK3,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f548,plain,
    ( sK2 != k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f547,plain,
    ( spl4_34
    | ~ spl4_2
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f199,f175,f77,f544])).

fof(f544,plain,
    ( spl4_34
  <=> r1_tarski(k1_tops_1(sK0,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f77,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f175,plain,
    ( spl4_15
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f199,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ spl4_2
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f79,f177,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f177,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f175])).

fof(f79,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f521,plain,
    ( ~ spl4_29
    | ~ spl4_2
    | spl4_11
    | ~ spl4_12
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f386,f325,f278,f195,f185,f144,f120,f77,f518])).

fof(f518,plain,
    ( spl4_29
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f120,plain,
    ( spl4_11
  <=> v4_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f144,plain,
    ( spl4_12
  <=> r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f185,plain,
    ( spl4_17
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f195,plain,
    ( spl4_19
  <=> sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f278,plain,
    ( spl4_20
  <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f325,plain,
    ( spl4_23
  <=> r1_tarski(k2_pre_topc(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f386,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl4_2
    | spl4_11
    | ~ spl4_12
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f385,f122])).

fof(f122,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f120])).

fof(f385,plain,
    ( v4_tops_1(sK2,sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f384,f334])).

fof(f334,plain,
    ( sK2 = k2_pre_topc(sK0,sK2)
    | ~ spl4_12
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f169,f327])).

fof(f327,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),sK2)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f325])).

fof(f169,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK2),sK2)
    | sK2 = k2_pre_topc(sK0,sK2)
    | ~ spl4_12 ),
    inference(resolution,[],[f146,f68])).

fof(f146,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f144])).

fof(f384,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | v4_tops_1(k2_pre_topc(sK0,sK2),sK0)
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f383,f69])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f383,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | v4_tops_1(k2_pre_topc(sK0,sK2),sK0)
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f382,f197])).

fof(f197,plain,
    ( sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f195])).

fof(f382,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | v4_tops_1(k2_pre_topc(sK0,sK2),sK0)
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_17
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f381,f334])).

fof(f381,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))))
    | v4_tops_1(k2_pre_topc(sK0,sK2),sK0)
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_17
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f380,f334])).

fof(f380,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2))
    | ~ r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))))
    | v4_tops_1(k2_pre_topc(sK0,sK2),sK0)
    | ~ spl4_2
    | ~ spl4_17
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f379,f79])).

fof(f379,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2))
    | ~ r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))))
    | v4_tops_1(k2_pre_topc(sK0,sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_17
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f374,f187])).

fof(f187,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f185])).

fof(f374,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2))
    | ~ r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))))
    | v4_tops_1(k2_pre_topc(sK0,sK2),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_20 ),
    inference(superposition,[],[f59,f280])).

fof(f280,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f278])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f372,plain,
    ( ~ spl4_26
    | ~ spl4_3
    | ~ spl4_5
    | spl4_9 ),
    inference(avatar_split_clause,[],[f323,f111,f92,f82,f369])).

fof(f111,plain,
    ( spl4_9
  <=> v5_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f323,plain,
    ( sK3 != k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | ~ spl4_3
    | ~ spl4_5
    | spl4_9 ),
    inference(unit_resulting_resolution,[],[f84,f94,f113,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(f113,plain,
    ( ~ v5_tops_1(sK3,sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f367,plain,
    ( spl4_25
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f315,f106,f92,f82,f364])).

fof(f315,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f84,f94,f108,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v4_tops_1(X1,X0)
      | r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f333,plain,
    ( spl4_24
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f309,f97,f92,f82,f330])).

fof(f97,plain,
    ( spl4_6
  <=> v4_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f309,plain,
    ( r1_tarski(k2_pre_topc(sK1,sK3),sK3)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f84,f69,f94,f94,f99,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_pre_topc(X0,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

fof(f99,plain,
    ( v4_pre_topc(sK3,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f328,plain,
    ( spl4_23
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f214,f116,f87,f77,f325])).

fof(f87,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f116,plain,
    ( spl4_10
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f214,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),sK2)
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f79,f69,f89,f89,f117,f61])).

fof(f117,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f89,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f87])).

% (10525)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f281,plain,
    ( spl4_20
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f137,f87,f77,f278])).

fof(f137,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f79,f89,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f213,plain,
    ( spl4_10
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_15
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f209,f195,f175,f77,f72,f116])).

fof(f72,plain,
    ( spl4_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

% (10529)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f209,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_15
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f203,f197])).

fof(f203,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f74,f79,f177,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f74,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f198,plain,
    ( spl4_19
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f141,f101,f87,f77,f195])).

fof(f101,plain,
    ( spl4_7
  <=> v5_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f141,plain,
    ( sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f79,f103,f89,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v5_tops_1(X1,X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f103,plain,
    ( v5_tops_1(sK2,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f188,plain,
    ( spl4_17
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f135,f87,f77,f185])).

fof(f135,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f79,f89,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f183,plain,
    ( spl4_16
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f134,f92,f82,f180])).

fof(f134,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f84,f94,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f178,plain,
    ( spl4_15
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f133,f87,f77,f175])).

fof(f133,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f79,f89,f63])).

fof(f163,plain,
    ( spl4_13
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f129,f92,f82,f160])).

fof(f129,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f84,f94,f53])).

fof(f147,plain,
    ( spl4_12
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f128,f87,f77,f144])).

fof(f128,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f79,f89,f53])).

fof(f125,plain,
    ( ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f52,f120,f116,f111])).

fof(f52,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v5_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ( ( ~ v4_tops_1(sK2,sK0)
          | ~ v4_pre_topc(sK2,sK0) )
        & v5_tops_1(sK2,sK0) )
      | ( ~ v5_tops_1(sK3,sK1)
        & v4_tops_1(sK3,sK1)
        & v4_pre_topc(sK3,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f35,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ v4_tops_1(X2,X0)
                          | ~ v4_pre_topc(X2,X0) )
                        & v5_tops_1(X2,X0) )
                      | ( ~ v5_tops_1(X3,X1)
                        & v4_tops_1(X3,X1)
                        & v4_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,sK0)
                        | ~ v4_pre_topc(X2,sK0) )
                      & v5_tops_1(X2,sK0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ v4_tops_1(X2,sK0)
                      | ~ v4_pre_topc(X2,sK0) )
                    & v5_tops_1(X2,sK0) )
                  | ( ~ v5_tops_1(X3,X1)
                    & v4_tops_1(X3,X1)
                    & v4_pre_topc(X3,X1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,sK0)
                    | ~ v4_pre_topc(X2,sK0) )
                  & v5_tops_1(X2,sK0) )
                | ( ~ v5_tops_1(X3,sK1)
                  & v4_tops_1(X3,sK1)
                  & v4_pre_topc(X3,sK1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(X2,sK0)
                  | ~ v4_pre_topc(X2,sK0) )
                & v5_tops_1(X2,sK0) )
              | ( ~ v5_tops_1(X3,sK1)
                & v4_tops_1(X3,sK1)
                & v4_pre_topc(X3,sK1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ( ( ~ v4_tops_1(sK2,sK0)
                | ~ v4_pre_topc(sK2,sK0) )
              & v5_tops_1(sK2,sK0) )
            | ( ~ v5_tops_1(X3,sK1)
              & v4_tops_1(X3,sK1)
              & v4_pre_topc(X3,sK1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X3] :
        ( ( ( ( ~ v4_tops_1(sK2,sK0)
              | ~ v4_pre_topc(sK2,sK0) )
            & v5_tops_1(sK2,sK0) )
          | ( ~ v5_tops_1(X3,sK1)
            & v4_tops_1(X3,sK1)
            & v4_pre_topc(X3,sK1) ) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ( ( ~ v4_tops_1(sK2,sK0)
            | ~ v4_pre_topc(sK2,sK0) )
          & v5_tops_1(sK2,sK0) )
        | ( ~ v5_tops_1(sK3,sK1)
          & v4_tops_1(sK3,sK1)
          & v4_pre_topc(sK3,sK1) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v5_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v4_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v4_pre_topc(X3,X1) )
                       => v5_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v5_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v4_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v4_pre_topc(X3,X1) )
                     => v5_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tops_1)).

fof(f124,plain,
    ( spl4_8
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f51,f120,f116,f106])).

fof(f51,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f123,plain,
    ( spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f50,f120,f116,f97])).

fof(f50,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f114,plain,
    ( ~ spl4_9
    | spl4_7 ),
    inference(avatar_split_clause,[],[f49,f101,f111])).

fof(f49,plain,
    ( v5_tops_1(sK2,sK0)
    | ~ v5_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f109,plain,
    ( spl4_8
    | spl4_7 ),
    inference(avatar_split_clause,[],[f48,f101,f106])).

fof(f48,plain,
    ( v5_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f104,plain,
    ( spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f47,f101,f97])).

fof(f47,plain,
    ( v5_tops_1(sK2,sK0)
    | v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f46,f92])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f45,f87])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f44,f82])).

fof(f44,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f43,f77])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f42,f72])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (10536)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (10526)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.49  % (10545)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (10535)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (10524)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (10547)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.51  % (10540)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (10534)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (10527)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (10522)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (10528)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (10532)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (10545)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (10537)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f594,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f104,f109,f114,f123,f124,f125,f147,f163,f178,f183,f188,f198,f213,f281,f328,f333,f367,f372,f521,f547,f548,f578,f593])).
% 0.22/0.52  fof(f593,plain,(
% 0.22/0.52    ~spl4_3 | ~spl4_5 | ~spl4_13 | ~spl4_16 | ~spl4_24 | ~spl4_25 | spl4_26 | ~spl4_35),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f592])).
% 0.22/0.52  fof(f592,plain,(
% 0.22/0.52    $false | (~spl4_3 | ~spl4_5 | ~spl4_13 | ~spl4_16 | ~spl4_24 | ~spl4_25 | spl4_26 | ~spl4_35)),
% 0.22/0.52    inference(subsumption_resolution,[],[f591,f371])).
% 0.22/0.52  fof(f371,plain,(
% 0.22/0.52    sK3 != k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | spl4_26),
% 0.22/0.52    inference(avatar_component_clause,[],[f369])).
% 0.22/0.52  fof(f369,plain,(
% 0.22/0.52    spl4_26 <=> sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.22/0.52  fof(f591,plain,(
% 0.22/0.52    sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | (~spl4_3 | ~spl4_5 | ~spl4_13 | ~spl4_16 | ~spl4_24 | ~spl4_25 | ~spl4_35)),
% 0.22/0.52    inference(subsumption_resolution,[],[f586,f582])).
% 0.22/0.52  fof(f582,plain,(
% 0.22/0.52    r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3) | (~spl4_3 | ~spl4_5 | ~spl4_13 | ~spl4_16 | ~spl4_24 | ~spl4_35)),
% 0.22/0.52    inference(forward_demodulation,[],[f580,f551])).
% 0.22/0.52  fof(f551,plain,(
% 0.22/0.52    sK3 = k2_pre_topc(sK1,sK3) | (~spl4_13 | ~spl4_24)),
% 0.22/0.52    inference(subsumption_resolution,[],[f170,f332])).
% 0.22/0.52  fof(f332,plain,(
% 0.22/0.52    r1_tarski(k2_pre_topc(sK1,sK3),sK3) | ~spl4_24),
% 0.22/0.52    inference(avatar_component_clause,[],[f330])).
% 0.22/0.52  fof(f330,plain,(
% 0.22/0.52    spl4_24 <=> r1_tarski(k2_pre_topc(sK1,sK3),sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    ~r1_tarski(k2_pre_topc(sK1,sK3),sK3) | sK3 = k2_pre_topc(sK1,sK3) | ~spl4_13),
% 0.22/0.52    inference(resolution,[],[f162,f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | ~spl4_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f160])).
% 0.22/0.52  fof(f160,plain,(
% 0.22/0.52    spl4_13 <=> r1_tarski(sK3,k2_pre_topc(sK1,sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.52  fof(f580,plain,(
% 0.22/0.52    r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k2_pre_topc(sK1,sK3)) | (~spl4_3 | ~spl4_5 | ~spl4_16 | ~spl4_35)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f84,f94,f182,f577,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).
% 0.22/0.52  fof(f577,plain,(
% 0.22/0.52    r1_tarski(k1_tops_1(sK1,sK3),sK3) | ~spl4_35),
% 0.22/0.52    inference(avatar_component_clause,[],[f575])).
% 0.22/0.52  fof(f575,plain,(
% 0.22/0.52    spl4_35 <=> r1_tarski(k1_tops_1(sK1,sK3),sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.22/0.52  fof(f182,plain,(
% 0.22/0.52    m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl4_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f180])).
% 0.22/0.52  fof(f180,plain,(
% 0.22/0.52    spl4_16 <=> m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl4_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f92])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    spl4_5 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    l1_pre_topc(sK1) | ~spl4_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f82])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    spl4_3 <=> l1_pre_topc(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.52  fof(f586,plain,(
% 0.22/0.52    ~r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3) | sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | ~spl4_25),
% 0.22/0.52    inference(resolution,[],[f366,f68])).
% 0.22/0.52  fof(f366,plain,(
% 0.22/0.52    r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | ~spl4_25),
% 0.22/0.52    inference(avatar_component_clause,[],[f364])).
% 0.22/0.52  fof(f364,plain,(
% 0.22/0.52    spl4_25 <=> r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.52  fof(f578,plain,(
% 0.22/0.52    spl4_35 | ~spl4_3 | ~spl4_5 | ~spl4_8 | ~spl4_13 | ~spl4_24),
% 0.22/0.52    inference(avatar_split_clause,[],[f562,f330,f160,f106,f92,f82,f575])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    spl4_8 <=> v4_tops_1(sK3,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.53  % (10530)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  fof(f562,plain,(
% 0.22/0.53    r1_tarski(k1_tops_1(sK1,sK3),sK3) | (~spl4_3 | ~spl4_5 | ~spl4_8 | ~spl4_13 | ~spl4_24)),
% 0.22/0.53    inference(forward_demodulation,[],[f559,f551])).
% 0.22/0.53  fof(f559,plain,(
% 0.22/0.53    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | (~spl4_3 | ~spl4_5 | ~spl4_8)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f84,f94,f108,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v4_tops_1(X1,X0) | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    v4_tops_1(sK3,sK1) | ~spl4_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f106])).
% 0.22/0.53  fof(f548,plain,(
% 0.22/0.53    sK2 != k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~r1_tarski(k1_tops_1(sK0,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f547,plain,(
% 0.22/0.53    spl4_34 | ~spl4_2 | ~spl4_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f199,f175,f77,f544])).
% 0.22/0.53  fof(f544,plain,(
% 0.22/0.53    spl4_34 <=> r1_tarski(k1_tops_1(sK0,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl4_2 <=> l1_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    spl4_15 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.53  fof(f199,plain,(
% 0.22/0.53    r1_tarski(k1_tops_1(sK0,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | (~spl4_2 | ~spl4_15)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f79,f177,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f175])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    l1_pre_topc(sK0) | ~spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f77])).
% 0.22/0.53  fof(f521,plain,(
% 0.22/0.53    ~spl4_29 | ~spl4_2 | spl4_11 | ~spl4_12 | ~spl4_17 | ~spl4_19 | ~spl4_20 | ~spl4_23),
% 0.22/0.53    inference(avatar_split_clause,[],[f386,f325,f278,f195,f185,f144,f120,f77,f518])).
% 0.22/0.53  fof(f518,plain,(
% 0.22/0.53    spl4_29 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    spl4_11 <=> v4_tops_1(sK2,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    spl4_12 <=> r1_tarski(sK2,k2_pre_topc(sK0,sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    spl4_17 <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.53  fof(f195,plain,(
% 0.22/0.53    spl4_19 <=> sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.53  fof(f278,plain,(
% 0.22/0.53    spl4_20 <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.53  fof(f325,plain,(
% 0.22/0.53    spl4_23 <=> r1_tarski(k2_pre_topc(sK0,sK2),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.22/0.53  fof(f386,plain,(
% 0.22/0.53    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | (~spl4_2 | spl4_11 | ~spl4_12 | ~spl4_17 | ~spl4_19 | ~spl4_20 | ~spl4_23)),
% 0.22/0.53    inference(subsumption_resolution,[],[f385,f122])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    ~v4_tops_1(sK2,sK0) | spl4_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f120])).
% 0.22/0.53  fof(f385,plain,(
% 0.22/0.53    v4_tops_1(sK2,sK0) | ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | (~spl4_2 | ~spl4_12 | ~spl4_17 | ~spl4_19 | ~spl4_20 | ~spl4_23)),
% 0.22/0.53    inference(forward_demodulation,[],[f384,f334])).
% 0.22/0.53  fof(f334,plain,(
% 0.22/0.53    sK2 = k2_pre_topc(sK0,sK2) | (~spl4_12 | ~spl4_23)),
% 0.22/0.53    inference(subsumption_resolution,[],[f169,f327])).
% 0.22/0.53  fof(f327,plain,(
% 0.22/0.53    r1_tarski(k2_pre_topc(sK0,sK2),sK2) | ~spl4_23),
% 0.22/0.53    inference(avatar_component_clause,[],[f325])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    ~r1_tarski(k2_pre_topc(sK0,sK2),sK2) | sK2 = k2_pre_topc(sK0,sK2) | ~spl4_12),
% 0.22/0.53    inference(resolution,[],[f146,f68])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | ~spl4_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f144])).
% 0.22/0.53  fof(f384,plain,(
% 0.22/0.53    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | v4_tops_1(k2_pre_topc(sK0,sK2),sK0) | (~spl4_2 | ~spl4_12 | ~spl4_17 | ~spl4_19 | ~spl4_20 | ~spl4_23)),
% 0.22/0.53    inference(subsumption_resolution,[],[f383,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  fof(f383,plain,(
% 0.22/0.53    ~r1_tarski(sK2,sK2) | ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | v4_tops_1(k2_pre_topc(sK0,sK2),sK0) | (~spl4_2 | ~spl4_12 | ~spl4_17 | ~spl4_19 | ~spl4_20 | ~spl4_23)),
% 0.22/0.53    inference(forward_demodulation,[],[f382,f197])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | ~spl4_19),
% 0.22/0.53    inference(avatar_component_clause,[],[f195])).
% 0.22/0.53  fof(f382,plain,(
% 0.22/0.53    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | v4_tops_1(k2_pre_topc(sK0,sK2),sK0) | (~spl4_2 | ~spl4_12 | ~spl4_17 | ~spl4_20 | ~spl4_23)),
% 0.22/0.53    inference(forward_demodulation,[],[f381,f334])).
% 0.22/0.53  fof(f381,plain,(
% 0.22/0.53    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2)))) | v4_tops_1(k2_pre_topc(sK0,sK2),sK0) | (~spl4_2 | ~spl4_12 | ~spl4_17 | ~spl4_20 | ~spl4_23)),
% 0.22/0.53    inference(forward_demodulation,[],[f380,f334])).
% 0.22/0.53  fof(f380,plain,(
% 0.22/0.53    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2)) | ~r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2)))) | v4_tops_1(k2_pre_topc(sK0,sK2),sK0) | (~spl4_2 | ~spl4_17 | ~spl4_20)),
% 0.22/0.53    inference(subsumption_resolution,[],[f379,f79])).
% 0.22/0.53  fof(f379,plain,(
% 0.22/0.53    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2)) | ~r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2)))) | v4_tops_1(k2_pre_topc(sK0,sK2),sK0) | ~l1_pre_topc(sK0) | (~spl4_17 | ~spl4_20)),
% 0.22/0.53    inference(subsumption_resolution,[],[f374,f187])).
% 0.22/0.53  fof(f187,plain,(
% 0.22/0.53    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f185])).
% 0.22/0.53  fof(f374,plain,(
% 0.22/0.53    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2)) | ~r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2)))) | v4_tops_1(k2_pre_topc(sK0,sK2),sK0) | ~m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_20),
% 0.22/0.53    inference(superposition,[],[f59,f280])).
% 0.22/0.53  fof(f280,plain,(
% 0.22/0.53    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2)) | ~spl4_20),
% 0.22/0.53    inference(avatar_component_clause,[],[f278])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f372,plain,(
% 0.22/0.53    ~spl4_26 | ~spl4_3 | ~spl4_5 | spl4_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f323,f111,f92,f82,f369])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    spl4_9 <=> v5_tops_1(sK3,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.53  fof(f323,plain,(
% 0.22/0.53    sK3 != k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | (~spl4_3 | ~spl4_5 | spl4_9)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f84,f94,f113,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ~v5_tops_1(sK3,sK1) | spl4_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f111])).
% 0.22/0.53  fof(f367,plain,(
% 0.22/0.53    spl4_25 | ~spl4_3 | ~spl4_5 | ~spl4_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f315,f106,f92,f82,f364])).
% 0.22/0.53  fof(f315,plain,(
% 0.22/0.53    r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | (~spl4_3 | ~spl4_5 | ~spl4_8)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f84,f94,f108,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v4_tops_1(X1,X0) | r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f333,plain,(
% 0.22/0.53    spl4_24 | ~spl4_3 | ~spl4_5 | ~spl4_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f309,f97,f92,f82,f330])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    spl4_6 <=> v4_pre_topc(sK3,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.53  fof(f309,plain,(
% 0.22/0.53    r1_tarski(k2_pre_topc(sK1,sK3),sK3) | (~spl4_3 | ~spl4_5 | ~spl4_6)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f84,f69,f94,f94,f99,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v4_pre_topc(X1,X0) | ~r1_tarski(X2,X1) | r1_tarski(k2_pre_topc(X0,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X2),X1) | (~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    v4_pre_topc(sK3,sK1) | ~spl4_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f97])).
% 0.22/0.53  fof(f328,plain,(
% 0.22/0.53    spl4_23 | ~spl4_2 | ~spl4_4 | ~spl4_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f214,f116,f87,f77,f325])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    spl4_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    spl4_10 <=> v4_pre_topc(sK2,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.53  fof(f214,plain,(
% 0.22/0.53    r1_tarski(k2_pre_topc(sK0,sK2),sK2) | (~spl4_2 | ~spl4_4 | ~spl4_10)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f79,f69,f89,f89,f117,f61])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    v4_pre_topc(sK2,sK0) | ~spl4_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f116])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f87])).
% 0.22/0.53  % (10525)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  fof(f281,plain,(
% 0.22/0.53    spl4_20 | ~spl4_2 | ~spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f137,f87,f77,f278])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2)) | (~spl4_2 | ~spl4_4)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f79,f89,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).
% 0.22/0.53  fof(f213,plain,(
% 0.22/0.53    spl4_10 | ~spl4_1 | ~spl4_2 | ~spl4_15 | ~spl4_19),
% 0.22/0.53    inference(avatar_split_clause,[],[f209,f195,f175,f77,f72,f116])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    spl4_1 <=> v2_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.53  % (10529)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  fof(f209,plain,(
% 0.22/0.53    v4_pre_topc(sK2,sK0) | (~spl4_1 | ~spl4_2 | ~spl4_15 | ~spl4_19)),
% 0.22/0.53    inference(forward_demodulation,[],[f203,f197])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) | (~spl4_1 | ~spl4_2 | ~spl4_15)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f74,f79,f177,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    v2_pre_topc(sK0) | ~spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f72])).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    spl4_19 | ~spl4_2 | ~spl4_4 | ~spl4_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f141,f101,f87,f77,f195])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    spl4_7 <=> v5_tops_1(sK2,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | (~spl4_2 | ~spl4_4 | ~spl4_7)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f79,f103,f89,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    v5_tops_1(sK2,sK0) | ~spl4_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f101])).
% 0.22/0.53  fof(f188,plain,(
% 0.22/0.53    spl4_17 | ~spl4_2 | ~spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f135,f87,f77,f185])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_4)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f79,f89,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.53  fof(f183,plain,(
% 0.22/0.53    spl4_16 | ~spl4_3 | ~spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f134,f92,f82,f180])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl4_3 | ~spl4_5)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f84,f94,f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    spl4_15 | ~spl4_2 | ~spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f133,f87,f77,f175])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_4)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f79,f89,f63])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    spl4_13 | ~spl4_3 | ~spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f129,f92,f82,f160])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | (~spl4_3 | ~spl4_5)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f84,f94,f53])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    spl4_12 | ~spl4_2 | ~spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f128,f87,f77,f144])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | (~spl4_2 | ~spl4_4)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f79,f89,f53])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    ~spl4_9 | ~spl4_10 | ~spl4_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f52,f120,f116,f111])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0) | ~v5_tops_1(sK3,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ((((((~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0)) & v5_tops_1(sK2,sK0)) | (~v5_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v4_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f35,f34,f33,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v4_pre_topc(X2,sK0)) & v5_tops_1(X2,sK0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v4_pre_topc(X2,sK0)) & v5_tops_1(X2,sK0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v4_pre_topc(X2,sK0)) & v5_tops_1(X2,sK0)) | (~v5_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v4_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v4_pre_topc(X2,sK0)) & v5_tops_1(X2,sK0)) | (~v5_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v4_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((((~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0)) & v5_tops_1(sK2,sK0)) | (~v5_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v4_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ? [X3] : ((((~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0)) & v5_tops_1(sK2,sK0)) | (~v5_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v4_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => ((((~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0)) & v5_tops_1(sK2,sK0)) | (~v5_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v4_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f12])).
% 0.22/0.53  fof(f12,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tops_1)).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    spl4_8 | ~spl4_10 | ~spl4_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f51,f120,f116,f106])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    spl4_6 | ~spl4_10 | ~spl4_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f50,f120,f116,f97])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0) | v4_pre_topc(sK3,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    ~spl4_9 | spl4_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f49,f101,f111])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    v5_tops_1(sK2,sK0) | ~v5_tops_1(sK3,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    spl4_8 | spl4_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f48,f101,f106])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    v5_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    spl4_6 | spl4_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f47,f101,f97])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    v5_tops_1(sK2,sK0) | v4_pre_topc(sK3,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f46,f92])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f45,f87])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    spl4_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f44,f82])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    l1_pre_topc(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f43,f77])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    spl4_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f42,f72])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    v2_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (10545)------------------------------
% 0.22/0.53  % (10545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10545)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (10545)Memory used [KB]: 11001
% 0.22/0.53  % (10545)Time elapsed: 0.101 s
% 0.22/0.53  % (10545)------------------------------
% 0.22/0.53  % (10545)------------------------------
% 0.22/0.53  % (10543)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (10546)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.54  % (10521)Success in time 0.175 s
%------------------------------------------------------------------------------
