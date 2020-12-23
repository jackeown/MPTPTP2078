%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 280 expanded)
%              Number of leaves         :   32 ( 132 expanded)
%              Depth                    :    9
%              Number of atoms          :  474 ( 869 expanded)
%              Number of equality atoms :   43 ( 120 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f693,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f77,f78,f87,f93,f99,f113,f121,f165,f212,f218,f244,f250,f258,f333,f334,f341,f361,f414,f417,f450,f540,f692])).

% (22936)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f692,plain,
    ( ~ spl3_11
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f691,f408,f90,f54,f96,f68,f118])).

fof(f118,plain,
    ( spl3_11
  <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f68,plain,
    ( spl3_4
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f96,plain,
    ( spl3_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f54,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f90,plain,
    ( spl3_7
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

% (22916)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f408,plain,
    ( spl3_46
  <=> ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ v2_compts_1(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f691,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_46 ),
    inference(forward_demodulation,[],[f686,f92])).

fof(f92,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f686,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_46 ),
    inference(resolution,[],[f409,f56])).

fof(f56,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f409,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f408])).

fof(f540,plain,
    ( ~ spl3_11
    | ~ spl3_26
    | ~ spl3_47
    | ~ spl3_25
    | ~ spl3_40
    | ~ spl3_50 ),
    inference(avatar_split_clause,[],[f539,f447,f359,f247,f411,f255,f118])).

fof(f255,plain,
    ( spl3_26
  <=> v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f411,plain,
    ( spl3_47
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f247,plain,
    ( spl3_25
  <=> sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f359,plain,
    ( spl3_40
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ v2_compts_1(sK2(X0,sK1),X0)
        | ~ r1_tarski(sK1,k2_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f447,plain,
    ( spl3_50
  <=> sK1 = sK2(k1_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f539,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_25
    | ~ spl3_40
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f537,f249])).

fof(f249,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f247])).

fof(f537,plain,
    ( ~ v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ r1_tarski(sK1,k2_struct_0(k1_pre_topc(sK0,sK1)))
    | ~ spl3_40
    | ~ spl3_50 ),
    inference(superposition,[],[f360,f449])).

fof(f449,plain,
    ( sK1 = sK2(k1_pre_topc(sK0,sK1),sK1)
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f447])).

fof(f360,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(sK2(X0,sK1),X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r1_tarski(sK1,k2_struct_0(X0)) )
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f359])).

fof(f450,plain,
    ( spl3_50
    | ~ spl3_47
    | ~ spl3_11
    | ~ spl3_25
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f445,f339,f247,f118,f411,f447])).

fof(f339,plain,
    ( spl3_38
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | sK1 = sK2(X0,sK1)
        | ~ r1_tarski(sK1,k2_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f445,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK2(k1_pre_topc(sK0,sK1),sK1)
    | ~ spl3_11
    | ~ spl3_25
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f442,f249])).

fof(f442,plain,
    ( sK1 = sK2(k1_pre_topc(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,k2_struct_0(k1_pre_topc(sK0,sK1)))
    | ~ spl3_11
    | ~ spl3_38 ),
    inference(resolution,[],[f340,f119])).

fof(f119,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f340,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | sK1 = sK2(X0,sK1)
        | ~ r1_tarski(sK1,k2_struct_0(X0)) )
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f339])).

fof(f417,plain,(
    spl3_47 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | spl3_47 ),
    inference(unit_resulting_resolution,[],[f81,f413,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

% (22933)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f413,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl3_47 ),
    inference(avatar_component_clause,[],[f411])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f38,f37])).

fof(f37,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f414,plain,
    ( spl3_46
    | ~ spl3_47
    | ~ spl3_37
    | ~ spl3_24
    | ~ spl3_25
    | spl3_26 ),
    inference(avatar_split_clause,[],[f406,f255,f247,f241,f326,f411,f408])).

fof(f326,plain,
    ( spl3_37
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f241,plain,
    ( spl3_24
  <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f406,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
        | ~ r1_tarski(sK1,sK1)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_compts_1(sK1,X0) )
    | ~ spl3_24
    | ~ spl3_25
    | spl3_26 ),
    inference(forward_demodulation,[],[f405,f243])).

fof(f243,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f241])).

% (22916)Refutation not found, incomplete strategy% (22916)------------------------------
% (22916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f405,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,sK1)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
        | ~ l1_pre_topc(X0)
        | ~ v2_compts_1(sK1,X0) )
    | ~ spl3_25
    | spl3_26 ),
    inference(forward_demodulation,[],[f404,f249])).

% (22916)Termination reason: Refutation not found, incomplete strategy

% (22916)Memory used [KB]: 6140
% (22916)Time elapsed: 0.104 s
% (22916)------------------------------
% (22916)------------------------------
fof(f404,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r1_tarski(sK1,k2_struct_0(k1_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
        | ~ l1_pre_topc(X0)
        | ~ v2_compts_1(sK1,X0) )
    | spl3_26 ),
    inference(resolution,[],[f52,f257])).

fof(f257,plain,
    ( ~ v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f255])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X3,k2_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_compts_1(X3,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X2 != X3
      | v2_compts_1(X3,X1)
      | ~ v2_compts_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,k2_struct_0(X1))
               => ( v2_compts_1(X2,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => v2_compts_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

fof(f361,plain,
    ( ~ spl3_1
    | spl3_40
    | ~ spl3_8
    | spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f357,f90,f68,f96,f359,f54])).

fof(f357,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_pre_topc(X0,sK0)
        | ~ r1_tarski(sK1,k2_struct_0(X0))
        | ~ v2_compts_1(sK2(X0,sK1),X0)
        | ~ l1_pre_topc(sK0) )
    | spl3_4
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f355,f92])).

fof(f355,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,k2_struct_0(X0))
        | ~ v2_compts_1(sK2(X0,sK1),X0)
        | ~ l1_pre_topc(sK0) )
    | spl3_4 ),
    inference(resolution,[],[f70,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ v2_compts_1(sK2(X1,X2),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f341,plain,
    ( ~ spl3_1
    | spl3_38
    | ~ spl3_8
    | spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f337,f90,f68,f96,f339,f54])).

fof(f337,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_pre_topc(X0,sK0)
        | ~ r1_tarski(sK1,k2_struct_0(X0))
        | sK1 = sK2(X0,sK1)
        | ~ l1_pre_topc(sK0) )
    | spl3_4
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f336,f92])).

fof(f336,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,k2_struct_0(X0))
        | sK1 = sK2(X0,sK1)
        | ~ l1_pre_topc(sK0) )
    | spl3_4 ),
    inference(resolution,[],[f70,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | sK2(X1,X2) = X2
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f334,plain,
    ( ~ spl3_5
    | ~ spl3_9
    | spl3_26
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f259,f247,f255,f106,f72])).

fof(f72,plain,
    ( spl3_5
  <=> v1_compts_1(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f106,plain,
    ( spl3_9
  <=> l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f259,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ spl3_25 ),
    inference(superposition,[],[f42,f249])).

fof(f42,plain,(
    ! [X0] :
      ( v2_compts_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).

fof(f333,plain,(
    spl3_37 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | spl3_37 ),
    inference(unit_resulting_resolution,[],[f81,f328])).

fof(f328,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | spl3_37 ),
    inference(avatar_component_clause,[],[f326])).

fof(f258,plain,
    ( ~ spl3_26
    | spl3_10
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f253,f247,f110,f255])).

fof(f110,plain,
    ( spl3_10
  <=> v2_compts_1(k2_struct_0(k1_pre_topc(sK0,sK1)),k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f253,plain,
    ( ~ v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | spl3_10
    | ~ spl3_25 ),
    inference(backward_demodulation,[],[f112,f249])).

fof(f112,plain,
    ( ~ v2_compts_1(k2_struct_0(k1_pre_topc(sK0,sK1)),k1_pre_topc(sK0,sK1))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f250,plain,
    ( spl3_25
    | ~ spl3_21
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f245,f241,f215,f247])).

fof(f215,plain,
    ( spl3_21
  <=> k2_struct_0(k1_pre_topc(sK0,sK1)) = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f245,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_21
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f217,f243])).

fof(f217,plain,
    ( k2_struct_0(k1_pre_topc(sK0,sK1)) = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f215])).

% (22923)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f244,plain,
    ( spl3_24
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f234,f96,f90,f54,f241])).

fof(f234,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(resolution,[],[f225,f98])).

fof(f98,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 )
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f222,f92])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 )
    | ~ spl3_1 ),
    inference(resolution,[],[f49,f56])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f218,plain,
    ( spl3_21
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f213,f209,f215])).

fof(f209,plain,
    ( spl3_20
  <=> l1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f213,plain,
    ( k2_struct_0(k1_pre_topc(sK0,sK1)) = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_20 ),
    inference(resolution,[],[f211,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f211,plain,
    ( l1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f209])).

fof(f212,plain,
    ( spl3_20
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f206,f106,f209])).

fof(f206,plain,
    ( l1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_9 ),
    inference(resolution,[],[f107,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f107,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f165,plain,
    ( ~ spl3_1
    | ~ spl3_8
    | ~ spl3_7
    | spl3_11 ),
    inference(avatar_split_clause,[],[f164,f118,f90,f96,f54])).

fof(f164,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_7
    | spl3_11 ),
    inference(forward_demodulation,[],[f149,f92])).

fof(f149,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_11 ),
    inference(resolution,[],[f50,f120])).

fof(f120,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

% (22912)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f121,plain,
    ( ~ spl3_11
    | ~ spl3_1
    | spl3_9 ),
    inference(avatar_split_clause,[],[f115,f106,f54,f118])).

fof(f115,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_1
    | spl3_9 ),
    inference(resolution,[],[f114,f56])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0) )
    | spl3_9 ),
    inference(resolution,[],[f108,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f108,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f113,plain,
    ( ~ spl3_9
    | ~ spl3_10
    | spl3_5 ),
    inference(avatar_split_clause,[],[f104,f72,f110,f106])).

fof(f104,plain,
    ( ~ v2_compts_1(k2_struct_0(k1_pre_topc(sK0,sK1)),k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl3_5 ),
    inference(resolution,[],[f41,f74])).

fof(f74,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f41,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_compts_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f99,plain,
    ( spl3_8
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f94,f90,f59,f96])).

fof(f59,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f94,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f61,f92])).

fof(f61,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f93,plain,
    ( spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f88,f84,f90])).

fof(f84,plain,
    ( spl3_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f88,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f39,f86])).

fof(f86,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f87,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f82,f54,f84])).

fof(f82,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f40,f56])).

fof(f78,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f31,f72,f68])).

fof(f31,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <~> v1_compts_1(k1_pre_topc(X0,X1)) )
              & k1_xboole_0 != X1 )
            | ( ( v2_compts_1(X1,X0)
              <~> v1_compts_1(k1_pre_topc(X0,X1)) )
              & k1_xboole_0 = X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                | k1_xboole_0 = X1 )
              & ( k1_xboole_0 = X1
               => ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v2_pre_topc(X0)
               => ( ( v2_compts_1(X1,X0)
                  <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                  | k1_xboole_0 = X1 ) )
              & ( k1_xboole_0 = X1
               => ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_pre_topc(X0)
             => ( ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                | k1_xboole_0 = X1 ) )
            & ( k1_xboole_0 = X1
             => ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_compts_1)).

fof(f77,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f32,f72,f68])).

fof(f32,plain,
    ( v1_compts_1(k1_pre_topc(sK0,sK1))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f35,f59])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f36,f54])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:56:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (22918)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.48  % (22926)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.49  % (22914)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (22915)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (22911)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (22919)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (22926)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f693,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f57,f62,f77,f78,f87,f93,f99,f113,f121,f165,f212,f218,f244,f250,f258,f333,f334,f341,f361,f414,f417,f450,f540,f692])).
% 0.21/0.51  % (22936)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  fof(f692,plain,(
% 0.21/0.51    ~spl3_11 | ~spl3_4 | ~spl3_8 | ~spl3_1 | ~spl3_7 | ~spl3_46),
% 0.21/0.51    inference(avatar_split_clause,[],[f691,f408,f90,f54,f96,f68,f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    spl3_11 <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl3_4 <=> v2_compts_1(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl3_8 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    spl3_1 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl3_7 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.51  % (22916)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  fof(f408,plain,(
% 0.21/0.51    spl3_46 <=> ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~v2_compts_1(sK1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.21/0.51  fof(f691,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_compts_1(sK1,sK0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | (~spl3_1 | ~spl3_7 | ~spl3_46)),
% 0.21/0.51    inference(forward_demodulation,[],[f686,f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f90])).
% 0.21/0.51  fof(f686,plain,(
% 0.21/0.51    ~v2_compts_1(sK1,sK0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_46)),
% 0.21/0.51    inference(resolution,[],[f409,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f54])).
% 0.21/0.51  fof(f409,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_compts_1(sK1,X0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl3_46),
% 0.21/0.51    inference(avatar_component_clause,[],[f408])).
% 0.21/0.51  fof(f540,plain,(
% 0.21/0.51    ~spl3_11 | ~spl3_26 | ~spl3_47 | ~spl3_25 | ~spl3_40 | ~spl3_50),
% 0.21/0.51    inference(avatar_split_clause,[],[f539,f447,f359,f247,f411,f255,f118])).
% 0.21/0.51  fof(f255,plain,(
% 0.21/0.51    spl3_26 <=> v2_compts_1(sK1,k1_pre_topc(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.51  fof(f411,plain,(
% 0.21/0.51    spl3_47 <=> r1_tarski(sK1,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    spl3_25 <=> sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.51  fof(f359,plain,(
% 0.21/0.51    spl3_40 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | ~v2_compts_1(sK2(X0,sK1),X0) | ~r1_tarski(sK1,k2_struct_0(X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.51  fof(f447,plain,(
% 0.21/0.51    spl3_50 <=> sK1 = sK2(k1_pre_topc(sK0,sK1),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.21/0.51  fof(f539,plain,(
% 0.21/0.51    ~r1_tarski(sK1,sK1) | ~v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | (~spl3_25 | ~spl3_40 | ~spl3_50)),
% 0.21/0.51    inference(forward_demodulation,[],[f537,f249])).
% 0.21/0.51  fof(f249,plain,(
% 0.21/0.51    sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f247])).
% 0.21/0.51  fof(f537,plain,(
% 0.21/0.51    ~v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~r1_tarski(sK1,k2_struct_0(k1_pre_topc(sK0,sK1))) | (~spl3_40 | ~spl3_50)),
% 0.21/0.51    inference(superposition,[],[f360,f449])).
% 0.21/0.51  fof(f449,plain,(
% 0.21/0.51    sK1 = sK2(k1_pre_topc(sK0,sK1),sK1) | ~spl3_50),
% 0.21/0.51    inference(avatar_component_clause,[],[f447])).
% 0.21/0.51  fof(f360,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_compts_1(sK2(X0,sK1),X0) | ~m1_pre_topc(X0,sK0) | ~r1_tarski(sK1,k2_struct_0(X0))) ) | ~spl3_40),
% 0.21/0.51    inference(avatar_component_clause,[],[f359])).
% 0.21/0.51  fof(f450,plain,(
% 0.21/0.51    spl3_50 | ~spl3_47 | ~spl3_11 | ~spl3_25 | ~spl3_38),
% 0.21/0.51    inference(avatar_split_clause,[],[f445,f339,f247,f118,f411,f447])).
% 0.21/0.51  fof(f339,plain,(
% 0.21/0.51    spl3_38 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | sK1 = sK2(X0,sK1) | ~r1_tarski(sK1,k2_struct_0(X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.51  fof(f445,plain,(
% 0.21/0.51    ~r1_tarski(sK1,sK1) | sK1 = sK2(k1_pre_topc(sK0,sK1),sK1) | (~spl3_11 | ~spl3_25 | ~spl3_38)),
% 0.21/0.51    inference(forward_demodulation,[],[f442,f249])).
% 0.21/0.51  fof(f442,plain,(
% 0.21/0.51    sK1 = sK2(k1_pre_topc(sK0,sK1),sK1) | ~r1_tarski(sK1,k2_struct_0(k1_pre_topc(sK0,sK1))) | (~spl3_11 | ~spl3_38)),
% 0.21/0.51    inference(resolution,[],[f340,f119])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~spl3_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f118])).
% 0.21/0.51  fof(f340,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK0) | sK1 = sK2(X0,sK1) | ~r1_tarski(sK1,k2_struct_0(X0))) ) | ~spl3_38),
% 0.21/0.51    inference(avatar_component_clause,[],[f339])).
% 0.21/0.51  fof(f417,plain,(
% 0.21/0.51    spl3_47),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f415])).
% 0.21/0.51  fof(f415,plain,(
% 0.21/0.51    $false | spl3_47),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f81,f413,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  % (22933)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.51    inference(unused_predicate_definition_removal,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f413,plain,(
% 0.21/0.51    ~r1_tarski(sK1,sK1) | spl3_47),
% 0.21/0.51    inference(avatar_component_clause,[],[f411])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f38,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.51  fof(f414,plain,(
% 0.21/0.51    spl3_46 | ~spl3_47 | ~spl3_37 | ~spl3_24 | ~spl3_25 | spl3_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f406,f255,f247,f241,f326,f411,f408])).
% 0.21/0.51  fof(f326,plain,(
% 0.21/0.51    spl3_37 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.51  fof(f241,plain,(
% 0.21/0.51    spl3_24 <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.51  fof(f406,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~r1_tarski(sK1,sK1) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_compts_1(sK1,X0)) ) | (~spl3_24 | ~spl3_25 | spl3_26)),
% 0.21/0.51    inference(forward_demodulation,[],[f405,f243])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f241])).
% 0.21/0.51  % (22916)Refutation not found, incomplete strategy% (22916)------------------------------
% 0.21/0.51  % (22916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  fof(f405,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(sK1,sK1) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~l1_pre_topc(X0) | ~v2_compts_1(sK1,X0)) ) | (~spl3_25 | spl3_26)),
% 0.21/0.51    inference(forward_demodulation,[],[f404,f249])).
% 0.21/0.51  % (22916)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22916)Memory used [KB]: 6140
% 0.21/0.51  % (22916)Time elapsed: 0.104 s
% 0.21/0.51  % (22916)------------------------------
% 0.21/0.51  % (22916)------------------------------
% 0.21/0.51  fof(f404,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(sK1,k2_struct_0(k1_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~l1_pre_topc(X0) | ~v2_compts_1(sK1,X0)) ) | spl3_26),
% 0.21/0.51    inference(resolution,[],[f52,f257])).
% 0.21/0.51  fof(f257,plain,(
% 0.21/0.51    ~v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | spl3_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f255])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (v2_compts_1(X3,X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X3,k2_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_compts_1(X3,X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | X2 != X3 | v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).
% 0.21/0.51  fof(f361,plain,(
% 0.21/0.51    ~spl3_1 | spl3_40 | ~spl3_8 | spl3_4 | ~spl3_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f357,f90,f68,f96,f359,f54])).
% 0.21/0.51  fof(f357,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_pre_topc(X0,sK0) | ~r1_tarski(sK1,k2_struct_0(X0)) | ~v2_compts_1(sK2(X0,sK1),X0) | ~l1_pre_topc(sK0)) ) | (spl3_4 | ~spl3_7)),
% 0.21/0.51    inference(forward_demodulation,[],[f355,f92])).
% 0.21/0.51  fof(f355,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,k2_struct_0(X0)) | ~v2_compts_1(sK2(X0,sK1),X0) | ~l1_pre_topc(sK0)) ) | spl3_4),
% 0.21/0.51    inference(resolution,[],[f70,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~v2_compts_1(sK2(X1,X2),X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ~v2_compts_1(sK1,sK0) | spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f68])).
% 0.21/0.51  fof(f341,plain,(
% 0.21/0.51    ~spl3_1 | spl3_38 | ~spl3_8 | spl3_4 | ~spl3_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f337,f90,f68,f96,f339,f54])).
% 0.21/0.51  fof(f337,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_pre_topc(X0,sK0) | ~r1_tarski(sK1,k2_struct_0(X0)) | sK1 = sK2(X0,sK1) | ~l1_pre_topc(sK0)) ) | (spl3_4 | ~spl3_7)),
% 0.21/0.51    inference(forward_demodulation,[],[f336,f92])).
% 0.21/0.51  fof(f336,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,k2_struct_0(X0)) | sK1 = sK2(X0,sK1) | ~l1_pre_topc(sK0)) ) | spl3_4),
% 0.21/0.51    inference(resolution,[],[f70,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | sK2(X1,X2) = X2 | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f334,plain,(
% 0.21/0.51    ~spl3_5 | ~spl3_9 | spl3_26 | ~spl3_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f259,f247,f255,f106,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl3_5 <=> v1_compts_1(k1_pre_topc(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    spl3_9 <=> l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~v1_compts_1(k1_pre_topc(sK0,sK1)) | ~spl3_25),
% 0.21/0.52    inference(superposition,[],[f42,f249])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0] : (v2_compts_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v1_compts_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : ((v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).
% 0.21/0.52  fof(f333,plain,(
% 0.21/0.52    spl3_37),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f330])).
% 0.21/0.52  fof(f330,plain,(
% 0.21/0.52    $false | spl3_37),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f81,f328])).
% 0.21/0.52  fof(f328,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | spl3_37),
% 0.21/0.52    inference(avatar_component_clause,[],[f326])).
% 0.21/0.52  fof(f258,plain,(
% 0.21/0.52    ~spl3_26 | spl3_10 | ~spl3_25),
% 0.21/0.52    inference(avatar_split_clause,[],[f253,f247,f110,f255])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    spl3_10 <=> v2_compts_1(k2_struct_0(k1_pre_topc(sK0,sK1)),k1_pre_topc(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.52  fof(f253,plain,(
% 0.21/0.52    ~v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | (spl3_10 | ~spl3_25)),
% 0.21/0.52    inference(backward_demodulation,[],[f112,f249])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ~v2_compts_1(k2_struct_0(k1_pre_topc(sK0,sK1)),k1_pre_topc(sK0,sK1)) | spl3_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f110])).
% 0.21/0.52  fof(f250,plain,(
% 0.21/0.52    spl3_25 | ~spl3_21 | ~spl3_24),
% 0.21/0.52    inference(avatar_split_clause,[],[f245,f241,f215,f247])).
% 0.21/0.52  fof(f215,plain,(
% 0.21/0.52    spl3_21 <=> k2_struct_0(k1_pre_topc(sK0,sK1)) = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) | (~spl3_21 | ~spl3_24)),
% 0.21/0.52    inference(backward_demodulation,[],[f217,f243])).
% 0.21/0.52  fof(f217,plain,(
% 0.21/0.52    k2_struct_0(k1_pre_topc(sK0,sK1)) = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f215])).
% 0.21/0.52  % (22923)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    spl3_24 | ~spl3_1 | ~spl3_7 | ~spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f234,f96,f90,f54,f241])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | (~spl3_1 | ~spl3_7 | ~spl3_8)),
% 0.21/0.52    inference(resolution,[],[f225,f98])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | u1_struct_0(k1_pre_topc(sK0,X0)) = X0) ) | (~spl3_1 | ~spl3_7)),
% 0.21/0.52    inference(forward_demodulation,[],[f222,f92])).
% 0.21/0.52  fof(f222,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(k1_pre_topc(sK0,X0)) = X0) ) | ~spl3_1),
% 0.21/0.52    inference(resolution,[],[f49,f56])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    spl3_21 | ~spl3_20),
% 0.21/0.52    inference(avatar_split_clause,[],[f213,f209,f215])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    spl3_20 <=> l1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.52  fof(f213,plain,(
% 0.21/0.52    k2_struct_0(k1_pre_topc(sK0,sK1)) = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_20),
% 0.21/0.52    inference(resolution,[],[f211,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.52  fof(f211,plain,(
% 0.21/0.52    l1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f209])).
% 0.21/0.52  fof(f212,plain,(
% 0.21/0.52    spl3_20 | ~spl3_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f206,f106,f209])).
% 0.21/0.52  fof(f206,plain,(
% 0.21/0.52    l1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_9),
% 0.21/0.52    inference(resolution,[],[f107,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~spl3_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f106])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ~spl3_1 | ~spl3_8 | ~spl3_7 | spl3_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f164,f118,f90,f96,f54])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_7 | spl3_11)),
% 0.21/0.52    inference(forward_demodulation,[],[f149,f92])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_11),
% 0.21/0.52    inference(resolution,[],[f50,f120])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | spl3_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f118])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  % (22912)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    ~spl3_11 | ~spl3_1 | spl3_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f115,f106,f54,f118])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | (~spl3_1 | spl3_9)),
% 0.21/0.52    inference(resolution,[],[f114,f56])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0)) ) | spl3_9),
% 0.21/0.52    inference(resolution,[],[f108,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | spl3_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f106])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ~spl3_9 | ~spl3_10 | spl3_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f104,f72,f110,f106])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ~v2_compts_1(k2_struct_0(k1_pre_topc(sK0,sK1)),k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | spl3_5),
% 0.21/0.52    inference(resolution,[],[f41,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | spl3_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f72])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0] : (v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl3_8 | ~spl3_2 | ~spl3_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f94,f90,f59,f96])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_2 | ~spl3_7)),
% 0.21/0.52    inference(backward_demodulation,[],[f61,f92])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f59])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    spl3_7 | ~spl3_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f88,f84,f90])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    spl3_6 <=> l1_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_6),
% 0.21/0.52    inference(resolution,[],[f39,f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    l1_struct_0(sK0) | ~spl3_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f84])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    spl3_6 | ~spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f82,f54,f84])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    l1_struct_0(sK0) | ~spl3_1),
% 0.21/0.52    inference(resolution,[],[f40,f56])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ~spl3_4 | ~spl3_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f31,f72,f68])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | ~v2_compts_1(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 != X1) | ((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_compts_1)).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl3_4 | spl3_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f32,f72,f68])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    v1_compts_1(k1_pre_topc(sK0,sK1)) | v2_compts_1(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f35,f59])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f36,f54])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (22926)------------------------------
% 0.21/0.52  % (22926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22926)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (22926)Memory used [KB]: 6524
% 0.21/0.52  % (22926)Time elapsed: 0.105 s
% 0.21/0.52  % (22926)------------------------------
% 0.21/0.52  % (22926)------------------------------
% 0.21/0.52  % (22910)Success in time 0.16 s
%------------------------------------------------------------------------------
