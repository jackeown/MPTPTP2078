%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:56 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 371 expanded)
%              Number of leaves         :   42 ( 163 expanded)
%              Depth                    :   11
%              Number of atoms          :  720 (1533 expanded)
%              Number of equality atoms :   55 (  76 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f915,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f104,f109,f114,f119,f124,f129,f176,f274,f325,f372,f385,f428,f480,f481,f490,f525,f535,f694,f709,f714,f722,f737,f838,f914])).

fof(f914,plain,
    ( spl5_45
    | ~ spl5_3
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f909,f711,f106,f706])).

fof(f706,plain,
    ( spl5_45
  <=> r2_hidden(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f106,plain,
    ( spl5_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

% (6474)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f711,plain,
    ( spl5_46
  <=> r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f909,plain,
    ( r2_hidden(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_3
    | ~ spl5_46 ),
    inference(resolution,[],[f713,f203])).

fof(f203,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | r2_hidden(X2,u1_struct_0(sK0)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f108,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f108,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f713,plain,
    ( r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1)
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f711])).

fof(f838,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | sK1 != k2_pre_topc(sK0,sK1)
    | v1_subset_1(sK1,sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f737,plain,
    ( ~ spl5_25
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f730,f425,f420])).

% (6468)Refutation not found, incomplete strategy% (6468)------------------------------
% (6468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6468)Termination reason: Refutation not found, incomplete strategy

% (6468)Memory used [KB]: 10618
% (6468)Time elapsed: 0.137 s
% (6468)------------------------------
% (6468)------------------------------
fof(f420,plain,
    ( spl5_25
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f425,plain,
    ( spl5_26
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f730,plain,
    ( ~ v1_subset_1(sK1,sK1)
    | ~ spl5_26 ),
    inference(resolution,[],[f427,f94])).

fof(f94,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f427,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f425])).

fof(f722,plain,
    ( ~ spl5_11
    | ~ spl5_15
    | spl5_17 ),
    inference(avatar_split_clause,[],[f537,f245,f232,f212])).

fof(f212,plain,
    ( spl5_11
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f232,plain,
    ( spl5_15
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f245,plain,
    ( spl5_17
  <=> u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f537,plain,
    ( u1_struct_0(sK0) != sK1
    | ~ spl5_15
    | spl5_17 ),
    inference(backward_demodulation,[],[f246,f234])).

fof(f234,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f232])).

fof(f246,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f245])).

fof(f714,plain,
    ( spl5_46
    | spl5_43 ),
    inference(avatar_split_clause,[],[f701,f691,f711])).

fof(f691,plain,
    ( spl5_43
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f701,plain,
    ( r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1)
    | spl5_43 ),
    inference(unit_resulting_resolution,[],[f693,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f56,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

% (6471)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f693,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl5_43 ),
    inference(avatar_component_clause,[],[f691])).

fof(f709,plain,
    ( ~ spl5_45
    | spl5_43 ),
    inference(avatar_split_clause,[],[f702,f691,f706])).

fof(f702,plain,
    ( ~ r2_hidden(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl5_43 ),
    inference(unit_resulting_resolution,[],[f693,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f694,plain,
    ( ~ spl5_43
    | ~ spl5_9
    | spl5_11
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f689,f323,f212,f173,f691])).

fof(f173,plain,
    ( spl5_9
  <=> v2_tex_2(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f323,plain,
    ( spl5_23
  <=> ! [X0] :
        ( sK1 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f689,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_9
    | spl5_11
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f688,f67])).

fof(f67,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f688,plain,
    ( ~ r1_tarski(sK1,k2_subset_1(u1_struct_0(sK0)))
    | ~ spl5_9
    | spl5_11
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f687,f175])).

fof(f175,plain,
    ( v2_tex_2(u1_struct_0(sK0),sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f173])).

fof(f687,plain,
    ( ~ v2_tex_2(u1_struct_0(sK0),sK0)
    | ~ r1_tarski(sK1,k2_subset_1(u1_struct_0(sK0)))
    | spl5_11
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f686,f67])).

fof(f686,plain,
    ( ~ v2_tex_2(k2_subset_1(u1_struct_0(sK0)),sK0)
    | ~ r1_tarski(sK1,k2_subset_1(u1_struct_0(sK0)))
    | spl5_11
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f685,f213])).

fof(f213,plain,
    ( u1_struct_0(sK0) != sK1
    | spl5_11 ),
    inference(avatar_component_clause,[],[f212])).

fof(f685,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ v2_tex_2(k2_subset_1(u1_struct_0(sK0)),sK0)
    | ~ r1_tarski(sK1,k2_subset_1(u1_struct_0(sK0)))
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f679,f67])).

fof(f679,plain,
    ( sK1 = k2_subset_1(u1_struct_0(sK0))
    | ~ v2_tex_2(k2_subset_1(u1_struct_0(sK0)),sK0)
    | ~ r1_tarski(sK1,k2_subset_1(u1_struct_0(sK0)))
    | ~ spl5_23 ),
    inference(resolution,[],[f324,f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f324,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X0
        | ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(sK1,X0) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f323])).

fof(f535,plain,
    ( spl5_15
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f532,f228,f111,f106,f232])).

fof(f111,plain,
    ( spl5_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f228,plain,
    ( spl5_14
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f532,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f113,f108,f229,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f229,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f228])).

fof(f113,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f525,plain,
    ( ~ spl5_10
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_24 ),
    inference(avatar_split_clause,[],[f522,f379,f121,f116,f111,f207])).

fof(f207,plain,
    ( spl5_10
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f116,plain,
    ( spl5_5
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f121,plain,
    ( spl5_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f379,plain,
    ( spl5_24
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f522,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_24 ),
    inference(unit_resulting_resolution,[],[f123,f113,f118,f381,f84])).

fof(f84,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK3(X0),X0)
            & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f51,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f50])).

% (6478)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f50,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f381,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl5_24 ),
    inference(avatar_component_clause,[],[f379])).

fof(f118,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f116])).

fof(f123,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f490,plain,
    ( ~ spl5_17
    | ~ spl5_3
    | ~ spl5_4
    | spl5_16 ),
    inference(avatar_split_clause,[],[f489,f241,f111,f106,f245])).

fof(f241,plain,
    ( spl5_16
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f489,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | ~ spl5_3
    | ~ spl5_4
    | spl5_16 ),
    inference(subsumption_resolution,[],[f488,f113])).

fof(f488,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_3
    | spl5_16 ),
    inference(subsumption_resolution,[],[f464,f243])).

fof(f243,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f241])).

fof(f464,plain,
    ( v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f108,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f481,plain,
    ( ~ spl5_24
    | ~ spl5_3
    | ~ spl5_4
    | spl5_14 ),
    inference(avatar_split_clause,[],[f457,f228,f111,f106,f379])).

fof(f457,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_3
    | ~ spl5_4
    | spl5_14 ),
    inference(unit_resulting_resolution,[],[f113,f230,f108,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f230,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f228])).

fof(f480,plain,
    ( spl5_10
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f460,f106,f207])).

fof(f460,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f108,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f428,plain,
    ( spl5_26
    | ~ spl5_3
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f397,f212,f106,f425])).

fof(f397,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl5_3
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f108,f214])).

fof(f214,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f212])).

fof(f385,plain,
    ( spl5_11
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f383,f106,f100,f212])).

fof(f100,plain,
    ( spl5_2
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f383,plain,
    ( u1_struct_0(sK0) = sK1
    | spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f108,f101,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f101,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f372,plain,
    ( ~ spl5_16
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f358,f222,f126,f121,f111,f106,f96,f241])).

fof(f96,plain,
    ( spl5_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f126,plain,
    ( spl5_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f222,plain,
    ( spl5_13
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f358,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f128,f123,f113,f224,f108,f98,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
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
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

fof(f98,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f224,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f222])).

fof(f128,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f325,plain,
    ( ~ spl5_1
    | spl5_23
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f321,f111,f106,f323,f96])).

fof(f321,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r1_tarski(sK1,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(sK1,sK0) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f192,f113])).

fof(f192,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r1_tarski(sK1,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(sK1,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f108,f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

% (6477)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

% (6482)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f274,plain,
    ( spl5_13
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f273,f126,f121,f116,f111,f106,f222])).

fof(f273,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f272,f128])).

fof(f272,plain,
    ( v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f271,f123])).

fof(f271,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f270,f118])).

fof(f270,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f200,f113])).

% (6476)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f200,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f108,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f176,plain,
    ( spl5_9
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f171,f126,f121,f116,f111,f173])).

fof(f171,plain,
    ( v2_tex_2(u1_struct_0(sK0),sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(forward_demodulation,[],[f168,f67])).

fof(f168,plain,
    ( v2_tex_2(k2_subset_1(u1_struct_0(sK0)),sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f113,f123,f118,f68,f128,f82])).

fof(f129,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f59,f126])).

fof(f59,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( v1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v3_tex_2(sK1,sK0) )
    & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK0))
            | ~ v3_tex_2(X1,sK0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ( v1_subset_1(X1,u1_struct_0(sK0))
          | ~ v3_tex_2(X1,sK0) )
        & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( v1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v3_tex_2(sK1,sK0) )
      & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f124,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f60,f121])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f119,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f61,f116])).

fof(f61,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f114,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f62,f111])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f109,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f63,f106])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f104,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f64,f100,f96])).

fof(f64,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f103,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f65,f100,f96])).

fof(f65,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (6467)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (6483)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (6467)Refutation not found, incomplete strategy% (6467)------------------------------
% 0.21/0.51  % (6467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6467)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (6467)Memory used [KB]: 10618
% 0.21/0.51  % (6467)Time elapsed: 0.102 s
% 0.21/0.51  % (6467)------------------------------
% 0.21/0.51  % (6467)------------------------------
% 0.21/0.52  % (6475)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.25/0.52  % (6475)Refutation not found, incomplete strategy% (6475)------------------------------
% 1.25/0.52  % (6475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (6475)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (6475)Memory used [KB]: 10618
% 1.25/0.52  % (6475)Time elapsed: 0.115 s
% 1.25/0.52  % (6475)------------------------------
% 1.25/0.52  % (6475)------------------------------
% 1.25/0.52  % (6484)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.25/0.52  % (6458)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.25/0.52  % (6460)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.52  % (6458)Refutation not found, incomplete strategy% (6458)------------------------------
% 1.25/0.52  % (6458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (6473)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.25/0.52  % (6458)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (6458)Memory used [KB]: 1663
% 1.25/0.52  % (6458)Time elapsed: 0.084 s
% 1.25/0.52  % (6458)------------------------------
% 1.25/0.52  % (6458)------------------------------
% 1.25/0.53  % (6462)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.25/0.53  % (6465)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.25/0.53  % (6459)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.25/0.53  % (6461)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.25/0.54  % (6480)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.54  % (6472)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.25/0.54  % (6481)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.25/0.54  % (6463)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.25/0.54  % (6483)Refutation found. Thanks to Tanya!
% 1.25/0.54  % SZS status Theorem for theBenchmark
% 1.25/0.54  % (6468)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.25/0.54  % SZS output start Proof for theBenchmark
% 1.25/0.54  fof(f915,plain,(
% 1.25/0.54    $false),
% 1.25/0.54    inference(avatar_sat_refutation,[],[f103,f104,f109,f114,f119,f124,f129,f176,f274,f325,f372,f385,f428,f480,f481,f490,f525,f535,f694,f709,f714,f722,f737,f838,f914])).
% 1.25/0.54  fof(f914,plain,(
% 1.25/0.54    spl5_45 | ~spl5_3 | ~spl5_46),
% 1.25/0.54    inference(avatar_split_clause,[],[f909,f711,f106,f706])).
% 1.25/0.54  fof(f706,plain,(
% 1.25/0.54    spl5_45 <=> r2_hidden(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 1.25/0.54  fof(f106,plain,(
% 1.25/0.54    spl5_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.25/0.54  % (6474)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.25/0.54  fof(f711,plain,(
% 1.25/0.54    spl5_46 <=> r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 1.25/0.54  fof(f909,plain,(
% 1.25/0.54    r2_hidden(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | (~spl5_3 | ~spl5_46)),
% 1.25/0.54    inference(resolution,[],[f713,f203])).
% 1.25/0.54  fof(f203,plain,(
% 1.25/0.54    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(X2,u1_struct_0(sK0))) ) | ~spl5_3),
% 1.25/0.54    inference(resolution,[],[f108,f90])).
% 1.25/0.54  fof(f90,plain,(
% 1.25/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.25/0.54    inference(cnf_transformation,[],[f36])).
% 1.25/0.54  fof(f36,plain,(
% 1.25/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.25/0.54    inference(ennf_transformation,[],[f5])).
% 1.25/0.54  fof(f5,axiom,(
% 1.25/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.25/0.54  fof(f108,plain,(
% 1.25/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_3),
% 1.25/0.54    inference(avatar_component_clause,[],[f106])).
% 1.25/0.54  fof(f713,plain,(
% 1.25/0.54    r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1) | ~spl5_46),
% 1.25/0.54    inference(avatar_component_clause,[],[f711])).
% 1.25/0.54  fof(f838,plain,(
% 1.25/0.54    u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) | sK1 != k2_pre_topc(sK0,sK1) | v1_subset_1(sK1,sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.25/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.25/0.54  fof(f737,plain,(
% 1.25/0.54    ~spl5_25 | ~spl5_26),
% 1.25/0.54    inference(avatar_split_clause,[],[f730,f425,f420])).
% 1.25/0.54  % (6468)Refutation not found, incomplete strategy% (6468)------------------------------
% 1.25/0.54  % (6468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (6468)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (6468)Memory used [KB]: 10618
% 1.25/0.54  % (6468)Time elapsed: 0.137 s
% 1.25/0.54  % (6468)------------------------------
% 1.25/0.54  % (6468)------------------------------
% 1.25/0.54  fof(f420,plain,(
% 1.25/0.54    spl5_25 <=> v1_subset_1(sK1,sK1)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.25/0.54  fof(f425,plain,(
% 1.25/0.54    spl5_26 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.25/0.54  fof(f730,plain,(
% 1.25/0.54    ~v1_subset_1(sK1,sK1) | ~spl5_26),
% 1.25/0.54    inference(resolution,[],[f427,f94])).
% 1.25/0.54  fof(f94,plain,(
% 1.25/0.54    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 1.25/0.54    inference(equality_resolution,[],[f88])).
% 1.25/0.54  fof(f88,plain,(
% 1.25/0.54    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.25/0.54    inference(cnf_transformation,[],[f54])).
% 1.25/0.54  fof(f54,plain,(
% 1.25/0.54    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.25/0.54    inference(nnf_transformation,[],[f35])).
% 1.25/0.54  fof(f35,plain,(
% 1.25/0.54    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.25/0.54    inference(ennf_transformation,[],[f11])).
% 1.25/0.54  fof(f11,axiom,(
% 1.25/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 1.25/0.54  fof(f427,plain,(
% 1.25/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl5_26),
% 1.25/0.54    inference(avatar_component_clause,[],[f425])).
% 1.25/0.54  fof(f722,plain,(
% 1.25/0.54    ~spl5_11 | ~spl5_15 | spl5_17),
% 1.25/0.54    inference(avatar_split_clause,[],[f537,f245,f232,f212])).
% 1.25/0.54  fof(f212,plain,(
% 1.25/0.54    spl5_11 <=> u1_struct_0(sK0) = sK1),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.25/0.54  fof(f232,plain,(
% 1.25/0.54    spl5_15 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.25/0.54  fof(f245,plain,(
% 1.25/0.54    spl5_17 <=> u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.25/0.54  fof(f537,plain,(
% 1.25/0.54    u1_struct_0(sK0) != sK1 | (~spl5_15 | spl5_17)),
% 1.25/0.54    inference(backward_demodulation,[],[f246,f234])).
% 1.25/0.54  fof(f234,plain,(
% 1.25/0.54    sK1 = k2_pre_topc(sK0,sK1) | ~spl5_15),
% 1.25/0.54    inference(avatar_component_clause,[],[f232])).
% 1.25/0.54  fof(f246,plain,(
% 1.25/0.54    u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) | spl5_17),
% 1.25/0.54    inference(avatar_component_clause,[],[f245])).
% 1.25/0.54  fof(f714,plain,(
% 1.25/0.54    spl5_46 | spl5_43),
% 1.25/0.54    inference(avatar_split_clause,[],[f701,f691,f711])).
% 1.25/0.54  fof(f691,plain,(
% 1.25/0.54    spl5_43 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 1.25/0.54  fof(f701,plain,(
% 1.25/0.54    r2_hidden(sK4(sK1,u1_struct_0(sK0)),sK1) | spl5_43),
% 1.25/0.54    inference(unit_resulting_resolution,[],[f693,f92])).
% 1.25/0.54  fof(f92,plain,(
% 1.25/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f58])).
% 1.25/0.54  fof(f58,plain,(
% 1.25/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.25/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f56,f57])).
% 1.25/0.54  fof(f57,plain,(
% 1.25/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  % (6471)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.25/0.54  fof(f56,plain,(
% 1.25/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.25/0.54    inference(rectify,[],[f55])).
% 1.25/0.54  fof(f55,plain,(
% 1.25/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.25/0.54    inference(nnf_transformation,[],[f37])).
% 1.25/0.54  fof(f37,plain,(
% 1.25/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.25/0.54    inference(ennf_transformation,[],[f1])).
% 1.25/0.54  fof(f1,axiom,(
% 1.25/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.25/0.54  fof(f693,plain,(
% 1.25/0.54    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl5_43),
% 1.25/0.54    inference(avatar_component_clause,[],[f691])).
% 1.25/0.54  fof(f709,plain,(
% 1.25/0.54    ~spl5_45 | spl5_43),
% 1.25/0.54    inference(avatar_split_clause,[],[f702,f691,f706])).
% 1.25/0.54  fof(f702,plain,(
% 1.25/0.54    ~r2_hidden(sK4(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | spl5_43),
% 1.25/0.54    inference(unit_resulting_resolution,[],[f693,f93])).
% 1.25/0.54  fof(f93,plain,(
% 1.25/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f58])).
% 1.25/0.54  fof(f694,plain,(
% 1.25/0.54    ~spl5_43 | ~spl5_9 | spl5_11 | ~spl5_23),
% 1.25/0.54    inference(avatar_split_clause,[],[f689,f323,f212,f173,f691])).
% 1.25/0.54  fof(f173,plain,(
% 1.25/0.54    spl5_9 <=> v2_tex_2(u1_struct_0(sK0),sK0)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.25/0.54  fof(f323,plain,(
% 1.25/0.54    spl5_23 <=> ! [X0] : (sK1 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~r1_tarski(sK1,X0))),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.25/0.54  fof(f689,plain,(
% 1.25/0.54    ~r1_tarski(sK1,u1_struct_0(sK0)) | (~spl5_9 | spl5_11 | ~spl5_23)),
% 1.25/0.54    inference(forward_demodulation,[],[f688,f67])).
% 1.25/0.54  fof(f67,plain,(
% 1.25/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.25/0.54    inference(cnf_transformation,[],[f2])).
% 1.25/0.54  fof(f2,axiom,(
% 1.25/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.25/0.54  fof(f688,plain,(
% 1.25/0.54    ~r1_tarski(sK1,k2_subset_1(u1_struct_0(sK0))) | (~spl5_9 | spl5_11 | ~spl5_23)),
% 1.25/0.54    inference(subsumption_resolution,[],[f687,f175])).
% 1.25/0.54  fof(f175,plain,(
% 1.25/0.54    v2_tex_2(u1_struct_0(sK0),sK0) | ~spl5_9),
% 1.25/0.54    inference(avatar_component_clause,[],[f173])).
% 1.25/0.54  fof(f687,plain,(
% 1.25/0.54    ~v2_tex_2(u1_struct_0(sK0),sK0) | ~r1_tarski(sK1,k2_subset_1(u1_struct_0(sK0))) | (spl5_11 | ~spl5_23)),
% 1.25/0.54    inference(forward_demodulation,[],[f686,f67])).
% 1.25/0.54  fof(f686,plain,(
% 1.25/0.54    ~v2_tex_2(k2_subset_1(u1_struct_0(sK0)),sK0) | ~r1_tarski(sK1,k2_subset_1(u1_struct_0(sK0))) | (spl5_11 | ~spl5_23)),
% 1.25/0.54    inference(subsumption_resolution,[],[f685,f213])).
% 1.25/0.54  fof(f213,plain,(
% 1.25/0.54    u1_struct_0(sK0) != sK1 | spl5_11),
% 1.25/0.54    inference(avatar_component_clause,[],[f212])).
% 1.25/0.54  fof(f685,plain,(
% 1.25/0.54    u1_struct_0(sK0) = sK1 | ~v2_tex_2(k2_subset_1(u1_struct_0(sK0)),sK0) | ~r1_tarski(sK1,k2_subset_1(u1_struct_0(sK0))) | ~spl5_23),
% 1.25/0.54    inference(forward_demodulation,[],[f679,f67])).
% 1.25/0.54  fof(f679,plain,(
% 1.25/0.54    sK1 = k2_subset_1(u1_struct_0(sK0)) | ~v2_tex_2(k2_subset_1(u1_struct_0(sK0)),sK0) | ~r1_tarski(sK1,k2_subset_1(u1_struct_0(sK0))) | ~spl5_23),
% 1.25/0.54    inference(resolution,[],[f324,f68])).
% 1.25/0.54  fof(f68,plain,(
% 1.25/0.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.25/0.54    inference(cnf_transformation,[],[f3])).
% 1.25/0.54  fof(f3,axiom,(
% 1.25/0.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.25/0.54  fof(f324,plain,(
% 1.25/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0 | ~v2_tex_2(X0,sK0) | ~r1_tarski(sK1,X0)) ) | ~spl5_23),
% 1.25/0.54    inference(avatar_component_clause,[],[f323])).
% 1.25/0.54  fof(f535,plain,(
% 1.25/0.54    spl5_15 | ~spl5_3 | ~spl5_4 | ~spl5_14),
% 1.25/0.54    inference(avatar_split_clause,[],[f532,f228,f111,f106,f232])).
% 1.25/0.54  fof(f111,plain,(
% 1.25/0.54    spl5_4 <=> l1_pre_topc(sK0)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.25/0.54  fof(f228,plain,(
% 1.25/0.54    spl5_14 <=> v4_pre_topc(sK1,sK0)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.25/0.54  fof(f532,plain,(
% 1.25/0.54    sK1 = k2_pre_topc(sK0,sK1) | (~spl5_3 | ~spl5_4 | ~spl5_14)),
% 1.25/0.54    inference(unit_resulting_resolution,[],[f113,f108,f229,f70])).
% 1.25/0.54  fof(f70,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f23])).
% 1.25/0.54  fof(f23,plain,(
% 1.25/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.25/0.54    inference(flattening,[],[f22])).
% 1.25/0.54  fof(f22,plain,(
% 1.25/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.25/0.54    inference(ennf_transformation,[],[f7])).
% 1.25/0.54  fof(f7,axiom,(
% 1.25/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.25/0.54  fof(f229,plain,(
% 1.25/0.54    v4_pre_topc(sK1,sK0) | ~spl5_14),
% 1.25/0.54    inference(avatar_component_clause,[],[f228])).
% 1.25/0.54  fof(f113,plain,(
% 1.25/0.54    l1_pre_topc(sK0) | ~spl5_4),
% 1.25/0.54    inference(avatar_component_clause,[],[f111])).
% 1.25/0.54  fof(f525,plain,(
% 1.25/0.54    ~spl5_10 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_24),
% 1.25/0.54    inference(avatar_split_clause,[],[f522,f379,f121,f116,f111,f207])).
% 1.25/0.54  fof(f207,plain,(
% 1.25/0.54    spl5_10 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.25/0.54  fof(f116,plain,(
% 1.25/0.54    spl5_5 <=> v1_tdlat_3(sK0)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.25/0.54  fof(f121,plain,(
% 1.25/0.54    spl5_6 <=> v2_pre_topc(sK0)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.25/0.54  fof(f379,plain,(
% 1.25/0.54    spl5_24 <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.25/0.54  fof(f522,plain,(
% 1.25/0.54    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_24)),
% 1.25/0.54    inference(unit_resulting_resolution,[],[f123,f113,f118,f381,f84])).
% 1.25/0.54  fof(f84,plain,(
% 1.25/0.54    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f53])).
% 1.25/0.54  fof(f53,plain,(
% 1.25/0.54    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.25/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f51,f52])).
% 1.25/0.54  fof(f52,plain,(
% 1.25/0.54    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f51,plain,(
% 1.25/0.54    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.25/0.54    inference(rectify,[],[f50])).
% 1.25/0.54  % (6478)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.25/0.54  fof(f50,plain,(
% 1.25/0.54    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.25/0.54    inference(nnf_transformation,[],[f33])).
% 1.25/0.54  fof(f33,plain,(
% 1.25/0.54    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.25/0.54    inference(flattening,[],[f32])).
% 1.25/0.54  fof(f32,plain,(
% 1.25/0.54    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.25/0.54    inference(ennf_transformation,[],[f13])).
% 1.25/0.54  fof(f13,axiom,(
% 1.25/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).
% 1.25/0.54  fof(f381,plain,(
% 1.25/0.54    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | spl5_24),
% 1.25/0.54    inference(avatar_component_clause,[],[f379])).
% 1.25/0.54  fof(f118,plain,(
% 1.25/0.54    v1_tdlat_3(sK0) | ~spl5_5),
% 1.25/0.54    inference(avatar_component_clause,[],[f116])).
% 1.25/0.54  fof(f123,plain,(
% 1.25/0.54    v2_pre_topc(sK0) | ~spl5_6),
% 1.25/0.54    inference(avatar_component_clause,[],[f121])).
% 1.25/0.54  fof(f490,plain,(
% 1.25/0.54    ~spl5_17 | ~spl5_3 | ~spl5_4 | spl5_16),
% 1.25/0.54    inference(avatar_split_clause,[],[f489,f241,f111,f106,f245])).
% 1.25/0.54  fof(f241,plain,(
% 1.25/0.54    spl5_16 <=> v1_tops_1(sK1,sK0)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.25/0.54  fof(f489,plain,(
% 1.25/0.54    u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) | (~spl5_3 | ~spl5_4 | spl5_16)),
% 1.25/0.54    inference(subsumption_resolution,[],[f488,f113])).
% 1.25/0.54  fof(f488,plain,(
% 1.25/0.54    u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl5_3 | spl5_16)),
% 1.25/0.54    inference(subsumption_resolution,[],[f464,f243])).
% 1.25/0.54  fof(f243,plain,(
% 1.25/0.54    ~v1_tops_1(sK1,sK0) | spl5_16),
% 1.25/0.54    inference(avatar_component_clause,[],[f241])).
% 1.25/0.54  fof(f464,plain,(
% 1.25/0.54    v1_tops_1(sK1,sK0) | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | ~spl5_3),
% 1.25/0.54    inference(resolution,[],[f108,f73])).
% 1.25/0.54  fof(f73,plain,(
% 1.25/0.54    ( ! [X0,X1] : (v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f43])).
% 1.25/0.54  fof(f43,plain,(
% 1.25/0.54    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.25/0.54    inference(nnf_transformation,[],[f24])).
% 1.25/0.54  fof(f24,plain,(
% 1.25/0.54    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.25/0.54    inference(ennf_transformation,[],[f10])).
% 1.25/0.54  fof(f10,axiom,(
% 1.25/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 1.25/0.54  fof(f481,plain,(
% 1.25/0.54    ~spl5_24 | ~spl5_3 | ~spl5_4 | spl5_14),
% 1.25/0.54    inference(avatar_split_clause,[],[f457,f228,f111,f106,f379])).
% 1.25/0.54  fof(f457,plain,(
% 1.25/0.54    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (~spl5_3 | ~spl5_4 | spl5_14)),
% 1.25/0.54    inference(unit_resulting_resolution,[],[f113,f230,f108,f81])).
% 1.25/0.54  fof(f81,plain,(
% 1.25/0.54    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f49])).
% 1.25/0.54  fof(f49,plain,(
% 1.25/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.25/0.54    inference(nnf_transformation,[],[f27])).
% 1.25/0.54  fof(f27,plain,(
% 1.25/0.54    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.25/0.54    inference(ennf_transformation,[],[f8])).
% 1.25/0.54  fof(f8,axiom,(
% 1.25/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 1.25/0.54  fof(f230,plain,(
% 1.25/0.54    ~v4_pre_topc(sK1,sK0) | spl5_14),
% 1.25/0.54    inference(avatar_component_clause,[],[f228])).
% 1.25/0.54  fof(f480,plain,(
% 1.25/0.54    spl5_10 | ~spl5_3),
% 1.25/0.54    inference(avatar_split_clause,[],[f460,f106,f207])).
% 1.25/0.54  fof(f460,plain,(
% 1.25/0.54    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_3),
% 1.25/0.54    inference(unit_resulting_resolution,[],[f108,f87])).
% 1.25/0.54  fof(f87,plain,(
% 1.25/0.54    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.25/0.54    inference(cnf_transformation,[],[f34])).
% 1.25/0.54  fof(f34,plain,(
% 1.25/0.54    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.25/0.54    inference(ennf_transformation,[],[f4])).
% 1.25/0.54  fof(f4,axiom,(
% 1.25/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.25/0.54  fof(f428,plain,(
% 1.25/0.54    spl5_26 | ~spl5_3 | ~spl5_11),
% 1.25/0.54    inference(avatar_split_clause,[],[f397,f212,f106,f425])).
% 1.25/0.54  fof(f397,plain,(
% 1.25/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl5_3 | ~spl5_11)),
% 1.25/0.54    inference(backward_demodulation,[],[f108,f214])).
% 1.25/0.54  fof(f214,plain,(
% 1.25/0.54    u1_struct_0(sK0) = sK1 | ~spl5_11),
% 1.25/0.54    inference(avatar_component_clause,[],[f212])).
% 1.25/0.54  fof(f385,plain,(
% 1.25/0.54    spl5_11 | spl5_2 | ~spl5_3),
% 1.25/0.54    inference(avatar_split_clause,[],[f383,f106,f100,f212])).
% 1.25/0.54  fof(f100,plain,(
% 1.25/0.54    spl5_2 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.25/0.54  fof(f383,plain,(
% 1.25/0.54    u1_struct_0(sK0) = sK1 | (spl5_2 | ~spl5_3)),
% 1.25/0.54    inference(unit_resulting_resolution,[],[f108,f101,f89])).
% 1.25/0.54  fof(f89,plain,(
% 1.25/0.54    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.25/0.54    inference(cnf_transformation,[],[f54])).
% 1.25/0.54  fof(f101,plain,(
% 1.25/0.54    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl5_2),
% 1.25/0.54    inference(avatar_component_clause,[],[f100])).
% 1.25/0.54  fof(f372,plain,(
% 1.25/0.54    ~spl5_16 | spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_6 | spl5_7 | ~spl5_13),
% 1.25/0.54    inference(avatar_split_clause,[],[f358,f222,f126,f121,f111,f106,f96,f241])).
% 1.25/0.54  fof(f96,plain,(
% 1.25/0.54    spl5_1 <=> v3_tex_2(sK1,sK0)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.25/0.54  fof(f126,plain,(
% 1.25/0.54    spl5_7 <=> v2_struct_0(sK0)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.25/0.54  fof(f222,plain,(
% 1.25/0.54    spl5_13 <=> v2_tex_2(sK1,sK0)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.25/0.54  fof(f358,plain,(
% 1.25/0.54    ~v1_tops_1(sK1,sK0) | (spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_6 | spl5_7 | ~spl5_13)),
% 1.25/0.54    inference(unit_resulting_resolution,[],[f128,f123,f113,f224,f108,f98,f83])).
% 1.25/0.54  fof(f83,plain,(
% 1.25/0.54    ( ! [X0,X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f31])).
% 1.25/0.54  fof(f31,plain,(
% 1.25/0.54    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.25/0.54    inference(flattening,[],[f30])).
% 1.25/0.54  fof(f30,plain,(
% 1.25/0.54    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.25/0.54    inference(ennf_transformation,[],[f15])).
% 1.25/0.54  fof(f15,axiom,(
% 1.25/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).
% 1.25/0.54  fof(f98,plain,(
% 1.25/0.54    ~v3_tex_2(sK1,sK0) | spl5_1),
% 1.25/0.54    inference(avatar_component_clause,[],[f96])).
% 1.25/0.54  fof(f224,plain,(
% 1.25/0.54    v2_tex_2(sK1,sK0) | ~spl5_13),
% 1.25/0.54    inference(avatar_component_clause,[],[f222])).
% 1.49/0.54  fof(f128,plain,(
% 1.49/0.54    ~v2_struct_0(sK0) | spl5_7),
% 1.49/0.54    inference(avatar_component_clause,[],[f126])).
% 1.49/0.54  fof(f325,plain,(
% 1.49/0.54    ~spl5_1 | spl5_23 | ~spl5_3 | ~spl5_4),
% 1.49/0.54    inference(avatar_split_clause,[],[f321,f111,f106,f323,f96])).
% 1.49/0.54  fof(f321,plain,(
% 1.49/0.54    ( ! [X0] : (sK1 = X0 | ~r1_tarski(sK1,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(sK1,sK0)) ) | (~spl5_3 | ~spl5_4)),
% 1.49/0.54    inference(subsumption_resolution,[],[f192,f113])).
% 1.49/0.54  fof(f192,plain,(
% 1.49/0.54    ( ! [X0] : (sK1 = X0 | ~r1_tarski(sK1,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)) ) | ~spl5_3),
% 1.49/0.54    inference(resolution,[],[f108,f75])).
% 1.49/0.54  fof(f75,plain,(
% 1.49/0.54    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.54    inference(cnf_transformation,[],[f48])).
% 1.49/0.54  fof(f48,plain,(
% 1.49/0.54    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).
% 1.49/0.54  fof(f47,plain,(
% 1.49/0.54    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.49/0.54    introduced(choice_axiom,[])).
% 1.49/0.54  % (6477)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.49/0.54  fof(f46,plain,(
% 1.49/0.54    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.54    inference(rectify,[],[f45])).
% 1.49/0.54  fof(f45,plain,(
% 1.49/0.54    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.54    inference(flattening,[],[f44])).
% 1.49/0.54  fof(f44,plain,(
% 1.49/0.54    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.54    inference(nnf_transformation,[],[f26])).
% 1.49/0.54  fof(f26,plain,(
% 1.49/0.54    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.54    inference(flattening,[],[f25])).
% 1.49/0.54  fof(f25,plain,(
% 1.49/0.54    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.54    inference(ennf_transformation,[],[f12])).
% 1.49/0.54  fof(f12,axiom,(
% 1.49/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.49/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 1.49/0.54  % (6482)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.49/0.54  fof(f274,plain,(
% 1.49/0.54    spl5_13 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7),
% 1.49/0.54    inference(avatar_split_clause,[],[f273,f126,f121,f116,f111,f106,f222])).
% 1.49/0.54  fof(f273,plain,(
% 1.49/0.54    v2_tex_2(sK1,sK0) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7)),
% 1.49/0.54    inference(subsumption_resolution,[],[f272,f128])).
% 1.49/0.54  fof(f272,plain,(
% 1.49/0.54    v2_tex_2(sK1,sK0) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 1.49/0.54    inference(subsumption_resolution,[],[f271,f123])).
% 1.49/0.54  fof(f271,plain,(
% 1.49/0.54    v2_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.49/0.54    inference(subsumption_resolution,[],[f270,f118])).
% 1.49/0.54  fof(f270,plain,(
% 1.49/0.54    v2_tex_2(sK1,sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4)),
% 1.49/0.54    inference(subsumption_resolution,[],[f200,f113])).
% 1.49/0.54  % (6476)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.49/0.54  fof(f200,plain,(
% 1.49/0.54    v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_3),
% 1.49/0.54    inference(resolution,[],[f108,f82])).
% 1.49/0.54  fof(f82,plain,(
% 1.49/0.54    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.54    inference(cnf_transformation,[],[f29])).
% 1.49/0.54  fof(f29,plain,(
% 1.49/0.54    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.54    inference(flattening,[],[f28])).
% 1.49/0.54  fof(f28,plain,(
% 1.49/0.54    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.54    inference(ennf_transformation,[],[f14])).
% 1.49/0.54  fof(f14,axiom,(
% 1.49/0.54    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 1.49/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 1.49/0.54  fof(f176,plain,(
% 1.49/0.54    spl5_9 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7),
% 1.49/0.54    inference(avatar_split_clause,[],[f171,f126,f121,f116,f111,f173])).
% 1.49/0.54  fof(f171,plain,(
% 1.49/0.54    v2_tex_2(u1_struct_0(sK0),sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7)),
% 1.49/0.54    inference(forward_demodulation,[],[f168,f67])).
% 1.49/0.54  fof(f168,plain,(
% 1.49/0.54    v2_tex_2(k2_subset_1(u1_struct_0(sK0)),sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_7)),
% 1.49/0.54    inference(unit_resulting_resolution,[],[f113,f123,f118,f68,f128,f82])).
% 1.49/0.54  fof(f129,plain,(
% 1.49/0.54    ~spl5_7),
% 1.49/0.54    inference(avatar_split_clause,[],[f59,f126])).
% 1.49/0.54  fof(f59,plain,(
% 1.49/0.54    ~v2_struct_0(sK0)),
% 1.49/0.54    inference(cnf_transformation,[],[f42])).
% 1.49/0.54  fof(f42,plain,(
% 1.49/0.54    ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.49/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).
% 1.49/0.54  fof(f40,plain,(
% 1.49/0.54    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.49/0.54    introduced(choice_axiom,[])).
% 1.49/0.54  fof(f41,plain,(
% 1.49/0.54    ? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.49/0.54    introduced(choice_axiom,[])).
% 1.49/0.54  fof(f39,plain,(
% 1.49/0.54    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.49/0.54    inference(flattening,[],[f38])).
% 1.49/0.54  fof(f38,plain,(
% 1.49/0.54    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.49/0.54    inference(nnf_transformation,[],[f19])).
% 1.49/0.54  fof(f19,plain,(
% 1.49/0.54    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.49/0.54    inference(flattening,[],[f18])).
% 1.49/0.54  fof(f18,plain,(
% 1.49/0.54    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.49/0.54    inference(ennf_transformation,[],[f17])).
% 1.49/0.54  fof(f17,negated_conjecture,(
% 1.49/0.54    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.49/0.54    inference(negated_conjecture,[],[f16])).
% 1.49/0.54  fof(f16,conjecture,(
% 1.49/0.54    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.49/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).
% 1.49/0.54  fof(f124,plain,(
% 1.49/0.54    spl5_6),
% 1.49/0.54    inference(avatar_split_clause,[],[f60,f121])).
% 1.49/0.54  fof(f60,plain,(
% 1.49/0.54    v2_pre_topc(sK0)),
% 1.49/0.54    inference(cnf_transformation,[],[f42])).
% 1.49/0.54  fof(f119,plain,(
% 1.49/0.54    spl5_5),
% 1.49/0.54    inference(avatar_split_clause,[],[f61,f116])).
% 1.49/0.54  fof(f61,plain,(
% 1.49/0.54    v1_tdlat_3(sK0)),
% 1.49/0.54    inference(cnf_transformation,[],[f42])).
% 1.49/0.54  fof(f114,plain,(
% 1.49/0.54    spl5_4),
% 1.49/0.54    inference(avatar_split_clause,[],[f62,f111])).
% 1.49/0.54  fof(f62,plain,(
% 1.49/0.54    l1_pre_topc(sK0)),
% 1.49/0.54    inference(cnf_transformation,[],[f42])).
% 1.49/0.54  fof(f109,plain,(
% 1.49/0.54    spl5_3),
% 1.49/0.54    inference(avatar_split_clause,[],[f63,f106])).
% 1.49/0.54  fof(f63,plain,(
% 1.49/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.54    inference(cnf_transformation,[],[f42])).
% 1.49/0.54  fof(f104,plain,(
% 1.49/0.54    spl5_1 | ~spl5_2),
% 1.49/0.54    inference(avatar_split_clause,[],[f64,f100,f96])).
% 1.49/0.54  fof(f64,plain,(
% 1.49/0.54    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 1.49/0.54    inference(cnf_transformation,[],[f42])).
% 1.49/0.55  fof(f103,plain,(
% 1.49/0.55    ~spl5_1 | spl5_2),
% 1.49/0.55    inference(avatar_split_clause,[],[f65,f100,f96])).
% 1.49/0.55  fof(f65,plain,(
% 1.49/0.55    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 1.49/0.55    inference(cnf_transformation,[],[f42])).
% 1.49/0.55  % SZS output end Proof for theBenchmark
% 1.49/0.55  % (6483)------------------------------
% 1.49/0.55  % (6483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (6483)Termination reason: Refutation
% 1.49/0.55  
% 1.49/0.55  % (6483)Memory used [KB]: 6652
% 1.49/0.55  % (6483)Time elapsed: 0.141 s
% 1.49/0.55  % (6483)------------------------------
% 1.49/0.55  % (6483)------------------------------
% 1.49/0.55  % (6470)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.55  % (6457)Success in time 0.188 s
%------------------------------------------------------------------------------
