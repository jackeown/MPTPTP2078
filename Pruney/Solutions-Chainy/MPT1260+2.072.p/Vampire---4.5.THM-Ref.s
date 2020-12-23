%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:45 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 364 expanded)
%              Number of leaves         :   39 ( 133 expanded)
%              Depth                    :   13
%              Number of atoms          :  558 (1128 expanded)
%              Number of equality atoms :   94 ( 228 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f825,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f91,f96,f101,f106,f171,f197,f284,f322,f357,f503,f527,f618,f664,f670,f677,f689,f721,f781,f800,f824])).

fof(f824,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f800,plain,
    ( spl2_39
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_49 ),
    inference(avatar_split_clause,[],[f799,f776,f98,f93,f521])).

fof(f521,plain,
    ( spl2_39
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f93,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f98,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f776,plain,
    ( spl2_49
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f799,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_49 ),
    inference(subsumption_resolution,[],[f798,f100])).

fof(f100,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f798,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_49 ),
    inference(subsumption_resolution,[],[f788,f95])).

fof(f95,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f788,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_49 ),
    inference(superposition,[],[f203,f778])).

fof(f778,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f776])).

fof(f203,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f57,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f781,plain,
    ( spl2_49
    | ~ spl2_18
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f780,f487,f315,f776])).

fof(f315,plain,
    ( spl2_18
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f487,plain,
    ( spl2_33
  <=> sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f780,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_18
    | ~ spl2_33 ),
    inference(subsumption_resolution,[],[f773,f316])).

fof(f316,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f315])).

fof(f773,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_33 ),
    inference(superposition,[],[f57,f489])).

fof(f489,plain,
    ( sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f487])).

fof(f721,plain,(
    ~ spl2_32 ),
    inference(avatar_contradiction_clause,[],[f706])).

fof(f706,plain,
    ( $false
    | ~ spl2_32 ),
    inference(unit_resulting_resolution,[],[f115,f115,f485,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f485,plain,
    ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f484])).

fof(f484,plain,
    ( spl2_32
  <=> ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f115,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f79,f75])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f79,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

% (14411)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (14401)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (14417)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f689,plain,
    ( spl2_23
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f683,f151,f338])).

fof(f338,plain,
    ( spl2_23
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f151,plain,
    ( spl2_10
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f683,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_10 ),
    inference(superposition,[],[f115,f153])).

fof(f153,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f151])).

fof(f677,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f676,f147,f87,f151])).

fof(f87,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f147,plain,
    ( spl2_9
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f676,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f673,f148])).

fof(f148,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f673,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f57,f88])).

fof(f88,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f670,plain,
    ( ~ spl2_38
    | ~ spl2_1
    | spl2_39
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f619,f98,f93,f521,f83,f517])).

fof(f517,plain,
    ( spl2_38
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f83,plain,
    ( spl2_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f619,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f598,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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

fof(f598,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f270,f95])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | k1_tops_1(sK0,sK1) = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(superposition,[],[f249,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f134,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f134,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f62,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f249,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),X0))
        | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),X0),sK1)
        | k1_tops_1(sK0,sK1) = k4_xboole_0(u1_struct_0(sK0),X0)
        | ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) )
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f227,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f227,plain,
    ( ! [X1] :
        ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),X1),k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X1),sK0)
        | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),X1),sK1) )
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f225,f115])).

fof(f225,plain,
    ( ! [X16] :
        ( ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X16,sK0)
        | r1_tarski(X16,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X16,sK1) )
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f223,f100])).

fof(f223,plain,
    ( ! [X16] :
        ( ~ r1_tarski(X16,sK1)
        | ~ v3_pre_topc(X16,sK0)
        | r1_tarski(X16,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_3 ),
    inference(resolution,[],[f70,f95])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f664,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_10
    | ~ spl2_39 ),
    inference(avatar_contradiction_clause,[],[f663])).

fof(f663,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_10
    | ~ spl2_39 ),
    inference(subsumption_resolution,[],[f662,f100])).

fof(f662,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | spl2_10
    | ~ spl2_39 ),
    inference(subsumption_resolution,[],[f661,f95])).

fof(f661,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_10
    | ~ spl2_39 ),
    inference(subsumption_resolution,[],[f655,f152])).

fof(f152,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f151])).

fof(f655,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_39 ),
    inference(superposition,[],[f451,f523])).

fof(f523,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f521])).

fof(f451,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f216,f207])).

fof(f207,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f206,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f206,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f205])).

fof(f205,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f77,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f216,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f63,f57])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f618,plain,
    ( spl2_38
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f617,f98,f93,f517])).

fof(f617,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f609,f100])).

fof(f609,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f360,f95])).

fof(f360,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5)))
      | r1_tarski(k1_tops_1(X5,X4),X4)
      | ~ l1_pre_topc(X5) ) ),
    inference(superposition,[],[f116,f203])).

fof(f116,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f115,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f527,plain,
    ( ~ spl2_10
    | spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f526,f147,f87,f151])).

fof(f526,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl2_2
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f525,f148])).

fof(f525,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2 ),
    inference(superposition,[],[f89,f57])).

fof(f89,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f503,plain,
    ( spl2_32
    | ~ spl2_23
    | spl2_33
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f465,f319,f487,f338,f484])).

fof(f319,plain,
    ( spl2_19
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f465,plain,
    ( ! [X2] :
        ( sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl2_19 ),
    inference(superposition,[],[f214,f321])).

fof(f321,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f319])).

fof(f214,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f210,f73])).

fof(f210,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f65,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f357,plain,
    ( ~ spl2_12
    | spl2_18 ),
    inference(avatar_contradiction_clause,[],[f356])).

fof(f356,plain,
    ( $false
    | ~ spl2_12
    | spl2_18 ),
    inference(subsumption_resolution,[],[f354,f170])).

fof(f170,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl2_12
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f354,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl2_18 ),
    inference(resolution,[],[f317,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f317,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl2_18 ),
    inference(avatar_component_clause,[],[f315])).

fof(f322,plain,
    ( ~ spl2_18
    | spl2_19
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f310,f151,f319,f315])).

fof(f310,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_10 ),
    inference(superposition,[],[f140,f153])).

fof(f140,plain,(
    ! [X2,X3] :
      ( k3_subset_1(X2,k4_xboole_0(X2,X3)) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X2,X3] :
      ( k3_subset_1(X2,k4_xboole_0(X2,X3)) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f61,f62])).

fof(f284,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_9 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_9 ),
    inference(subsumption_resolution,[],[f282,f100])).

fof(f282,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | spl2_9 ),
    inference(subsumption_resolution,[],[f272,f95])).

fof(f272,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_9 ),
    inference(resolution,[],[f207,f149])).

fof(f149,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f197,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f192,f103,f98,f93,f194])).

fof(f194,plain,
    ( spl2_15
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f103,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f192,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f191,f105])).

fof(f105,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f191,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f189,f100])).

fof(f189,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f69,f95])).

fof(f69,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f171,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f166,f98,f93,f168])).

fof(f166,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f165,f100])).

fof(f165,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f67,f95])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f106,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f52,f103])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f45,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f101,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f53,f98])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f96,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f54,f93])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f91,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f55,f87,f83])).

fof(f55,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f90,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f56,f87,f83])).

fof(f56,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:08:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.50  % (14405)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.51  % (14418)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.51  % (14402)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.52  % (14398)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.52  % (14415)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.36/0.53  % (14407)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.36/0.53  % (14421)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.36/0.54  % (14394)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.36/0.54  % (14404)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.36/0.54  % (14413)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.54/0.55  % (14423)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.54/0.55  % (14410)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.54/0.55  % (14416)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.54/0.55  % (14397)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.54/0.56  % (14408)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.54/0.56  % (14399)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.54/0.56  % (14412)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.54/0.56  % (14404)Refutation not found, incomplete strategy% (14404)------------------------------
% 1.54/0.56  % (14404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (14404)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (14404)Memory used [KB]: 10874
% 1.54/0.56  % (14404)Time elapsed: 0.146 s
% 1.54/0.56  % (14404)------------------------------
% 1.54/0.56  % (14404)------------------------------
% 1.54/0.57  % (14400)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.54/0.57  % (14420)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.54/0.57  % (14422)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.54/0.58  % (14403)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.54/0.58  % (14410)Refutation not found, incomplete strategy% (14410)------------------------------
% 1.54/0.58  % (14410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (14410)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.58  
% 1.54/0.58  % (14410)Memory used [KB]: 10746
% 1.54/0.58  % (14410)Time elapsed: 0.188 s
% 1.54/0.58  % (14410)------------------------------
% 1.54/0.58  % (14410)------------------------------
% 1.54/0.58  % (14395)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.54/0.59  % (14414)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.54/0.59  % (14419)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.54/0.60  % (14422)Refutation not found, incomplete strategy% (14422)------------------------------
% 1.54/0.60  % (14422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.60  % (14422)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.60  
% 1.54/0.60  % (14422)Memory used [KB]: 10874
% 1.54/0.60  % (14422)Time elapsed: 0.184 s
% 1.54/0.60  % (14422)------------------------------
% 1.54/0.60  % (14422)------------------------------
% 1.54/0.60  % (14406)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.54/0.60  % (14396)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.54/0.61  % (14415)Refutation found. Thanks to Tanya!
% 1.54/0.61  % SZS status Theorem for theBenchmark
% 1.54/0.61  % SZS output start Proof for theBenchmark
% 1.54/0.61  fof(f825,plain,(
% 1.54/0.61    $false),
% 1.54/0.61    inference(avatar_sat_refutation,[],[f90,f91,f96,f101,f106,f171,f197,f284,f322,f357,f503,f527,f618,f664,f670,f677,f689,f721,f781,f800,f824])).
% 1.54/0.61  fof(f824,plain,(
% 1.54/0.61    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.54/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.54/0.61  fof(f800,plain,(
% 1.54/0.61    spl2_39 | ~spl2_3 | ~spl2_4 | ~spl2_49),
% 1.54/0.61    inference(avatar_split_clause,[],[f799,f776,f98,f93,f521])).
% 1.54/0.61  fof(f521,plain,(
% 1.54/0.61    spl2_39 <=> sK1 = k1_tops_1(sK0,sK1)),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 1.54/0.61  fof(f93,plain,(
% 1.54/0.61    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.54/0.61  fof(f98,plain,(
% 1.54/0.61    spl2_4 <=> l1_pre_topc(sK0)),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.54/0.61  fof(f776,plain,(
% 1.54/0.61    spl2_49 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 1.54/0.61  fof(f799,plain,(
% 1.54/0.61    sK1 = k1_tops_1(sK0,sK1) | (~spl2_3 | ~spl2_4 | ~spl2_49)),
% 1.54/0.61    inference(subsumption_resolution,[],[f798,f100])).
% 1.54/0.61  fof(f100,plain,(
% 1.54/0.61    l1_pre_topc(sK0) | ~spl2_4),
% 1.54/0.61    inference(avatar_component_clause,[],[f98])).
% 1.54/0.61  fof(f798,plain,(
% 1.54/0.61    sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_49)),
% 1.54/0.61    inference(subsumption_resolution,[],[f788,f95])).
% 1.54/0.61  fof(f95,plain,(
% 1.54/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 1.54/0.61    inference(avatar_component_clause,[],[f93])).
% 1.54/0.61  fof(f788,plain,(
% 1.54/0.61    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_49),
% 1.54/0.61    inference(superposition,[],[f203,f778])).
% 1.54/0.61  fof(f778,plain,(
% 1.54/0.61    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_49),
% 1.54/0.61    inference(avatar_component_clause,[],[f776])).
% 1.54/0.61  fof(f203,plain,(
% 1.54/0.61    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.54/0.61    inference(duplicate_literal_removal,[],[f202])).
% 1.54/0.61  fof(f202,plain,(
% 1.54/0.61    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.54/0.61    inference(superposition,[],[f57,f64])).
% 1.54/0.61  fof(f64,plain,(
% 1.54/0.61    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.54/0.61    inference(cnf_transformation,[],[f30])).
% 1.54/0.61  fof(f30,plain,(
% 1.54/0.61    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.61    inference(ennf_transformation,[],[f21])).
% 1.54/0.61  fof(f21,axiom,(
% 1.54/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.54/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 1.54/0.61  fof(f57,plain,(
% 1.54/0.61    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.54/0.61    inference(cnf_transformation,[],[f26])).
% 1.54/0.61  fof(f26,plain,(
% 1.54/0.61    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.61    inference(ennf_transformation,[],[f11])).
% 1.54/0.61  fof(f11,axiom,(
% 1.54/0.61    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.54/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.54/0.61  fof(f781,plain,(
% 1.54/0.61    spl2_49 | ~spl2_18 | ~spl2_33),
% 1.54/0.61    inference(avatar_split_clause,[],[f780,f487,f315,f776])).
% 1.54/0.61  fof(f315,plain,(
% 1.54/0.61    spl2_18 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 1.54/0.61  fof(f487,plain,(
% 1.54/0.61    spl2_33 <=> sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 1.54/0.61  fof(f780,plain,(
% 1.54/0.61    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_18 | ~spl2_33)),
% 1.54/0.61    inference(subsumption_resolution,[],[f773,f316])).
% 1.54/0.61  fof(f316,plain,(
% 1.54/0.61    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_18),
% 1.54/0.61    inference(avatar_component_clause,[],[f315])).
% 1.54/0.61  fof(f773,plain,(
% 1.54/0.61    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_33),
% 1.54/0.61    inference(superposition,[],[f57,f489])).
% 1.54/0.61  fof(f489,plain,(
% 1.54/0.61    sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) | ~spl2_33),
% 1.54/0.61    inference(avatar_component_clause,[],[f487])).
% 1.54/0.61  fof(f721,plain,(
% 1.54/0.61    ~spl2_32),
% 1.54/0.61    inference(avatar_contradiction_clause,[],[f706])).
% 1.54/0.61  fof(f706,plain,(
% 1.54/0.61    $false | ~spl2_32),
% 1.54/0.61    inference(unit_resulting_resolution,[],[f115,f115,f485,f77])).
% 1.54/0.61  fof(f77,plain,(
% 1.54/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.54/0.61    inference(cnf_transformation,[],[f43])).
% 1.54/0.61  fof(f43,plain,(
% 1.54/0.61    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.61    inference(flattening,[],[f42])).
% 1.54/0.61  fof(f42,plain,(
% 1.54/0.61    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.54/0.61    inference(ennf_transformation,[],[f5])).
% 1.54/0.61  fof(f5,axiom,(
% 1.54/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.54/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 1.54/0.61  fof(f485,plain,(
% 1.54/0.61    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl2_32),
% 1.54/0.61    inference(avatar_component_clause,[],[f484])).
% 1.54/0.61  fof(f484,plain,(
% 1.54/0.61    spl2_32 <=> ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 1.54/0.61  fof(f115,plain,(
% 1.54/0.61    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 1.54/0.61    inference(backward_demodulation,[],[f79,f75])).
% 1.54/0.61  fof(f75,plain,(
% 1.54/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.54/0.61    inference(cnf_transformation,[],[f10])).
% 1.54/0.61  fof(f10,axiom,(
% 1.54/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.54/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.54/0.61  fof(f79,plain,(
% 1.54/0.61    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.54/0.61    inference(cnf_transformation,[],[f6])).
% 1.54/0.62  % (14411)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.54/0.62  % (14401)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.54/0.62  % (14417)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.54/0.62  fof(f6,axiom,(
% 1.54/0.62    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 1.54/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 1.54/0.62  fof(f689,plain,(
% 1.54/0.62    spl2_23 | ~spl2_10),
% 1.54/0.62    inference(avatar_split_clause,[],[f683,f151,f338])).
% 1.54/0.62  fof(f338,plain,(
% 1.54/0.62    spl2_23 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 1.54/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 1.54/0.62  fof(f151,plain,(
% 1.54/0.62    spl2_10 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 1.54/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.54/0.62  fof(f683,plain,(
% 1.54/0.62    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_10),
% 1.54/0.62    inference(superposition,[],[f115,f153])).
% 1.54/0.62  fof(f153,plain,(
% 1.54/0.62    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_10),
% 1.54/0.62    inference(avatar_component_clause,[],[f151])).
% 1.54/0.62  fof(f677,plain,(
% 1.54/0.62    spl2_10 | ~spl2_2 | ~spl2_9),
% 1.54/0.62    inference(avatar_split_clause,[],[f676,f147,f87,f151])).
% 1.54/0.62  fof(f87,plain,(
% 1.54/0.62    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 1.54/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.54/0.62  fof(f147,plain,(
% 1.54/0.62    spl2_9 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.54/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.54/0.62  fof(f676,plain,(
% 1.54/0.62    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl2_2 | ~spl2_9)),
% 1.54/0.62    inference(subsumption_resolution,[],[f673,f148])).
% 1.54/0.62  fof(f148,plain,(
% 1.54/0.62    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_9),
% 1.54/0.62    inference(avatar_component_clause,[],[f147])).
% 1.54/0.62  fof(f673,plain,(
% 1.54/0.62    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.54/0.62    inference(superposition,[],[f57,f88])).
% 1.54/0.62  fof(f88,plain,(
% 1.54/0.62    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 1.54/0.62    inference(avatar_component_clause,[],[f87])).
% 1.54/0.62  fof(f670,plain,(
% 1.54/0.62    ~spl2_38 | ~spl2_1 | spl2_39 | ~spl2_3 | ~spl2_4),
% 1.54/0.62    inference(avatar_split_clause,[],[f619,f98,f93,f521,f83,f517])).
% 1.54/0.62  fof(f517,plain,(
% 1.54/0.62    spl2_38 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.54/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 1.54/0.63  fof(f83,plain,(
% 1.54/0.63    spl2_1 <=> v3_pre_topc(sK1,sK0)),
% 1.54/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.54/0.63  fof(f619,plain,(
% 1.54/0.63    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_4)),
% 1.54/0.63    inference(subsumption_resolution,[],[f598,f80])).
% 1.54/0.63  fof(f80,plain,(
% 1.54/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.54/0.63    inference(equality_resolution,[],[f59])).
% 1.54/0.63  fof(f59,plain,(
% 1.54/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.54/0.63    inference(cnf_transformation,[],[f50])).
% 1.54/0.63  fof(f50,plain,(
% 1.54/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.54/0.63    inference(flattening,[],[f49])).
% 1.54/0.63  fof(f49,plain,(
% 1.54/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.54/0.63    inference(nnf_transformation,[],[f1])).
% 1.54/0.63  fof(f1,axiom,(
% 1.54/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.54/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.54/0.63  fof(f598,plain,(
% 1.54/0.63    ~r1_tarski(sK1,sK1) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_4)),
% 1.54/0.63    inference(resolution,[],[f270,f95])).
% 1.54/0.63  fof(f270,plain,(
% 1.54/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k1_tops_1(sK0,sK1) = X0 | ~v3_pre_topc(X0,sK0) | ~r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | (~spl2_3 | ~spl2_4)),
% 1.54/0.63    inference(superposition,[],[f249,f142])).
% 1.54/0.63  fof(f142,plain,(
% 1.54/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.54/0.63    inference(subsumption_resolution,[],[f134,f73])).
% 1.54/0.63  fof(f73,plain,(
% 1.54/0.63    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.54/0.63    inference(cnf_transformation,[],[f40])).
% 1.54/0.63  fof(f40,plain,(
% 1.54/0.63    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.63    inference(ennf_transformation,[],[f4])).
% 1.54/0.63  fof(f4,axiom,(
% 1.54/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.54/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.54/0.63  fof(f134,plain,(
% 1.54/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.54/0.63    inference(superposition,[],[f62,f61])).
% 1.54/0.63  fof(f61,plain,(
% 1.54/0.63    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.54/0.63    inference(cnf_transformation,[],[f27])).
% 1.54/0.63  fof(f27,plain,(
% 1.54/0.63    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.63    inference(ennf_transformation,[],[f8])).
% 1.54/0.63  fof(f8,axiom,(
% 1.54/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.54/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.54/0.63  fof(f62,plain,(
% 1.54/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.54/0.63    inference(cnf_transformation,[],[f28])).
% 1.54/0.63  fof(f28,plain,(
% 1.54/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.63    inference(ennf_transformation,[],[f3])).
% 1.54/0.63  fof(f3,axiom,(
% 1.54/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.54/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.54/0.63  fof(f249,plain,(
% 1.54/0.63    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),X0)) | ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),X0),sK1) | k1_tops_1(sK0,sK1) = k4_xboole_0(u1_struct_0(sK0),X0) | ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0)) ) | (~spl2_3 | ~spl2_4)),
% 1.54/0.63    inference(resolution,[],[f227,f60])).
% 1.54/0.63  fof(f60,plain,(
% 1.54/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.54/0.63    inference(cnf_transformation,[],[f50])).
% 1.54/0.63  fof(f227,plain,(
% 1.54/0.63    ( ! [X1] : (r1_tarski(k4_xboole_0(u1_struct_0(sK0),X1),k1_tops_1(sK0,sK1)) | ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X1),sK0) | ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),X1),sK1)) ) | (~spl2_3 | ~spl2_4)),
% 1.54/0.63    inference(resolution,[],[f225,f115])).
% 1.54/0.63  fof(f225,plain,(
% 1.54/0.63    ( ! [X16] : (~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X16,sK0) | r1_tarski(X16,k1_tops_1(sK0,sK1)) | ~r1_tarski(X16,sK1)) ) | (~spl2_3 | ~spl2_4)),
% 1.54/0.63    inference(subsumption_resolution,[],[f223,f100])).
% 1.54/0.63  fof(f223,plain,(
% 1.54/0.63    ( ! [X16] : (~r1_tarski(X16,sK1) | ~v3_pre_topc(X16,sK0) | r1_tarski(X16,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl2_3),
% 1.54/0.63    inference(resolution,[],[f70,f95])).
% 1.54/0.63  fof(f70,plain,(
% 1.54/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.54/0.63    inference(cnf_transformation,[],[f39])).
% 1.54/0.63  fof(f39,plain,(
% 1.54/0.63    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.63    inference(flattening,[],[f38])).
% 1.54/0.63  fof(f38,plain,(
% 1.54/0.63    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.63    inference(ennf_transformation,[],[f19])).
% 1.54/0.63  fof(f19,axiom,(
% 1.54/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.54/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 1.54/0.63  fof(f664,plain,(
% 1.54/0.63    ~spl2_3 | ~spl2_4 | spl2_10 | ~spl2_39),
% 1.54/0.63    inference(avatar_contradiction_clause,[],[f663])).
% 1.54/0.63  fof(f663,plain,(
% 1.54/0.63    $false | (~spl2_3 | ~spl2_4 | spl2_10 | ~spl2_39)),
% 1.54/0.63    inference(subsumption_resolution,[],[f662,f100])).
% 1.54/0.63  fof(f662,plain,(
% 1.54/0.63    ~l1_pre_topc(sK0) | (~spl2_3 | spl2_10 | ~spl2_39)),
% 1.54/0.63    inference(subsumption_resolution,[],[f661,f95])).
% 1.54/0.63  fof(f661,plain,(
% 1.54/0.63    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_10 | ~spl2_39)),
% 1.54/0.63    inference(subsumption_resolution,[],[f655,f152])).
% 1.54/0.63  fof(f152,plain,(
% 1.54/0.63    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | spl2_10),
% 1.54/0.63    inference(avatar_component_clause,[],[f151])).
% 1.54/0.63  fof(f655,plain,(
% 1.54/0.63    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_39),
% 1.54/0.63    inference(superposition,[],[f451,f523])).
% 1.54/0.63  fof(f523,plain,(
% 1.54/0.63    sK1 = k1_tops_1(sK0,sK1) | ~spl2_39),
% 1.54/0.63    inference(avatar_component_clause,[],[f521])).
% 1.54/0.63  fof(f451,plain,(
% 1.54/0.63    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 1.54/0.63    inference(subsumption_resolution,[],[f216,f207])).
% 1.54/0.63  fof(f207,plain,(
% 1.54/0.63    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.54/0.63    inference(subsumption_resolution,[],[f206,f68])).
% 1.54/0.63  fof(f68,plain,(
% 1.54/0.63    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.54/0.63    inference(cnf_transformation,[],[f35])).
% 1.54/0.63  fof(f35,plain,(
% 1.54/0.63    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.54/0.63    inference(flattening,[],[f34])).
% 1.54/0.63  fof(f34,plain,(
% 1.54/0.63    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.54/0.63    inference(ennf_transformation,[],[f16])).
% 1.54/0.63  fof(f16,axiom,(
% 1.54/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.54/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.54/0.63  fof(f206,plain,(
% 1.54/0.63    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.54/0.63    inference(duplicate_literal_removal,[],[f205])).
% 1.54/0.63  fof(f205,plain,(
% 1.54/0.63    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.54/0.63    inference(superposition,[],[f77,f66])).
% 1.54/0.63  fof(f66,plain,(
% 1.54/0.63    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.54/0.63    inference(cnf_transformation,[],[f32])).
% 1.54/0.63  fof(f32,plain,(
% 1.54/0.63    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.63    inference(ennf_transformation,[],[f20])).
% 1.54/0.63  fof(f20,axiom,(
% 1.54/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.54/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 1.54/0.63  fof(f216,plain,(
% 1.54/0.63    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.54/0.63    inference(superposition,[],[f63,f57])).
% 1.54/0.63  fof(f63,plain,(
% 1.54/0.63    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.54/0.63    inference(cnf_transformation,[],[f29])).
% 1.54/0.63  fof(f29,plain,(
% 1.54/0.63    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.63    inference(ennf_transformation,[],[f18])).
% 1.54/0.63  fof(f18,axiom,(
% 1.54/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.54/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 1.54/0.63  fof(f618,plain,(
% 1.54/0.63    spl2_38 | ~spl2_3 | ~spl2_4),
% 1.54/0.63    inference(avatar_split_clause,[],[f617,f98,f93,f517])).
% 1.54/0.63  fof(f617,plain,(
% 1.54/0.63    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_4)),
% 1.54/0.63    inference(subsumption_resolution,[],[f609,f100])).
% 1.54/0.63  fof(f609,plain,(
% 1.54/0.63    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl2_3),
% 1.54/0.63    inference(resolution,[],[f360,f95])).
% 1.54/0.63  fof(f360,plain,(
% 1.54/0.63    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5))) | r1_tarski(k1_tops_1(X5,X4),X4) | ~l1_pre_topc(X5)) )),
% 1.54/0.63    inference(superposition,[],[f116,f203])).
% 1.54/0.63  fof(f116,plain,(
% 1.54/0.63    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.54/0.63    inference(resolution,[],[f115,f71])).
% 1.54/0.63  fof(f71,plain,(
% 1.54/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.54/0.63    inference(cnf_transformation,[],[f51])).
% 1.54/0.63  fof(f51,plain,(
% 1.54/0.63    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.54/0.63    inference(nnf_transformation,[],[f14])).
% 1.54/0.63  fof(f14,axiom,(
% 1.54/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.54/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.54/0.63  fof(f527,plain,(
% 1.54/0.63    ~spl2_10 | spl2_2 | ~spl2_9),
% 1.54/0.63    inference(avatar_split_clause,[],[f526,f147,f87,f151])).
% 1.54/0.63  fof(f526,plain,(
% 1.54/0.63    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (spl2_2 | ~spl2_9)),
% 1.54/0.63    inference(subsumption_resolution,[],[f525,f148])).
% 1.54/0.63  fof(f525,plain,(
% 1.54/0.63    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_2),
% 1.54/0.63    inference(superposition,[],[f89,f57])).
% 1.54/0.63  fof(f89,plain,(
% 1.54/0.63    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl2_2),
% 1.54/0.63    inference(avatar_component_clause,[],[f87])).
% 1.54/0.63  fof(f503,plain,(
% 1.54/0.63    spl2_32 | ~spl2_23 | spl2_33 | ~spl2_19),
% 1.54/0.63    inference(avatar_split_clause,[],[f465,f319,f487,f338,f484])).
% 1.54/0.63  fof(f319,plain,(
% 1.54/0.63    spl2_19 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 1.54/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 1.54/0.63  fof(f465,plain,(
% 1.54/0.63    ( ! [X2] : (sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl2_19),
% 1.54/0.63    inference(superposition,[],[f214,f321])).
% 1.54/0.63  fof(f321,plain,(
% 1.54/0.63    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_19),
% 1.54/0.63    inference(avatar_component_clause,[],[f319])).
% 1.54/0.63  fof(f214,plain,(
% 1.54/0.63    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 1.54/0.63    inference(subsumption_resolution,[],[f210,f73])).
% 1.54/0.63  fof(f210,plain,(
% 1.54/0.63    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 1.54/0.63    inference(superposition,[],[f65,f76])).
% 1.54/0.63  fof(f76,plain,(
% 1.54/0.63    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.54/0.63    inference(cnf_transformation,[],[f41])).
% 1.54/0.63  fof(f41,plain,(
% 1.54/0.63    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.54/0.63    inference(ennf_transformation,[],[f7])).
% 1.54/0.63  fof(f7,axiom,(
% 1.54/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 1.54/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 1.54/0.63  fof(f65,plain,(
% 1.54/0.63    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.54/0.63    inference(cnf_transformation,[],[f31])).
% 1.54/0.63  fof(f31,plain,(
% 1.54/0.63    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.63    inference(ennf_transformation,[],[f12])).
% 1.54/0.63  fof(f12,axiom,(
% 1.54/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.54/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 1.54/0.63  fof(f357,plain,(
% 1.54/0.63    ~spl2_12 | spl2_18),
% 1.54/0.63    inference(avatar_contradiction_clause,[],[f356])).
% 1.54/0.63  fof(f356,plain,(
% 1.54/0.63    $false | (~spl2_12 | spl2_18)),
% 1.54/0.63    inference(subsumption_resolution,[],[f354,f170])).
% 1.54/0.63  fof(f170,plain,(
% 1.54/0.63    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_12),
% 1.54/0.63    inference(avatar_component_clause,[],[f168])).
% 1.54/0.63  fof(f168,plain,(
% 1.54/0.63    spl2_12 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 1.54/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.54/0.63  fof(f354,plain,(
% 1.54/0.63    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl2_18),
% 1.54/0.63    inference(resolution,[],[f317,f72])).
% 1.54/0.63  fof(f72,plain,(
% 1.54/0.63    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.54/0.63    inference(cnf_transformation,[],[f51])).
% 1.54/0.63  fof(f317,plain,(
% 1.54/0.63    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl2_18),
% 1.54/0.63    inference(avatar_component_clause,[],[f315])).
% 1.54/0.63  fof(f322,plain,(
% 1.54/0.63    ~spl2_18 | spl2_19 | ~spl2_10),
% 1.54/0.63    inference(avatar_split_clause,[],[f310,f151,f319,f315])).
% 1.54/0.63  fof(f310,plain,(
% 1.54/0.63    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_10),
% 1.54/0.63    inference(superposition,[],[f140,f153])).
% 1.54/0.63  fof(f140,plain,(
% 1.54/0.63    ( ! [X2,X3] : (k3_subset_1(X2,k4_xboole_0(X2,X3)) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 1.54/0.63    inference(duplicate_literal_removal,[],[f136])).
% 1.54/0.63  fof(f136,plain,(
% 1.54/0.63    ( ! [X2,X3] : (k3_subset_1(X2,k4_xboole_0(X2,X3)) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 1.54/0.63    inference(superposition,[],[f61,f62])).
% 1.54/0.63  fof(f284,plain,(
% 1.54/0.63    ~spl2_3 | ~spl2_4 | spl2_9),
% 1.54/0.63    inference(avatar_contradiction_clause,[],[f283])).
% 1.54/0.63  fof(f283,plain,(
% 1.54/0.63    $false | (~spl2_3 | ~spl2_4 | spl2_9)),
% 1.54/0.63    inference(subsumption_resolution,[],[f282,f100])).
% 1.54/0.63  fof(f282,plain,(
% 1.54/0.63    ~l1_pre_topc(sK0) | (~spl2_3 | spl2_9)),
% 1.54/0.63    inference(subsumption_resolution,[],[f272,f95])).
% 1.54/0.63  fof(f272,plain,(
% 1.54/0.63    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_9),
% 1.54/0.63    inference(resolution,[],[f207,f149])).
% 1.54/0.63  fof(f149,plain,(
% 1.54/0.63    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_9),
% 1.54/0.63    inference(avatar_component_clause,[],[f147])).
% 1.54/0.63  fof(f197,plain,(
% 1.54/0.63    spl2_15 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 1.54/0.63    inference(avatar_split_clause,[],[f192,f103,f98,f93,f194])).
% 1.54/0.63  fof(f194,plain,(
% 1.54/0.63    spl2_15 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.54/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 1.54/0.63  fof(f103,plain,(
% 1.54/0.63    spl2_5 <=> v2_pre_topc(sK0)),
% 1.54/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.54/0.63  fof(f192,plain,(
% 1.54/0.63    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 1.54/0.63    inference(subsumption_resolution,[],[f191,f105])).
% 1.54/0.63  fof(f105,plain,(
% 1.54/0.63    v2_pre_topc(sK0) | ~spl2_5),
% 1.54/0.63    inference(avatar_component_clause,[],[f103])).
% 1.54/0.63  fof(f191,plain,(
% 1.54/0.63    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl2_3 | ~spl2_4)),
% 1.54/0.63    inference(subsumption_resolution,[],[f189,f100])).
% 1.54/0.63  fof(f189,plain,(
% 1.54/0.63    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_3),
% 1.54/0.63    inference(resolution,[],[f69,f95])).
% 1.54/0.63  fof(f69,plain,(
% 1.54/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.54/0.63    inference(cnf_transformation,[],[f37])).
% 1.54/0.63  fof(f37,plain,(
% 1.54/0.63    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.54/0.63    inference(flattening,[],[f36])).
% 1.54/0.63  fof(f36,plain,(
% 1.54/0.63    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.54/0.63    inference(ennf_transformation,[],[f17])).
% 1.54/0.63  fof(f17,axiom,(
% 1.54/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.54/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.54/0.63  fof(f171,plain,(
% 1.54/0.63    spl2_12 | ~spl2_3 | ~spl2_4),
% 1.54/0.63    inference(avatar_split_clause,[],[f166,f98,f93,f168])).
% 1.54/0.63  fof(f166,plain,(
% 1.54/0.63    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 1.54/0.63    inference(subsumption_resolution,[],[f165,f100])).
% 1.54/0.63  fof(f165,plain,(
% 1.54/0.63    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl2_3),
% 1.54/0.63    inference(resolution,[],[f67,f95])).
% 1.54/0.63  fof(f67,plain,(
% 1.54/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.54/0.63    inference(cnf_transformation,[],[f33])).
% 1.54/0.63  fof(f33,plain,(
% 1.54/0.63    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.63    inference(ennf_transformation,[],[f15])).
% 1.54/0.63  fof(f15,axiom,(
% 1.54/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 1.54/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 1.54/0.63  fof(f106,plain,(
% 1.54/0.63    spl2_5),
% 1.54/0.63    inference(avatar_split_clause,[],[f52,f103])).
% 1.54/0.63  fof(f52,plain,(
% 1.54/0.63    v2_pre_topc(sK0)),
% 1.54/0.63    inference(cnf_transformation,[],[f48])).
% 1.54/0.63  fof(f48,plain,(
% 1.54/0.63    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.54/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f45,f47,f46])).
% 1.54/0.63  fof(f46,plain,(
% 1.54/0.63    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.54/0.63    introduced(choice_axiom,[])).
% 1.54/0.63  fof(f47,plain,(
% 1.54/0.63    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.54/0.63    introduced(choice_axiom,[])).
% 1.54/0.63  fof(f45,plain,(
% 1.54/0.63    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.54/0.63    inference(flattening,[],[f44])).
% 1.54/0.63  fof(f44,plain,(
% 1.54/0.63    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.54/0.63    inference(nnf_transformation,[],[f25])).
% 1.54/0.63  fof(f25,plain,(
% 1.54/0.63    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.54/0.63    inference(flattening,[],[f24])).
% 1.54/0.63  fof(f24,plain,(
% 1.54/0.63    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.54/0.63    inference(ennf_transformation,[],[f23])).
% 1.54/0.63  fof(f23,negated_conjecture,(
% 1.54/0.63    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.54/0.63    inference(negated_conjecture,[],[f22])).
% 1.54/0.63  fof(f22,conjecture,(
% 1.54/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.54/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 1.54/0.63  fof(f101,plain,(
% 1.54/0.63    spl2_4),
% 1.54/0.63    inference(avatar_split_clause,[],[f53,f98])).
% 1.54/0.63  fof(f53,plain,(
% 1.54/0.63    l1_pre_topc(sK0)),
% 1.54/0.63    inference(cnf_transformation,[],[f48])).
% 1.54/0.63  fof(f96,plain,(
% 1.54/0.63    spl2_3),
% 1.54/0.63    inference(avatar_split_clause,[],[f54,f93])).
% 1.54/0.63  fof(f54,plain,(
% 1.54/0.63    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.54/0.63    inference(cnf_transformation,[],[f48])).
% 1.54/0.63  fof(f91,plain,(
% 1.54/0.63    spl2_1 | spl2_2),
% 1.54/0.63    inference(avatar_split_clause,[],[f55,f87,f83])).
% 1.54/0.63  fof(f55,plain,(
% 1.54/0.63    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 1.54/0.63    inference(cnf_transformation,[],[f48])).
% 1.54/0.63  fof(f90,plain,(
% 1.54/0.63    ~spl2_1 | ~spl2_2),
% 1.54/0.63    inference(avatar_split_clause,[],[f56,f87,f83])).
% 1.54/0.63  fof(f56,plain,(
% 1.54/0.63    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.54/0.63    inference(cnf_transformation,[],[f48])).
% 1.54/0.63  % SZS output end Proof for theBenchmark
% 1.54/0.63  % (14415)------------------------------
% 1.54/0.63  % (14415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.63  % (14415)Termination reason: Refutation
% 1.54/0.63  
% 1.54/0.63  % (14415)Memory used [KB]: 6780
% 1.54/0.63  % (14415)Time elapsed: 0.219 s
% 1.54/0.63  % (14415)------------------------------
% 1.54/0.63  % (14415)------------------------------
% 1.54/0.63  % (14409)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.54/0.63  % (14393)Success in time 0.286 s
%------------------------------------------------------------------------------
