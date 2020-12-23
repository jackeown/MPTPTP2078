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
% DateTime   : Thu Dec  3 13:11:42 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 301 expanded)
%              Number of leaves         :   39 ( 118 expanded)
%              Depth                    :   10
%              Number of atoms          :  509 ( 976 expanded)
%              Number of equality atoms :   87 ( 194 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f87,f92,f97,f102,f116,f157,f204,f223,f236,f364,f407,f422,f480,f492,f498,f505,f1198,f1205,f2159,f2184,f2186])).

fof(f2186,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2184,plain,
    ( spl2_78
    | ~ spl2_82 ),
    inference(avatar_contradiction_clause,[],[f2183])).

fof(f2183,plain,
    ( $false
    | spl2_78
    | ~ spl2_82 ),
    inference(subsumption_resolution,[],[f2168,f1204])).

fof(f1204,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl2_78 ),
    inference(avatar_component_clause,[],[f1202])).

fof(f1202,plain,
    ( spl2_78
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).

fof(f2168,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_82 ),
    inference(superposition,[],[f163,f2155])).

fof(f2155,plain,
    ( sK1 = k3_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_82 ),
    inference(avatar_component_clause,[],[f2153])).

fof(f2153,plain,
    ( spl2_82
  <=> sK1 = k3_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).

fof(f163,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f149,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f149,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f72,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f2159,plain,
    ( spl2_82
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f2158,f460,f94,f89,f2153])).

fof(f89,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f94,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f460,plain,
    ( spl2_37
  <=> sK1 = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f2158,plain,
    ( sK1 = k3_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f2157,f96])).

fof(f96,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f2157,plain,
    ( sK1 = k3_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f2132,f91])).

fof(f91,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f2132,plain,
    ( sK1 = k3_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_37 ),
    inference(superposition,[],[f462,f617])).

% (2713)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
fof(f617,plain,(
    ! [X6,X7] :
      ( k3_xboole_0(k2_pre_topc(X6,X7),k1_tops_1(X6,X7)) = k4_xboole_0(k2_pre_topc(X6,X7),k2_tops_1(X6,X7))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_pre_topc(X6) ) ),
    inference(superposition,[],[f59,f289])).

fof(f289,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f287,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f287,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f63,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f462,plain,
    ( sK1 = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f460])).

fof(f1205,plain,
    ( ~ spl2_78
    | spl2_34
    | ~ spl2_77 ),
    inference(avatar_split_clause,[],[f1199,f1195,f404,f1202])).

fof(f404,plain,
    ( spl2_34
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f1195,plain,
    ( spl2_77
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).

fof(f1199,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_77 ),
    inference(resolution,[],[f1197,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1197,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_77 ),
    inference(avatar_component_clause,[],[f1195])).

fof(f1198,plain,
    ( spl2_77
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f1193,f94,f89,f1195])).

fof(f1193,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f1184,f96])).

fof(f1184,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f540,f91])).

fof(f540,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9)))
      | r1_tarski(k1_tops_1(X9,X8),X8)
      | ~ l1_pre_topc(X9) ) ),
    inference(superposition,[],[f72,f245])).

fof(f245,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f244])).

fof(f244,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f53,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f505,plain,
    ( spl2_32
    | ~ spl2_14
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f504,f352,f184,f356])).

fof(f356,plain,
    ( spl2_32
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f184,plain,
    ( spl2_14
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f352,plain,
    ( spl2_31
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f504,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_14
    | ~ spl2_31 ),
    inference(subsumption_resolution,[],[f500,f353])).

fof(f353,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f352])).

fof(f500,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_14 ),
    inference(superposition,[],[f173,f186])).

fof(f186,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f184])).

fof(f173,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f71,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f498,plain,
    ( spl2_14
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f497,f180,f83,f184])).

fof(f83,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f180,plain,
    ( spl2_13
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f497,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f494,f181])).

fof(f181,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f180])).

fof(f494,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f53,f84])).

fof(f84,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f492,plain,
    ( spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_34 ),
    inference(avatar_contradiction_clause,[],[f491])).

fof(f491,plain,
    ( $false
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f490,f96])).

fof(f490,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f489,f91])).

fof(f489,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f486,f85])).

fof(f85,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f486,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_34 ),
    inference(superposition,[],[f63,f406])).

fof(f406,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f404])).

fof(f480,plain,
    ( ~ spl2_32
    | spl2_37
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f451,f393,f460,f356])).

fof(f393,plain,
    ( spl2_33
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f451,plain,
    ( sK1 = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_33 ),
    inference(superposition,[],[f395,f58])).

fof(f395,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f393])).

fof(f422,plain,
    ( spl2_33
    | ~ spl2_14
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f421,f352,f184,f393])).

fof(f421,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_14
    | ~ spl2_31 ),
    inference(subsumption_resolution,[],[f416,f353])).

fof(f416,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_14 ),
    inference(superposition,[],[f174,f186])).

fof(f174,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f57,f58])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f407,plain,
    ( ~ spl2_1
    | spl2_34
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f402,f114,f94,f89,f404,f79])).

fof(f79,plain,
    ( spl2_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f114,plain,
    ( spl2_9
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f402,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f241,f96])).

fof(f241,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(resolution,[],[f115,f91])).

fof(f115,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f364,plain,
    ( ~ spl2_16
    | spl2_31 ),
    inference(avatar_contradiction_clause,[],[f363])).

fof(f363,plain,
    ( $false
    | ~ spl2_16
    | spl2_31 ),
    inference(subsumption_resolution,[],[f361,f203])).

fof(f203,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl2_16
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f361,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl2_31 ),
    inference(resolution,[],[f354,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f354,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl2_31 ),
    inference(avatar_component_clause,[],[f352])).

fof(f236,plain,
    ( spl2_19
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f231,f99,f94,f89,f233])).

fof(f233,plain,
    ( spl2_19
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f99,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f231,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f230,f101])).

fof(f101,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f230,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f228,f96])).

fof(f228,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f68,f91])).

fof(f68,plain,(
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

fof(f223,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_13 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_13 ),
    inference(subsumption_resolution,[],[f221,f96])).

fof(f221,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | spl2_13 ),
    inference(subsumption_resolution,[],[f216,f91])).

fof(f216,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_13 ),
    inference(resolution,[],[f66,f182])).

fof(f182,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f180])).

fof(f204,plain,
    ( spl2_16
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f199,f94,f89,f201])).

fof(f199,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f198,f96])).

fof(f198,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f67,f91])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f157,plain,
    ( ~ spl2_4
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f96,f101,f75,f112])).

fof(f112,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl2_8
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f116,plain,
    ( spl2_8
    | spl2_9 ),
    inference(avatar_split_clause,[],[f61,f114,f111])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f102,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f48,f99])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f42,plain,
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

fof(f43,plain,
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

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f97,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f49,f94])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f92,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f50,f89])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f87,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f51,f83,f79])).

fof(f51,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f86,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f52,f83,f79])).

fof(f52,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:56:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (2693)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (2710)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (2688)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (2702)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.27/0.52  % (2680)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.27/0.52  % (2690)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.27/0.53  % (2699)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.27/0.53  % (2684)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.27/0.53  % (2683)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.27/0.53  % (2685)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.27/0.53  % (2681)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.27/0.53  % (2694)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.27/0.53  % (2703)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.27/0.53  % (2696)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.27/0.54  % (2687)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.46/0.54  % (2701)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.46/0.54  % (2698)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.46/0.54  % (2700)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.46/0.54  % (2707)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.46/0.54  % (2686)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.46/0.54  % (2682)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.46/0.54  % (2709)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.46/0.54  % (2689)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.46/0.55  % (2706)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.46/0.55  % (2705)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.46/0.55  % (2697)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.46/0.55  % (2697)Refutation not found, incomplete strategy% (2697)------------------------------
% 1.46/0.55  % (2697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (2697)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (2697)Memory used [KB]: 10618
% 1.46/0.55  % (2697)Time elapsed: 0.151 s
% 1.46/0.55  % (2697)------------------------------
% 1.46/0.55  % (2697)------------------------------
% 1.46/0.55  % (2692)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.46/0.55  % (2708)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.46/0.55  % (2704)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.46/0.57  % (2691)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 2.14/0.65  % (2702)Refutation found. Thanks to Tanya!
% 2.14/0.65  % SZS status Theorem for theBenchmark
% 2.14/0.68  % SZS output start Proof for theBenchmark
% 2.14/0.68  fof(f2187,plain,(
% 2.14/0.68    $false),
% 2.14/0.68    inference(avatar_sat_refutation,[],[f86,f87,f92,f97,f102,f116,f157,f204,f223,f236,f364,f407,f422,f480,f492,f498,f505,f1198,f1205,f2159,f2184,f2186])).
% 2.14/0.68  fof(f2186,plain,(
% 2.14/0.68    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 2.14/0.68    introduced(theory_tautology_sat_conflict,[])).
% 2.14/0.68  fof(f2184,plain,(
% 2.14/0.68    spl2_78 | ~spl2_82),
% 2.14/0.68    inference(avatar_contradiction_clause,[],[f2183])).
% 2.14/0.68  fof(f2183,plain,(
% 2.14/0.68    $false | (spl2_78 | ~spl2_82)),
% 2.14/0.68    inference(subsumption_resolution,[],[f2168,f1204])).
% 2.14/0.68  fof(f1204,plain,(
% 2.14/0.68    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl2_78),
% 2.14/0.68    inference(avatar_component_clause,[],[f1202])).
% 2.14/0.68  fof(f1202,plain,(
% 2.14/0.68    spl2_78 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).
% 2.14/0.68  fof(f2168,plain,(
% 2.14/0.68    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl2_82),
% 2.14/0.68    inference(superposition,[],[f163,f2155])).
% 2.14/0.68  fof(f2155,plain,(
% 2.14/0.68    sK1 = k3_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_82),
% 2.14/0.68    inference(avatar_component_clause,[],[f2153])).
% 2.14/0.68  fof(f2153,plain,(
% 2.14/0.68    spl2_82 <=> sK1 = k3_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).
% 2.14/0.68  fof(f163,plain,(
% 2.14/0.68    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 2.14/0.68    inference(superposition,[],[f149,f60])).
% 2.14/0.68  fof(f60,plain,(
% 2.14/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f1])).
% 2.14/0.68  fof(f1,axiom,(
% 2.14/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.14/0.68  fof(f149,plain,(
% 2.14/0.68    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.14/0.68    inference(superposition,[],[f72,f59])).
% 2.14/0.68  fof(f59,plain,(
% 2.14/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.14/0.68    inference(cnf_transformation,[],[f5])).
% 2.14/0.68  fof(f5,axiom,(
% 2.14/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.14/0.68  fof(f72,plain,(
% 2.14/0.68    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f3])).
% 2.14/0.68  fof(f3,axiom,(
% 2.14/0.68    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.14/0.68  fof(f2159,plain,(
% 2.14/0.68    spl2_82 | ~spl2_3 | ~spl2_4 | ~spl2_37),
% 2.14/0.68    inference(avatar_split_clause,[],[f2158,f460,f94,f89,f2153])).
% 2.14/0.68  fof(f89,plain,(
% 2.14/0.68    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.14/0.68  fof(f94,plain,(
% 2.14/0.68    spl2_4 <=> l1_pre_topc(sK0)),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.14/0.68  fof(f460,plain,(
% 2.14/0.68    spl2_37 <=> sK1 = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 2.14/0.68  fof(f2158,plain,(
% 2.14/0.68    sK1 = k3_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_37)),
% 2.14/0.68    inference(subsumption_resolution,[],[f2157,f96])).
% 2.14/0.68  fof(f96,plain,(
% 2.14/0.68    l1_pre_topc(sK0) | ~spl2_4),
% 2.14/0.68    inference(avatar_component_clause,[],[f94])).
% 2.14/0.68  fof(f2157,plain,(
% 2.14/0.68    sK1 = k3_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_37)),
% 2.14/0.68    inference(subsumption_resolution,[],[f2132,f91])).
% 2.14/0.68  fof(f91,plain,(
% 2.14/0.68    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 2.14/0.68    inference(avatar_component_clause,[],[f89])).
% 2.14/0.68  fof(f2132,plain,(
% 2.14/0.68    sK1 = k3_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_37),
% 2.14/0.68    inference(superposition,[],[f462,f617])).
% 2.14/0.68  % (2713)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.14/0.68  fof(f617,plain,(
% 2.14/0.68    ( ! [X6,X7] : (k3_xboole_0(k2_pre_topc(X6,X7),k1_tops_1(X6,X7)) = k4_xboole_0(k2_pre_topc(X6,X7),k2_tops_1(X6,X7)) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6))) | ~l1_pre_topc(X6)) )),
% 2.14/0.68    inference(superposition,[],[f59,f289])).
% 2.14/0.68  fof(f289,plain,(
% 2.14/0.68    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 2.14/0.68    inference(subsumption_resolution,[],[f287,f66])).
% 2.14/0.68  fof(f66,plain,(
% 2.14/0.68    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f34])).
% 2.14/0.68  fof(f34,plain,(
% 2.14/0.68    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.14/0.68    inference(flattening,[],[f33])).
% 2.14/0.68  fof(f33,plain,(
% 2.14/0.68    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.14/0.68    inference(ennf_transformation,[],[f15])).
% 2.14/0.68  fof(f15,axiom,(
% 2.14/0.68    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.14/0.68  fof(f287,plain,(
% 2.14/0.68    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 2.14/0.68    inference(superposition,[],[f63,f53])).
% 2.14/0.68  fof(f53,plain,(
% 2.14/0.68    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.14/0.68    inference(cnf_transformation,[],[f25])).
% 2.14/0.68  fof(f25,plain,(
% 2.14/0.68    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.14/0.68    inference(ennf_transformation,[],[f9])).
% 2.14/0.68  fof(f9,axiom,(
% 2.14/0.68    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.14/0.68  fof(f63,plain,(
% 2.14/0.68    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f30])).
% 2.14/0.68  fof(f30,plain,(
% 2.14/0.68    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.68    inference(ennf_transformation,[],[f18])).
% 2.14/0.68  fof(f18,axiom,(
% 2.14/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 2.14/0.68  fof(f462,plain,(
% 2.14/0.68    sK1 = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_37),
% 2.14/0.68    inference(avatar_component_clause,[],[f460])).
% 2.14/0.68  fof(f1205,plain,(
% 2.14/0.68    ~spl2_78 | spl2_34 | ~spl2_77),
% 2.14/0.68    inference(avatar_split_clause,[],[f1199,f1195,f404,f1202])).
% 2.14/0.68  fof(f404,plain,(
% 2.14/0.68    spl2_34 <=> sK1 = k1_tops_1(sK0,sK1)),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 2.14/0.68  fof(f1195,plain,(
% 2.14/0.68    spl2_77 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_77])])).
% 2.14/0.68  fof(f1199,plain,(
% 2.14/0.68    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl2_77),
% 2.14/0.68    inference(resolution,[],[f1197,f56])).
% 2.14/0.68  fof(f56,plain,(
% 2.14/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f46])).
% 2.14/0.68  fof(f46,plain,(
% 2.14/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/0.68    inference(flattening,[],[f45])).
% 2.14/0.68  fof(f45,plain,(
% 2.14/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/0.68    inference(nnf_transformation,[],[f2])).
% 2.14/0.68  fof(f2,axiom,(
% 2.14/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.14/0.68  fof(f1197,plain,(
% 2.14/0.68    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_77),
% 2.14/0.68    inference(avatar_component_clause,[],[f1195])).
% 2.14/0.68  fof(f1198,plain,(
% 2.14/0.68    spl2_77 | ~spl2_3 | ~spl2_4),
% 2.14/0.68    inference(avatar_split_clause,[],[f1193,f94,f89,f1195])).
% 2.14/0.68  fof(f1193,plain,(
% 2.14/0.68    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_4)),
% 2.14/0.68    inference(subsumption_resolution,[],[f1184,f96])).
% 2.14/0.68  fof(f1184,plain,(
% 2.14/0.68    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl2_3),
% 2.14/0.68    inference(resolution,[],[f540,f91])).
% 2.14/0.68  fof(f540,plain,(
% 2.14/0.68    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9))) | r1_tarski(k1_tops_1(X9,X8),X8) | ~l1_pre_topc(X9)) )),
% 2.14/0.68    inference(superposition,[],[f72,f245])).
% 2.14/0.68  fof(f245,plain,(
% 2.14/0.68    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.14/0.68    inference(duplicate_literal_removal,[],[f244])).
% 2.14/0.68  fof(f244,plain,(
% 2.14/0.68    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.14/0.68    inference(superposition,[],[f53,f64])).
% 2.14/0.68  fof(f64,plain,(
% 2.14/0.68    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f31])).
% 2.14/0.68  fof(f31,plain,(
% 2.14/0.68    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.68    inference(ennf_transformation,[],[f20])).
% 2.14/0.68  fof(f20,axiom,(
% 2.14/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.14/0.68  fof(f505,plain,(
% 2.14/0.68    spl2_32 | ~spl2_14 | ~spl2_31),
% 2.14/0.68    inference(avatar_split_clause,[],[f504,f352,f184,f356])).
% 2.14/0.68  fof(f356,plain,(
% 2.14/0.68    spl2_32 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 2.14/0.68  fof(f184,plain,(
% 2.14/0.68    spl2_14 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 2.14/0.68  fof(f352,plain,(
% 2.14/0.68    spl2_31 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 2.14/0.68  fof(f504,plain,(
% 2.14/0.68    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | (~spl2_14 | ~spl2_31)),
% 2.14/0.68    inference(subsumption_resolution,[],[f500,f353])).
% 2.14/0.68  fof(f353,plain,(
% 2.14/0.68    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_31),
% 2.14/0.68    inference(avatar_component_clause,[],[f352])).
% 2.14/0.68  fof(f500,plain,(
% 2.14/0.68    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_14),
% 2.14/0.68    inference(superposition,[],[f173,f186])).
% 2.14/0.68  fof(f186,plain,(
% 2.14/0.68    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_14),
% 2.14/0.68    inference(avatar_component_clause,[],[f184])).
% 2.14/0.68  fof(f173,plain,(
% 2.14/0.68    ( ! [X2,X3] : (m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 2.14/0.68    inference(duplicate_literal_removal,[],[f171])).
% 2.14/0.68  fof(f171,plain,(
% 2.14/0.68    ( ! [X2,X3] : (m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 2.14/0.68    inference(superposition,[],[f71,f58])).
% 2.14/0.68  fof(f58,plain,(
% 2.14/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.14/0.68    inference(cnf_transformation,[],[f27])).
% 2.14/0.68  fof(f27,plain,(
% 2.14/0.68    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.14/0.68    inference(ennf_transformation,[],[f6])).
% 2.14/0.68  fof(f6,axiom,(
% 2.14/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.14/0.68  fof(f71,plain,(
% 2.14/0.68    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.14/0.68    inference(cnf_transformation,[],[f38])).
% 2.14/0.68  fof(f38,plain,(
% 2.14/0.68    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.14/0.68    inference(ennf_transformation,[],[f7])).
% 2.14/0.68  fof(f7,axiom,(
% 2.14/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.14/0.68  fof(f498,plain,(
% 2.14/0.68    spl2_14 | ~spl2_2 | ~spl2_13),
% 2.14/0.68    inference(avatar_split_clause,[],[f497,f180,f83,f184])).
% 2.14/0.68  fof(f83,plain,(
% 2.14/0.68    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.14/0.68  fof(f180,plain,(
% 2.14/0.68    spl2_13 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 2.14/0.68  fof(f497,plain,(
% 2.14/0.68    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl2_2 | ~spl2_13)),
% 2.14/0.68    inference(subsumption_resolution,[],[f494,f181])).
% 2.14/0.68  fof(f181,plain,(
% 2.14/0.68    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_13),
% 2.14/0.68    inference(avatar_component_clause,[],[f180])).
% 2.14/0.68  fof(f494,plain,(
% 2.14/0.68    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 2.14/0.68    inference(superposition,[],[f53,f84])).
% 2.14/0.68  fof(f84,plain,(
% 2.14/0.68    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 2.14/0.68    inference(avatar_component_clause,[],[f83])).
% 2.14/0.68  fof(f492,plain,(
% 2.14/0.68    spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_34),
% 2.14/0.68    inference(avatar_contradiction_clause,[],[f491])).
% 2.14/0.68  fof(f491,plain,(
% 2.14/0.68    $false | (spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_34)),
% 2.14/0.68    inference(subsumption_resolution,[],[f490,f96])).
% 2.14/0.68  fof(f490,plain,(
% 2.14/0.68    ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_3 | ~spl2_34)),
% 2.14/0.68    inference(subsumption_resolution,[],[f489,f91])).
% 2.14/0.68  fof(f489,plain,(
% 2.14/0.68    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_34)),
% 2.14/0.68    inference(subsumption_resolution,[],[f486,f85])).
% 2.14/0.68  fof(f85,plain,(
% 2.14/0.68    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl2_2),
% 2.14/0.68    inference(avatar_component_clause,[],[f83])).
% 2.14/0.68  fof(f486,plain,(
% 2.14/0.68    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_34),
% 2.14/0.68    inference(superposition,[],[f63,f406])).
% 2.14/0.68  fof(f406,plain,(
% 2.14/0.68    sK1 = k1_tops_1(sK0,sK1) | ~spl2_34),
% 2.14/0.68    inference(avatar_component_clause,[],[f404])).
% 2.14/0.68  fof(f480,plain,(
% 2.14/0.68    ~spl2_32 | spl2_37 | ~spl2_33),
% 2.14/0.68    inference(avatar_split_clause,[],[f451,f393,f460,f356])).
% 2.14/0.68  fof(f393,plain,(
% 2.14/0.68    spl2_33 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 2.14/0.68  fof(f451,plain,(
% 2.14/0.68    sK1 = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_33),
% 2.14/0.68    inference(superposition,[],[f395,f58])).
% 2.14/0.68  fof(f395,plain,(
% 2.14/0.68    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_33),
% 2.14/0.68    inference(avatar_component_clause,[],[f393])).
% 2.14/0.68  fof(f422,plain,(
% 2.14/0.68    spl2_33 | ~spl2_14 | ~spl2_31),
% 2.14/0.68    inference(avatar_split_clause,[],[f421,f352,f184,f393])).
% 2.14/0.68  fof(f421,plain,(
% 2.14/0.68    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_14 | ~spl2_31)),
% 2.14/0.68    inference(subsumption_resolution,[],[f416,f353])).
% 2.14/0.68  fof(f416,plain,(
% 2.14/0.68    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_14),
% 2.14/0.68    inference(superposition,[],[f174,f186])).
% 2.14/0.68  fof(f174,plain,(
% 2.14/0.68    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.14/0.68    inference(duplicate_literal_removal,[],[f170])).
% 2.14/0.68  fof(f170,plain,(
% 2.14/0.68    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.14/0.68    inference(superposition,[],[f57,f58])).
% 2.14/0.68  fof(f57,plain,(
% 2.14/0.68    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.14/0.68    inference(cnf_transformation,[],[f26])).
% 2.14/0.68  fof(f26,plain,(
% 2.14/0.68    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.14/0.68    inference(ennf_transformation,[],[f8])).
% 2.14/0.68  fof(f8,axiom,(
% 2.14/0.68    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.14/0.68  fof(f407,plain,(
% 2.14/0.68    ~spl2_1 | spl2_34 | ~spl2_3 | ~spl2_4 | ~spl2_9),
% 2.14/0.68    inference(avatar_split_clause,[],[f402,f114,f94,f89,f404,f79])).
% 2.14/0.68  fof(f79,plain,(
% 2.14/0.68    spl2_1 <=> v3_pre_topc(sK1,sK0)),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.14/0.68  fof(f114,plain,(
% 2.14/0.68    spl2_9 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 2.14/0.68  fof(f402,plain,(
% 2.14/0.68    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_4 | ~spl2_9)),
% 2.14/0.68    inference(subsumption_resolution,[],[f241,f96])).
% 2.14/0.68  fof(f241,plain,(
% 2.14/0.68    ~l1_pre_topc(sK0) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_9)),
% 2.14/0.68    inference(resolution,[],[f115,f91])).
% 2.14/0.68  fof(f115,plain,(
% 2.14/0.68    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1)) ) | ~spl2_9),
% 2.14/0.68    inference(avatar_component_clause,[],[f114])).
% 2.14/0.68  fof(f364,plain,(
% 2.14/0.68    ~spl2_16 | spl2_31),
% 2.14/0.68    inference(avatar_contradiction_clause,[],[f363])).
% 2.14/0.68  fof(f363,plain,(
% 2.14/0.68    $false | (~spl2_16 | spl2_31)),
% 2.14/0.68    inference(subsumption_resolution,[],[f361,f203])).
% 2.14/0.68  fof(f203,plain,(
% 2.14/0.68    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_16),
% 2.14/0.68    inference(avatar_component_clause,[],[f201])).
% 2.14/0.68  fof(f201,plain,(
% 2.14/0.68    spl2_16 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 2.14/0.68  fof(f361,plain,(
% 2.14/0.68    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl2_31),
% 2.14/0.68    inference(resolution,[],[f354,f70])).
% 2.14/0.68  fof(f70,plain,(
% 2.14/0.68    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f47])).
% 2.14/0.68  fof(f47,plain,(
% 2.14/0.68    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.14/0.68    inference(nnf_transformation,[],[f13])).
% 2.14/0.68  fof(f13,axiom,(
% 2.14/0.68    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.14/0.68  fof(f354,plain,(
% 2.14/0.68    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl2_31),
% 2.14/0.68    inference(avatar_component_clause,[],[f352])).
% 2.14/0.68  fof(f236,plain,(
% 2.14/0.68    spl2_19 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 2.14/0.68    inference(avatar_split_clause,[],[f231,f99,f94,f89,f233])).
% 2.14/0.68  fof(f233,plain,(
% 2.14/0.68    spl2_19 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 2.14/0.68  fof(f99,plain,(
% 2.14/0.68    spl2_5 <=> v2_pre_topc(sK0)),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.14/0.68  fof(f231,plain,(
% 2.14/0.68    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 2.14/0.68    inference(subsumption_resolution,[],[f230,f101])).
% 2.14/0.68  fof(f101,plain,(
% 2.14/0.68    v2_pre_topc(sK0) | ~spl2_5),
% 2.14/0.68    inference(avatar_component_clause,[],[f99])).
% 2.14/0.68  fof(f230,plain,(
% 2.14/0.68    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl2_3 | ~spl2_4)),
% 2.14/0.68    inference(subsumption_resolution,[],[f228,f96])).
% 2.14/0.68  fof(f228,plain,(
% 2.14/0.68    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_3),
% 2.14/0.68    inference(resolution,[],[f68,f91])).
% 2.14/0.68  fof(f68,plain,(
% 2.14/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f37])).
% 2.14/0.68  fof(f37,plain,(
% 2.14/0.68    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.14/0.68    inference(flattening,[],[f36])).
% 2.14/0.68  fof(f36,plain,(
% 2.14/0.68    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.14/0.68    inference(ennf_transformation,[],[f17])).
% 2.14/0.68  fof(f17,axiom,(
% 2.14/0.68    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.14/0.68  fof(f223,plain,(
% 2.14/0.68    ~spl2_3 | ~spl2_4 | spl2_13),
% 2.14/0.68    inference(avatar_contradiction_clause,[],[f222])).
% 2.14/0.68  fof(f222,plain,(
% 2.14/0.68    $false | (~spl2_3 | ~spl2_4 | spl2_13)),
% 2.14/0.68    inference(subsumption_resolution,[],[f221,f96])).
% 2.14/0.68  fof(f221,plain,(
% 2.14/0.68    ~l1_pre_topc(sK0) | (~spl2_3 | spl2_13)),
% 2.14/0.68    inference(subsumption_resolution,[],[f216,f91])).
% 2.14/0.68  fof(f216,plain,(
% 2.14/0.68    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_13),
% 2.14/0.68    inference(resolution,[],[f66,f182])).
% 2.14/0.68  fof(f182,plain,(
% 2.14/0.68    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_13),
% 2.14/0.68    inference(avatar_component_clause,[],[f180])).
% 2.14/0.68  fof(f204,plain,(
% 2.14/0.68    spl2_16 | ~spl2_3 | ~spl2_4),
% 2.14/0.68    inference(avatar_split_clause,[],[f199,f94,f89,f201])).
% 2.14/0.68  fof(f199,plain,(
% 2.14/0.68    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 2.14/0.68    inference(subsumption_resolution,[],[f198,f96])).
% 2.14/0.68  fof(f198,plain,(
% 2.14/0.68    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl2_3),
% 2.14/0.68    inference(resolution,[],[f67,f91])).
% 2.14/0.68  fof(f67,plain,(
% 2.14/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f35])).
% 2.14/0.68  fof(f35,plain,(
% 2.14/0.68    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.68    inference(ennf_transformation,[],[f16])).
% 2.14/0.68  fof(f16,axiom,(
% 2.14/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 2.14/0.68  fof(f157,plain,(
% 2.14/0.68    ~spl2_4 | ~spl2_5 | ~spl2_8),
% 2.14/0.68    inference(avatar_contradiction_clause,[],[f152])).
% 2.14/0.68  fof(f152,plain,(
% 2.14/0.68    $false | (~spl2_4 | ~spl2_5 | ~spl2_8)),
% 2.14/0.68    inference(unit_resulting_resolution,[],[f96,f101,f75,f112])).
% 2.14/0.68  fof(f112,plain,(
% 2.14/0.68    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl2_8),
% 2.14/0.68    inference(avatar_component_clause,[],[f111])).
% 2.14/0.68  fof(f111,plain,(
% 2.14/0.68    spl2_8 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 2.14/0.68  fof(f75,plain,(
% 2.14/0.68    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.14/0.68    inference(cnf_transformation,[],[f12])).
% 2.14/0.68  fof(f12,axiom,(
% 2.14/0.68    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.14/0.68  fof(f116,plain,(
% 2.14/0.68    spl2_8 | spl2_9),
% 2.14/0.68    inference(avatar_split_clause,[],[f61,f114,f111])).
% 2.14/0.68  fof(f61,plain,(
% 2.14/0.68    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f29])).
% 2.14/0.68  fof(f29,plain,(
% 2.14/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.14/0.68    inference(flattening,[],[f28])).
% 2.14/0.68  fof(f28,plain,(
% 2.14/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.14/0.68    inference(ennf_transformation,[],[f19])).
% 2.14/0.68  fof(f19,axiom,(
% 2.14/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 2.14/0.68  fof(f102,plain,(
% 2.14/0.68    spl2_5),
% 2.14/0.68    inference(avatar_split_clause,[],[f48,f99])).
% 2.14/0.68  fof(f48,plain,(
% 2.14/0.68    v2_pre_topc(sK0)),
% 2.14/0.68    inference(cnf_transformation,[],[f44])).
% 2.14/0.68  fof(f44,plain,(
% 2.14/0.68    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.14/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 2.14/0.68  fof(f42,plain,(
% 2.14/0.68    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.14/0.68    introduced(choice_axiom,[])).
% 2.14/0.68  fof(f43,plain,(
% 2.14/0.68    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.14/0.68    introduced(choice_axiom,[])).
% 2.14/0.68  fof(f41,plain,(
% 2.14/0.68    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.14/0.68    inference(flattening,[],[f40])).
% 2.14/0.68  fof(f40,plain,(
% 2.14/0.68    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.14/0.68    inference(nnf_transformation,[],[f24])).
% 2.14/0.68  fof(f24,plain,(
% 2.14/0.68    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.14/0.68    inference(flattening,[],[f23])).
% 2.14/0.68  fof(f23,plain,(
% 2.14/0.68    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.14/0.68    inference(ennf_transformation,[],[f22])).
% 2.14/0.68  fof(f22,negated_conjecture,(
% 2.14/0.68    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.14/0.68    inference(negated_conjecture,[],[f21])).
% 2.14/0.68  fof(f21,conjecture,(
% 2.14/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 2.14/0.68  fof(f97,plain,(
% 2.14/0.68    spl2_4),
% 2.14/0.68    inference(avatar_split_clause,[],[f49,f94])).
% 2.14/0.68  fof(f49,plain,(
% 2.14/0.68    l1_pre_topc(sK0)),
% 2.14/0.68    inference(cnf_transformation,[],[f44])).
% 2.14/0.68  fof(f92,plain,(
% 2.14/0.68    spl2_3),
% 2.14/0.68    inference(avatar_split_clause,[],[f50,f89])).
% 2.14/0.68  fof(f50,plain,(
% 2.14/0.68    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.14/0.68    inference(cnf_transformation,[],[f44])).
% 2.14/0.68  fof(f87,plain,(
% 2.14/0.68    spl2_1 | spl2_2),
% 2.14/0.68    inference(avatar_split_clause,[],[f51,f83,f79])).
% 2.14/0.68  fof(f51,plain,(
% 2.14/0.68    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 2.14/0.68    inference(cnf_transformation,[],[f44])).
% 2.14/0.68  fof(f86,plain,(
% 2.14/0.68    ~spl2_1 | ~spl2_2),
% 2.14/0.68    inference(avatar_split_clause,[],[f52,f83,f79])).
% 2.14/0.68  fof(f52,plain,(
% 2.14/0.68    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.14/0.68    inference(cnf_transformation,[],[f44])).
% 2.14/0.68  % SZS output end Proof for theBenchmark
% 2.14/0.68  % (2702)------------------------------
% 2.14/0.68  % (2702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.68  % (2702)Termination reason: Refutation
% 2.14/0.68  
% 2.14/0.68  % (2702)Memory used [KB]: 7547
% 2.14/0.68  % (2702)Time elapsed: 0.253 s
% 2.14/0.68  % (2702)------------------------------
% 2.14/0.68  % (2702)------------------------------
% 2.14/0.69  % (2679)Success in time 0.332 s
%------------------------------------------------------------------------------
