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
% DateTime   : Thu Dec  3 13:12:21 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 398 expanded)
%              Number of leaves         :   39 ( 171 expanded)
%              Depth                    :   12
%              Number of atoms          :  502 (1421 expanded)
%              Number of equality atoms :   70 ( 178 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f628,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f90,f95,f103,f112,f120,f125,f130,f148,f166,f207,f243,f275,f292,f293,f338,f493,f584,f627])).

fof(f627,plain,
    ( ~ spl3_13
    | spl3_38 ),
    inference(avatar_contradiction_clause,[],[f622])).

fof(f622,plain,
    ( $false
    | ~ spl3_13
    | spl3_38 ),
    inference(unit_resulting_resolution,[],[f251,f581,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f581,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_38 ),
    inference(avatar_component_clause,[],[f579])).

fof(f579,plain,
    ( spl3_38
  <=> m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

% (10614)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% (10616)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f251,plain,
    ( ! [X0] : r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f237,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f237,plain,
    ( ! [X0] : m1_subset_1(k1_setfam_1(k2_tarski(X0,sK2)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f173,f185])).

fof(f185,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f129,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f52,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f129,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl3_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f173,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(k2_struct_0(sK0),X0,sK2),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f129,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f584,plain,
    ( ~ spl3_7
    | spl3_20
    | ~ spl3_38
    | ~ spl3_10
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f583,f490,f108,f579,f240,f87])).

fof(f87,plain,
    ( spl3_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f240,plain,
    ( spl3_20
  <=> v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f108,plain,
    ( spl3_10
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f490,plain,
    ( spl3_33
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f583,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f576,f110])).

fof(f110,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f576,plain,
    ( v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_33 ),
    inference(trivial_inequality_removal,[],[f575])).

fof(f575,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_33 ),
    inference(superposition,[],[f45,f492])).

fof(f492,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f490])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f493,plain,
    ( spl3_33
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_18
    | ~ spl3_22
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f488,f331,f288,f283,f264,f205,f127,f122,f62,f490])).

fof(f62,plain,
    ( spl3_2
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f122,plain,
    ( spl3_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f205,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f264,plain,
    ( spl3_22
  <=> k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f283,plain,
    ( spl3_23
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f288,plain,
    ( spl3_24
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f331,plain,
    ( spl3_26
  <=> sK2 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f488,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_18
    | ~ spl3_22
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f487,f285])).

fof(f285,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK2)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f283])).

fof(f487,plain,
    ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_pre_topc(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_18
    | ~ spl3_22
    | ~ spl3_24
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f486,f333])).

fof(f333,plain,
    ( sK2 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK2))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f331])).

fof(f486,plain,
    ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK2)))
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_18
    | ~ spl3_22
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f485,f290])).

fof(f290,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f288])).

fof(f485,plain,
    ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),sK2)))
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_18
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f484,f270])).

fof(f270,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),sK2,X0) = k1_setfam_1(k2_tarski(X0,sK2))
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f177,f185])).

fof(f177,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK2) = k9_subset_1(k2_struct_0(sK0),sK2,X0)
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f129,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f484,plain,
    ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1)))
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_18
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f483,f266])).

fof(f266,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f264])).

fof(f483,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1)))
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f470,f184])).

fof(f184,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f124,f55])).

fof(f124,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f122])).

fof(f470,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f64,f129,f124,f206])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f205])).

fof(f64,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f338,plain,
    ( spl3_26
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f337,f162,f127,f331])).

fof(f162,plain,
    ( spl3_17
  <=> sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f337,plain,
    ( sK2 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK2))
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f321,f164])).

fof(f164,plain,
    ( sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f162])).

fof(f321,plain,
    ( k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK2))
    | ~ spl3_13 ),
    inference(superposition,[],[f270,f183])).

fof(f183,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f104,f55])).

fof(f104,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f41,f40])).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f293,plain,
    ( spl3_24
    | ~ spl3_12
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f281,f108,f87,f72,f122,f288])).

fof(f72,plain,
    ( spl3_4
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f281,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(resolution,[],[f192,f74])).

fof(f74,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f192,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) )
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f191,f110])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) )
    | ~ spl3_7 ),
    inference(resolution,[],[f44,f89])).

fof(f89,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f292,plain,
    ( spl3_23
    | ~ spl3_13
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f280,f108,f87,f67,f127,f283])).

fof(f67,plain,
    ( spl3_3
  <=> v1_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f280,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK2)
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(resolution,[],[f192,f69])).

fof(f69,plain,
    ( v1_tops_1(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f275,plain,
    ( spl3_22
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f272,f127,f122,f264])).

fof(f272,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1))
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(superposition,[],[f184,f270])).

fof(f243,plain,
    ( ~ spl3_20
    | spl3_11
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f236,f127,f117,f240])).

fof(f117,plain,
    ( spl3_11
  <=> v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f236,plain,
    ( ~ v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | spl3_11
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f119,f185])).

fof(f119,plain,
    ( ~ v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f207,plain,
    ( ~ spl3_7
    | spl3_18
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f203,f108,f92,f205,f87])).

fof(f92,plain,
    ( spl3_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f202,f110])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f201,f110])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f200,f110])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl3_8 ),
    inference(resolution,[],[f46,f94])).

fof(f94,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).

fof(f166,plain,
    ( spl3_17
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f154,f138,f162])).

fof(f138,plain,
    ( spl3_14
  <=> r1_tarski(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f154,plain,
    ( sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))
    | ~ spl3_14 ),
    inference(resolution,[],[f54,f140])).

fof(f140,plain,
    ( r1_tarski(sK2,k2_struct_0(sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f138])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f48,f47])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f148,plain,
    ( spl3_14
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f136,f127,f138])).

fof(f136,plain,
    ( r1_tarski(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f49,f129])).

fof(f130,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f115,f108,f77,f127])).

fof(f77,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f115,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f79,f110])).

fof(f79,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f125,plain,
    ( spl3_12
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f114,f108,f82,f122])).

fof(f82,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f114,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f84,f110])).

fof(f84,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f120,plain,
    ( ~ spl3_11
    | spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f113,f108,f57,f117])).

fof(f57,plain,
    ( spl3_1
  <=> v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f113,plain,
    ( ~ v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0)
    | spl3_1
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f59,f110])).

fof(f59,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f112,plain,
    ( spl3_10
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f106,f99,f108])).

fof(f99,plain,
    ( spl3_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f106,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(resolution,[],[f42,f101])).

fof(f101,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f42,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f103,plain,
    ( spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f97,f87,f99])).

fof(f97,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f43,f89])).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f95,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f32,f92])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_pre_topc(sK2,sK0)
    & v1_tops_1(sK2,sK0)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_pre_topc(X2,X0)
                & v1_tops_1(X2,X0)
                & v1_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v3_pre_topc(X2,sK0)
              & v1_tops_1(X2,sK0)
              & v1_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v3_pre_topc(X2,sK0)
            & v1_tops_1(X2,sK0)
            & v1_tops_1(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v3_pre_topc(X2,sK0)
          & v1_tops_1(X2,sK0)
          & v1_tops_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v3_pre_topc(X2,sK0)
        & v1_tops_1(X2,sK0)
        & v1_tops_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v3_pre_topc(sK2,sK0)
      & v1_tops_1(sK2,sK0)
      & v1_tops_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v1_tops_1(X2,X0)
                    & v1_tops_1(X1,X0) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X2,X0)
                  & v1_tops_1(X2,X0)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).

fof(f90,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f33,f87])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f34,f82])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f35,f77])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f36,f72])).

fof(f36,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f37,f67])).

fof(f37,plain,(
    v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f38,f62])).

fof(f38,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f39,f57])).

fof(f39,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:54:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (10613)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.44  % (10609)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (10603)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (10604)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (10610)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (10605)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (10611)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (10615)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (10607)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (10606)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (10612)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (10602)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (10617)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.26/0.52  % (10608)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.26/0.52  % (10619)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.26/0.52  % (10618)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.26/0.52  % (10608)Refutation found. Thanks to Tanya!
% 1.26/0.52  % SZS status Theorem for theBenchmark
% 1.26/0.52  % SZS output start Proof for theBenchmark
% 1.26/0.52  fof(f628,plain,(
% 1.26/0.52    $false),
% 1.26/0.52    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f90,f95,f103,f112,f120,f125,f130,f148,f166,f207,f243,f275,f292,f293,f338,f493,f584,f627])).
% 1.26/0.52  fof(f627,plain,(
% 1.26/0.52    ~spl3_13 | spl3_38),
% 1.26/0.52    inference(avatar_contradiction_clause,[],[f622])).
% 1.26/0.52  fof(f622,plain,(
% 1.26/0.52    $false | (~spl3_13 | spl3_38)),
% 1.26/0.52    inference(unit_resulting_resolution,[],[f251,f581,f50])).
% 1.26/0.52  fof(f50,plain,(
% 1.26/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f31])).
% 1.26/0.52  fof(f31,plain,(
% 1.26/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.26/0.52    inference(nnf_transformation,[],[f8])).
% 1.26/0.52  fof(f8,axiom,(
% 1.26/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.26/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.26/0.52  fof(f581,plain,(
% 1.26/0.52    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_38),
% 1.26/0.52    inference(avatar_component_clause,[],[f579])).
% 1.26/0.52  fof(f579,plain,(
% 1.26/0.52    spl3_38 <=> m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 1.26/0.52  % (10614)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 1.26/0.53  % (10616)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.41/0.54  fof(f251,plain,(
% 1.41/0.54    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_tarski(X0,sK2)),k2_struct_0(sK0))) ) | ~spl3_13),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f237,f49])).
% 1.41/0.54  fof(f49,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f31])).
% 1.41/0.54  fof(f237,plain,(
% 1.41/0.54    ( ! [X0] : (m1_subset_1(k1_setfam_1(k2_tarski(X0,sK2)),k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_13),
% 1.41/0.54    inference(backward_demodulation,[],[f173,f185])).
% 1.41/0.54  fof(f185,plain,(
% 1.41/0.54    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))) ) | ~spl3_13),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f129,f55])).
% 1.41/0.54  fof(f55,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 1.41/0.54    inference(definition_unfolding,[],[f52,f47])).
% 1.41/0.54  fof(f47,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f7])).
% 1.41/0.54  fof(f7,axiom,(
% 1.41/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.41/0.54  fof(f52,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f24])).
% 1.41/0.54  fof(f24,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f6])).
% 1.41/0.54  fof(f6,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.41/0.54  fof(f129,plain,(
% 1.41/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_13),
% 1.41/0.54    inference(avatar_component_clause,[],[f127])).
% 1.41/0.54  fof(f127,plain,(
% 1.41/0.54    spl3_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.41/0.54  fof(f173,plain,(
% 1.41/0.54    ( ! [X0] : (m1_subset_1(k9_subset_1(k2_struct_0(sK0),X0,sK2),k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_13),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f129,f51])).
% 1.41/0.54  fof(f51,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f23])).
% 1.41/0.54  fof(f23,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f5])).
% 1.41/0.54  fof(f5,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 1.41/0.54  fof(f584,plain,(
% 1.41/0.54    ~spl3_7 | spl3_20 | ~spl3_38 | ~spl3_10 | ~spl3_33),
% 1.41/0.54    inference(avatar_split_clause,[],[f583,f490,f108,f579,f240,f87])).
% 1.41/0.54  fof(f87,plain,(
% 1.41/0.54    spl3_7 <=> l1_pre_topc(sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.41/0.54  fof(f240,plain,(
% 1.41/0.54    spl3_20 <=> v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.41/0.54  fof(f108,plain,(
% 1.41/0.54    spl3_10 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.41/0.54  fof(f490,plain,(
% 1.41/0.54    spl3_33 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 1.41/0.54  fof(f583,plain,(
% 1.41/0.54    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | ~l1_pre_topc(sK0) | (~spl3_10 | ~spl3_33)),
% 1.41/0.54    inference(forward_demodulation,[],[f576,f110])).
% 1.41/0.54  fof(f110,plain,(
% 1.41/0.54    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_10),
% 1.41/0.54    inference(avatar_component_clause,[],[f108])).
% 1.41/0.54  fof(f576,plain,(
% 1.41/0.54    v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_33),
% 1.41/0.54    inference(trivial_inequality_removal,[],[f575])).
% 1.41/0.54  fof(f575,plain,(
% 1.41/0.54    k2_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_33),
% 1.41/0.54    inference(superposition,[],[f45,f492])).
% 1.41/0.54  fof(f492,plain,(
% 1.41/0.54    k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) | ~spl3_33),
% 1.41/0.54    inference(avatar_component_clause,[],[f490])).
% 1.41/0.54  fof(f45,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f30])).
% 1.41/0.54  fof(f30,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.54    inference(nnf_transformation,[],[f19])).
% 1.41/0.54  fof(f19,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.54    inference(ennf_transformation,[],[f11])).
% 1.41/0.54  fof(f11,axiom,(
% 1.41/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 1.41/0.54  fof(f493,plain,(
% 1.41/0.54    spl3_33 | ~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_18 | ~spl3_22 | ~spl3_23 | ~spl3_24 | ~spl3_26),
% 1.41/0.54    inference(avatar_split_clause,[],[f488,f331,f288,f283,f264,f205,f127,f122,f62,f490])).
% 1.41/0.54  fof(f62,plain,(
% 1.41/0.54    spl3_2 <=> v3_pre_topc(sK2,sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.41/0.54  fof(f122,plain,(
% 1.41/0.54    spl3_12 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.41/0.54  fof(f205,plain,(
% 1.41/0.54    spl3_18 <=> ! [X1,X0] : (k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.41/0.54  fof(f264,plain,(
% 1.41/0.54    spl3_22 <=> k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.41/0.54  fof(f283,plain,(
% 1.41/0.54    spl3_23 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK2)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.41/0.54  fof(f288,plain,(
% 1.41/0.54    spl3_24 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.41/0.54  fof(f331,plain,(
% 1.41/0.54    spl3_26 <=> sK2 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK2))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.41/0.54  fof(f488,plain,(
% 1.41/0.54    k2_struct_0(sK0) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) | (~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_18 | ~spl3_22 | ~spl3_23 | ~spl3_24 | ~spl3_26)),
% 1.41/0.54    inference(forward_demodulation,[],[f487,f285])).
% 1.41/0.54  fof(f285,plain,(
% 1.41/0.54    k2_struct_0(sK0) = k2_pre_topc(sK0,sK2) | ~spl3_23),
% 1.41/0.54    inference(avatar_component_clause,[],[f283])).
% 1.41/0.54  fof(f487,plain,(
% 1.41/0.54    k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_pre_topc(sK0,sK2) | (~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_18 | ~spl3_22 | ~spl3_24 | ~spl3_26)),
% 1.41/0.54    inference(forward_demodulation,[],[f486,f333])).
% 1.41/0.54  fof(f333,plain,(
% 1.41/0.54    sK2 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK2)) | ~spl3_26),
% 1.41/0.54    inference(avatar_component_clause,[],[f331])).
% 1.41/0.54  fof(f486,plain,(
% 1.41/0.54    k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK2))) | (~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_18 | ~spl3_22 | ~spl3_24)),
% 1.41/0.54    inference(forward_demodulation,[],[f485,f290])).
% 1.41/0.54  fof(f290,plain,(
% 1.41/0.54    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~spl3_24),
% 1.41/0.54    inference(avatar_component_clause,[],[f288])).
% 1.41/0.54  fof(f485,plain,(
% 1.41/0.54    k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),sK2))) | (~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_18 | ~spl3_22)),
% 1.41/0.54    inference(forward_demodulation,[],[f484,f270])).
% 1.41/0.54  fof(f270,plain,(
% 1.41/0.54    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),sK2,X0) = k1_setfam_1(k2_tarski(X0,sK2))) ) | ~spl3_13),
% 1.41/0.54    inference(forward_demodulation,[],[f177,f185])).
% 1.41/0.54  fof(f177,plain,(
% 1.41/0.54    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,sK2) = k9_subset_1(k2_struct_0(sK0),sK2,X0)) ) | ~spl3_13),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f129,f53])).
% 1.41/0.54  fof(f53,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f25])).
% 1.41/0.54  fof(f25,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f2])).
% 1.41/0.54  fof(f2,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 1.41/0.54  fof(f484,plain,(
% 1.41/0.54    k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1))) | (~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_18 | ~spl3_22)),
% 1.41/0.54    inference(forward_demodulation,[],[f483,f266])).
% 1.41/0.54  fof(f266,plain,(
% 1.41/0.54    k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1)) | ~spl3_22),
% 1.41/0.54    inference(avatar_component_clause,[],[f264])).
% 1.41/0.54  fof(f483,plain,(
% 1.41/0.54    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,sK1))) | (~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_18)),
% 1.41/0.54    inference(forward_demodulation,[],[f470,f184])).
% 1.41/0.54  fof(f184,plain,(
% 1.41/0.54    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))) ) | ~spl3_12),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f124,f55])).
% 1.41/0.54  fof(f124,plain,(
% 1.41/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_12),
% 1.41/0.54    inference(avatar_component_clause,[],[f122])).
% 1.41/0.54  fof(f470,plain,(
% 1.41/0.54    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) | (~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_18)),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f64,f129,f124,f206])).
% 1.41/0.54  fof(f206,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl3_18),
% 1.41/0.54    inference(avatar_component_clause,[],[f205])).
% 1.41/0.54  fof(f64,plain,(
% 1.41/0.54    v3_pre_topc(sK2,sK0) | ~spl3_2),
% 1.41/0.54    inference(avatar_component_clause,[],[f62])).
% 1.41/0.54  fof(f338,plain,(
% 1.41/0.54    spl3_26 | ~spl3_13 | ~spl3_17),
% 1.41/0.54    inference(avatar_split_clause,[],[f337,f162,f127,f331])).
% 1.41/0.54  fof(f162,plain,(
% 1.41/0.54    spl3_17 <=> sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.41/0.54  fof(f337,plain,(
% 1.41/0.54    sK2 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK2)) | (~spl3_13 | ~spl3_17)),
% 1.41/0.54    inference(forward_demodulation,[],[f321,f164])).
% 1.41/0.54  fof(f164,plain,(
% 1.41/0.54    sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) | ~spl3_17),
% 1.41/0.54    inference(avatar_component_clause,[],[f162])).
% 1.41/0.54  fof(f321,plain,(
% 1.41/0.54    k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK2)) | ~spl3_13),
% 1.41/0.54    inference(superposition,[],[f270,f183])).
% 1.41/0.54  fof(f183,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f104,f55])).
% 1.41/0.54  fof(f104,plain,(
% 1.41/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.41/0.54    inference(forward_demodulation,[],[f41,f40])).
% 1.41/0.54  fof(f40,plain,(
% 1.41/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.41/0.54    inference(cnf_transformation,[],[f3])).
% 1.41/0.54  fof(f3,axiom,(
% 1.41/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.41/0.54  fof(f41,plain,(
% 1.41/0.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f4])).
% 1.41/0.54  fof(f4,axiom,(
% 1.41/0.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.41/0.54  fof(f293,plain,(
% 1.41/0.54    spl3_24 | ~spl3_12 | ~spl3_4 | ~spl3_7 | ~spl3_10),
% 1.41/0.54    inference(avatar_split_clause,[],[f281,f108,f87,f72,f122,f288])).
% 1.41/0.54  fof(f72,plain,(
% 1.41/0.54    spl3_4 <=> v1_tops_1(sK1,sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.41/0.54  fof(f281,plain,(
% 1.41/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | (~spl3_4 | ~spl3_7 | ~spl3_10)),
% 1.41/0.54    inference(resolution,[],[f192,f74])).
% 1.41/0.54  fof(f74,plain,(
% 1.41/0.54    v1_tops_1(sK1,sK0) | ~spl3_4),
% 1.41/0.54    inference(avatar_component_clause,[],[f72])).
% 1.41/0.54  fof(f192,plain,(
% 1.41/0.54    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) ) | (~spl3_7 | ~spl3_10)),
% 1.41/0.54    inference(forward_demodulation,[],[f191,f110])).
% 1.41/0.54  fof(f191,plain,(
% 1.41/0.54    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) ) | ~spl3_7),
% 1.41/0.54    inference(resolution,[],[f44,f89])).
% 1.41/0.54  fof(f89,plain,(
% 1.41/0.54    l1_pre_topc(sK0) | ~spl3_7),
% 1.41/0.54    inference(avatar_component_clause,[],[f87])).
% 1.41/0.54  fof(f44,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f30])).
% 1.41/0.54  fof(f292,plain,(
% 1.41/0.54    spl3_23 | ~spl3_13 | ~spl3_3 | ~spl3_7 | ~spl3_10),
% 1.41/0.54    inference(avatar_split_clause,[],[f280,f108,f87,f67,f127,f283])).
% 1.41/0.54  fof(f67,plain,(
% 1.41/0.54    spl3_3 <=> v1_tops_1(sK2,sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.41/0.54  fof(f280,plain,(
% 1.41/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK2) | (~spl3_3 | ~spl3_7 | ~spl3_10)),
% 1.41/0.54    inference(resolution,[],[f192,f69])).
% 1.41/0.54  fof(f69,plain,(
% 1.41/0.54    v1_tops_1(sK2,sK0) | ~spl3_3),
% 1.41/0.54    inference(avatar_component_clause,[],[f67])).
% 1.41/0.54  fof(f275,plain,(
% 1.41/0.54    spl3_22 | ~spl3_12 | ~spl3_13),
% 1.41/0.54    inference(avatar_split_clause,[],[f272,f127,f122,f264])).
% 1.41/0.54  fof(f272,plain,(
% 1.41/0.54    k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1)) | (~spl3_12 | ~spl3_13)),
% 1.41/0.54    inference(superposition,[],[f184,f270])).
% 1.41/0.54  fof(f243,plain,(
% 1.41/0.54    ~spl3_20 | spl3_11 | ~spl3_13),
% 1.41/0.54    inference(avatar_split_clause,[],[f236,f127,f117,f240])).
% 1.41/0.54  fof(f117,plain,(
% 1.41/0.54    spl3_11 <=> v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.41/0.54  fof(f236,plain,(
% 1.41/0.54    ~v1_tops_1(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | (spl3_11 | ~spl3_13)),
% 1.41/0.54    inference(backward_demodulation,[],[f119,f185])).
% 1.41/0.54  fof(f119,plain,(
% 1.41/0.54    ~v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0) | spl3_11),
% 1.41/0.54    inference(avatar_component_clause,[],[f117])).
% 1.41/0.54  fof(f207,plain,(
% 1.41/0.54    ~spl3_7 | spl3_18 | ~spl3_8 | ~spl3_10),
% 1.41/0.54    inference(avatar_split_clause,[],[f203,f108,f92,f205,f87])).
% 1.41/0.54  fof(f92,plain,(
% 1.41/0.54    spl3_8 <=> v2_pre_topc(sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.41/0.54  fof(f203,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | (~spl3_8 | ~spl3_10)),
% 1.41/0.54    inference(forward_demodulation,[],[f202,f110])).
% 1.41/0.54  fof(f202,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | (~spl3_8 | ~spl3_10)),
% 1.41/0.54    inference(forward_demodulation,[],[f201,f110])).
% 1.41/0.54  fof(f201,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | (~spl3_8 | ~spl3_10)),
% 1.41/0.54    inference(forward_demodulation,[],[f200,f110])).
% 1.41/0.54  fof(f200,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | ~spl3_8),
% 1.41/0.54    inference(resolution,[],[f46,f94])).
% 1.41/0.54  fof(f94,plain,(
% 1.41/0.54    v2_pre_topc(sK0) | ~spl3_8),
% 1.41/0.54    inference(avatar_component_clause,[],[f92])).
% 1.41/0.54  fof(f46,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f21])).
% 1.41/0.54  fof(f21,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.41/0.54    inference(flattening,[],[f20])).
% 1.41/0.54  fof(f20,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f12])).
% 1.41/0.54  fof(f12,axiom,(
% 1.41/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))))))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).
% 1.41/0.54  fof(f166,plain,(
% 1.41/0.54    spl3_17 | ~spl3_14),
% 1.41/0.54    inference(avatar_split_clause,[],[f154,f138,f162])).
% 1.41/0.54  fof(f138,plain,(
% 1.41/0.54    spl3_14 <=> r1_tarski(sK2,k2_struct_0(sK0))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.41/0.54  fof(f154,plain,(
% 1.41/0.54    sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) | ~spl3_14),
% 1.41/0.54    inference(resolution,[],[f54,f140])).
% 1.41/0.54  fof(f140,plain,(
% 1.41/0.54    r1_tarski(sK2,k2_struct_0(sK0)) | ~spl3_14),
% 1.41/0.54    inference(avatar_component_clause,[],[f138])).
% 1.41/0.54  fof(f54,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 1.41/0.54    inference(definition_unfolding,[],[f48,f47])).
% 1.41/0.54  fof(f48,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f22])).
% 1.41/0.54  fof(f22,plain,(
% 1.41/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.41/0.54    inference(ennf_transformation,[],[f1])).
% 1.41/0.54  fof(f1,axiom,(
% 1.41/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.41/0.54  fof(f148,plain,(
% 1.41/0.54    spl3_14 | ~spl3_13),
% 1.41/0.54    inference(avatar_split_clause,[],[f136,f127,f138])).
% 1.41/0.54  fof(f136,plain,(
% 1.41/0.54    r1_tarski(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 1.41/0.54    inference(resolution,[],[f49,f129])).
% 1.41/0.54  fof(f130,plain,(
% 1.41/0.54    spl3_13 | ~spl3_5 | ~spl3_10),
% 1.41/0.54    inference(avatar_split_clause,[],[f115,f108,f77,f127])).
% 1.41/0.54  fof(f77,plain,(
% 1.41/0.54    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.41/0.54  fof(f115,plain,(
% 1.41/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_5 | ~spl3_10)),
% 1.41/0.54    inference(backward_demodulation,[],[f79,f110])).
% 1.41/0.54  fof(f79,plain,(
% 1.41/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 1.41/0.54    inference(avatar_component_clause,[],[f77])).
% 1.41/0.54  fof(f125,plain,(
% 1.41/0.54    spl3_12 | ~spl3_6 | ~spl3_10),
% 1.41/0.54    inference(avatar_split_clause,[],[f114,f108,f82,f122])).
% 1.41/0.54  fof(f82,plain,(
% 1.41/0.54    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.41/0.54  fof(f114,plain,(
% 1.41/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_6 | ~spl3_10)),
% 1.41/0.54    inference(backward_demodulation,[],[f84,f110])).
% 1.41/0.54  fof(f84,plain,(
% 1.41/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 1.41/0.54    inference(avatar_component_clause,[],[f82])).
% 1.41/0.54  fof(f120,plain,(
% 1.41/0.54    ~spl3_11 | spl3_1 | ~spl3_10),
% 1.41/0.54    inference(avatar_split_clause,[],[f113,f108,f57,f117])).
% 1.41/0.54  fof(f57,plain,(
% 1.41/0.54    spl3_1 <=> v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.41/0.54  fof(f113,plain,(
% 1.41/0.54    ~v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0) | (spl3_1 | ~spl3_10)),
% 1.41/0.54    inference(backward_demodulation,[],[f59,f110])).
% 1.41/0.54  fof(f59,plain,(
% 1.41/0.54    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_1),
% 1.41/0.54    inference(avatar_component_clause,[],[f57])).
% 1.41/0.54  fof(f112,plain,(
% 1.41/0.54    spl3_10 | ~spl3_9),
% 1.41/0.54    inference(avatar_split_clause,[],[f106,f99,f108])).
% 1.41/0.54  fof(f99,plain,(
% 1.41/0.54    spl3_9 <=> l1_struct_0(sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.41/0.54  fof(f106,plain,(
% 1.41/0.54    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 1.41/0.54    inference(resolution,[],[f42,f101])).
% 1.41/0.54  fof(f101,plain,(
% 1.41/0.54    l1_struct_0(sK0) | ~spl3_9),
% 1.41/0.54    inference(avatar_component_clause,[],[f99])).
% 1.41/0.54  fof(f42,plain,(
% 1.41/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f17])).
% 1.41/0.54  fof(f17,plain,(
% 1.41/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.41/0.54    inference(ennf_transformation,[],[f9])).
% 1.41/0.54  fof(f9,axiom,(
% 1.41/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.41/0.54  fof(f103,plain,(
% 1.41/0.54    spl3_9 | ~spl3_7),
% 1.41/0.54    inference(avatar_split_clause,[],[f97,f87,f99])).
% 1.41/0.54  fof(f97,plain,(
% 1.41/0.54    l1_struct_0(sK0) | ~spl3_7),
% 1.41/0.54    inference(resolution,[],[f43,f89])).
% 1.41/0.54  fof(f43,plain,(
% 1.41/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f18])).
% 1.41/0.54  fof(f18,plain,(
% 1.41/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.41/0.54    inference(ennf_transformation,[],[f10])).
% 1.41/0.54  fof(f10,axiom,(
% 1.41/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.41/0.54  fof(f95,plain,(
% 1.41/0.54    spl3_8),
% 1.41/0.54    inference(avatar_split_clause,[],[f32,f92])).
% 1.41/0.54  fof(f32,plain,(
% 1.41/0.54    v2_pre_topc(sK0)),
% 1.41/0.54    inference(cnf_transformation,[],[f29])).
% 1.41/0.54  fof(f29,plain,(
% 1.41/0.54    ((~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.41/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f28,f27,f26])).
% 1.41/0.54  fof(f26,plain,(
% 1.41/0.54    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f27,plain,(
% 1.41/0.54    ? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f28,plain,(
% 1.41/0.54    ? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f16,plain,(
% 1.41/0.54    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.41/0.54    inference(flattening,[],[f15])).
% 1.41/0.54  fof(f15,plain,(
% 1.41/0.54    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f14])).
% 1.41/0.54  fof(f14,negated_conjecture,(
% 1.41/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.41/0.54    inference(negated_conjecture,[],[f13])).
% 1.41/0.54  fof(f13,conjecture,(
% 1.41/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).
% 1.41/0.54  fof(f90,plain,(
% 1.41/0.54    spl3_7),
% 1.41/0.54    inference(avatar_split_clause,[],[f33,f87])).
% 1.41/0.54  fof(f33,plain,(
% 1.41/0.54    l1_pre_topc(sK0)),
% 1.41/0.54    inference(cnf_transformation,[],[f29])).
% 1.41/0.54  fof(f85,plain,(
% 1.41/0.54    spl3_6),
% 1.41/0.54    inference(avatar_split_clause,[],[f34,f82])).
% 1.41/0.54  fof(f34,plain,(
% 1.41/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.41/0.54    inference(cnf_transformation,[],[f29])).
% 1.41/0.54  fof(f80,plain,(
% 1.41/0.54    spl3_5),
% 1.41/0.54    inference(avatar_split_clause,[],[f35,f77])).
% 1.41/0.54  fof(f35,plain,(
% 1.41/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.41/0.54    inference(cnf_transformation,[],[f29])).
% 1.41/0.54  fof(f75,plain,(
% 1.41/0.54    spl3_4),
% 1.41/0.54    inference(avatar_split_clause,[],[f36,f72])).
% 1.41/0.54  fof(f36,plain,(
% 1.41/0.54    v1_tops_1(sK1,sK0)),
% 1.41/0.54    inference(cnf_transformation,[],[f29])).
% 1.41/0.54  fof(f70,plain,(
% 1.41/0.54    spl3_3),
% 1.41/0.54    inference(avatar_split_clause,[],[f37,f67])).
% 1.41/0.54  fof(f37,plain,(
% 1.41/0.54    v1_tops_1(sK2,sK0)),
% 1.41/0.54    inference(cnf_transformation,[],[f29])).
% 1.41/0.54  fof(f65,plain,(
% 1.41/0.54    spl3_2),
% 1.41/0.54    inference(avatar_split_clause,[],[f38,f62])).
% 1.41/0.54  fof(f38,plain,(
% 1.41/0.54    v3_pre_topc(sK2,sK0)),
% 1.41/0.54    inference(cnf_transformation,[],[f29])).
% 1.41/0.54  fof(f60,plain,(
% 1.41/0.54    ~spl3_1),
% 1.41/0.54    inference(avatar_split_clause,[],[f39,f57])).
% 1.41/0.54  fof(f39,plain,(
% 1.41/0.54    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 1.41/0.54    inference(cnf_transformation,[],[f29])).
% 1.41/0.54  % SZS output end Proof for theBenchmark
% 1.41/0.54  % (10608)------------------------------
% 1.41/0.54  % (10608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (10608)Termination reason: Refutation
% 1.41/0.54  
% 1.41/0.54  % (10608)Memory used [KB]: 6524
% 1.41/0.54  % (10608)Time elapsed: 0.108 s
% 1.41/0.54  % (10608)------------------------------
% 1.41/0.54  % (10608)------------------------------
% 1.41/0.54  % (10601)Success in time 0.181 s
%------------------------------------------------------------------------------
