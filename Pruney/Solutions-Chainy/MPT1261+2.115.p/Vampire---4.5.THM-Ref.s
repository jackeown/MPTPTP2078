%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 271 expanded)
%              Number of leaves         :   39 ( 118 expanded)
%              Depth                    :    9
%              Number of atoms          :  369 ( 823 expanded)
%              Number of equality atoms :  103 ( 219 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1805,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f80,f85,f90,f95,f238,f406,f432,f457,f583,f584,f591,f836,f1577,f1582,f1587,f1703,f1704,f1705,f1789,f1802])).

fof(f1802,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) != k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | sK1 != k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) != k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | k2_pre_topc(sK0,sK1) != k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1789,plain,
    ( spl2_195
    | ~ spl2_173
    | ~ spl2_188 ),
    inference(avatar_split_clause,[],[f1722,f1700,f1579,f1786])).

fof(f1786,plain,
    ( spl2_195
  <=> k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_195])])).

fof(f1579,plain,
    ( spl2_173
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_173])])).

fof(f1700,plain,
    ( spl2_188
  <=> m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_188])])).

fof(f1722,plain,
    ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_173
    | ~ spl2_188 ),
    inference(unit_resulting_resolution,[],[f1581,f1702,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f1702,plain,
    ( m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl2_188 ),
    inference(avatar_component_clause,[],[f1700])).

fof(f1581,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_173 ),
    inference(avatar_component_clause,[],[f1579])).

fof(f1705,plain,
    ( spl2_184
    | ~ spl2_173 ),
    inference(avatar_split_clause,[],[f1653,f1579,f1678])).

fof(f1678,plain,
    ( spl2_184
  <=> sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_184])])).

fof(f1653,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_173 ),
    inference(resolution,[],[f1581,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 ) ),
    inference(forward_demodulation,[],[f59,f47])).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f1704,plain,
    ( spl2_186
    | ~ spl2_173 ),
    inference(avatar_split_clause,[],[f1651,f1579,f1688])).

fof(f1688,plain,
    ( spl2_186
  <=> k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_186])])).

fof(f1651,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_173 ),
    inference(resolution,[],[f1581,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1703,plain,
    ( spl2_188
    | ~ spl2_173 ),
    inference(avatar_split_clause,[],[f1632,f1579,f1700])).

fof(f1632,plain,
    ( m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl2_173 ),
    inference(unit_resulting_resolution,[],[f1581,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f1587,plain,
    ( spl2_174
    | ~ spl2_72 ),
    inference(avatar_split_clause,[],[f1569,f578,f1584])).

fof(f1584,plain,
    ( spl2_174
  <=> k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_174])])).

fof(f578,plain,
    ( spl2_72
  <=> k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).

fof(f1569,plain,
    ( k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_72 ),
    inference(superposition,[],[f66,f580])).

fof(f580,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl2_72 ),
    inference(avatar_component_clause,[],[f578])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f54,f56,f56])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f1582,plain,
    ( spl2_173
    | ~ spl2_72 ),
    inference(avatar_split_clause,[],[f1568,f578,f1579])).

fof(f1568,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_72 ),
    inference(superposition,[],[f104,f580])).

fof(f104,plain,(
    ! [X0,X1] : m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f67,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1577,plain,
    ( spl2_172
    | ~ spl2_72
    | ~ spl2_104 ),
    inference(avatar_split_clause,[],[f1572,f825,f578,f1574])).

fof(f1574,plain,
    ( spl2_172
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_172])])).

fof(f825,plain,
    ( spl2_104
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_104])])).

fof(f1572,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl2_72
    | ~ spl2_104 ),
    inference(forward_demodulation,[],[f1567,f827])).

fof(f827,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_104 ),
    inference(avatar_component_clause,[],[f825])).

fof(f1567,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl2_72 ),
    inference(superposition,[],[f174,f580])).

fof(f174,plain,(
    ! [X0,X1] : k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f172,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f172,plain,(
    ! [X0,X1] : k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f68,f66])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f836,plain,
    ( spl2_104
    | ~ spl2_3
    | ~ spl2_23
    | ~ spl2_50 ),
    inference(avatar_split_clause,[],[f835,f429,f235,f82,f825])).

fof(f82,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f235,plain,
    ( spl2_23
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f429,plain,
    ( spl2_50
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f835,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_23
    | ~ spl2_50 ),
    inference(forward_demodulation,[],[f820,f431])).

fof(f431,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f429])).

fof(f820,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_23 ),
    inference(resolution,[],[f309,f237])).

fof(f237,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f235])).

fof(f309,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0) )
    | ~ spl2_3 ),
    inference(resolution,[],[f65,f84])).

fof(f84,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f591,plain,
    ( spl2_72
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f589,f82,f76,f578])).

fof(f76,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f589,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f281,f77])).

fof(f77,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f281,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f84,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f64,f56])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f584,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f583,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | spl2_46 ),
    inference(avatar_split_clause,[],[f407,f403,f87,f82,f72])).

fof(f72,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f87,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f403,plain,
    ( spl2_46
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f407,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_4
    | spl2_46 ),
    inference(unit_resulting_resolution,[],[f89,f84,f405,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f405,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_46 ),
    inference(avatar_component_clause,[],[f403])).

fof(f89,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f457,plain,
    ( spl2_54
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f433,f87,f82,f454])).

fof(f454,plain,
    ( spl2_54
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f433,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f89,f84,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f432,plain,
    ( spl2_50
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f408,f87,f82,f429])).

fof(f408,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f89,f84,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f406,plain,
    ( ~ spl2_46
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f401,f92,f87,f82,f72,f403])).

fof(f92,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f401,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f89,f94,f74,f84,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f94,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f238,plain,
    ( spl2_23
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f220,f87,f82,f235])).

fof(f220,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f89,f84,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f95,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f42,f92])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f90,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f43,f87])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f44,f82])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f45,f76,f72])).

fof(f45,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f46,f76,f72])).

fof(f46,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (31748)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (31742)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (31751)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (31743)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (31739)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (31753)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (31747)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (31746)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (31750)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (31749)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (31745)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (31741)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (31740)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (31752)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (31737)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.50  % (31743)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f1805,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f79,f80,f85,f90,f95,f238,f406,f432,f457,f583,f584,f591,f836,f1577,f1582,f1587,f1703,f1704,f1705,f1789,f1802])).
% 0.20/0.50  fof(f1802,plain,(
% 0.20/0.50    k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) != k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) | sK1 != k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) != k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | k2_pre_topc(sK0,sK1) != k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f1789,plain,(
% 0.20/0.50    spl2_195 | ~spl2_173 | ~spl2_188),
% 0.20/0.50    inference(avatar_split_clause,[],[f1722,f1700,f1579,f1786])).
% 0.20/0.50  fof(f1786,plain,(
% 0.20/0.50    spl2_195 <=> k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_195])])).
% 0.20/0.50  fof(f1579,plain,(
% 0.20/0.50    spl2_173 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_173])])).
% 0.20/0.50  fof(f1700,plain,(
% 0.20/0.50    spl2_188 <=> m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_188])])).
% 0.20/0.50  fof(f1722,plain,(
% 0.20/0.50    k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | (~spl2_173 | ~spl2_188)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f1581,f1702,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(flattening,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.50  fof(f1702,plain,(
% 0.20/0.50    m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | ~spl2_188),
% 0.20/0.50    inference(avatar_component_clause,[],[f1700])).
% 0.20/0.50  fof(f1581,plain,(
% 0.20/0.50    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_173),
% 0.20/0.50    inference(avatar_component_clause,[],[f1579])).
% 0.20/0.50  fof(f1705,plain,(
% 0.20/0.50    spl2_184 | ~spl2_173),
% 0.20/0.50    inference(avatar_split_clause,[],[f1653,f1579,f1678])).
% 0.20/0.50  fof(f1678,plain,(
% 0.20/0.50    spl2_184 <=> sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_184])])).
% 0.20/0.50  fof(f1653,plain,(
% 0.20/0.50    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_173),
% 0.20/0.50    inference(resolution,[],[f1581,f131])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0) )),
% 0.20/0.50    inference(forward_demodulation,[],[f59,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 0.20/0.50  fof(f1704,plain,(
% 0.20/0.50    spl2_186 | ~spl2_173),
% 0.20/0.50    inference(avatar_split_clause,[],[f1651,f1579,f1688])).
% 0.20/0.50  fof(f1688,plain,(
% 0.20/0.50    spl2_186 <=> k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_186])])).
% 0.20/0.50  fof(f1651,plain,(
% 0.20/0.50    k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_173),
% 0.20/0.50    inference(resolution,[],[f1581,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f58,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.50  fof(f1703,plain,(
% 0.20/0.50    spl2_188 | ~spl2_173),
% 0.20/0.50    inference(avatar_split_clause,[],[f1632,f1579,f1700])).
% 0.20/0.50  fof(f1632,plain,(
% 0.20/0.50    m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | ~spl2_173),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f1581,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.50  fof(f1587,plain,(
% 0.20/0.50    spl2_174 | ~spl2_72),
% 0.20/0.50    inference(avatar_split_clause,[],[f1569,f578,f1584])).
% 0.20/0.50  fof(f1584,plain,(
% 0.20/0.50    spl2_174 <=> k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_174])])).
% 0.20/0.50  fof(f578,plain,(
% 0.20/0.50    spl2_72 <=> k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).
% 0.20/0.50  fof(f1569,plain,(
% 0.20/0.50    k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl2_72),
% 0.20/0.50    inference(superposition,[],[f66,f580])).
% 0.20/0.50  fof(f580,plain,(
% 0.20/0.50    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) | ~spl2_72),
% 0.20/0.50    inference(avatar_component_clause,[],[f578])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f54,f56,f56])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.51  fof(f1582,plain,(
% 0.20/0.51    spl2_173 | ~spl2_72),
% 0.20/0.51    inference(avatar_split_clause,[],[f1568,f578,f1579])).
% 0.20/0.51  fof(f1568,plain,(
% 0.20/0.51    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_72),
% 0.20/0.51    inference(superposition,[],[f104,f580])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f67,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.51    inference(nnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f52,f56])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.51  fof(f1577,plain,(
% 0.20/0.51    spl2_172 | ~spl2_72 | ~spl2_104),
% 0.20/0.51    inference(avatar_split_clause,[],[f1572,f825,f578,f1574])).
% 0.20/0.51  fof(f1574,plain,(
% 0.20/0.51    spl2_172 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_172])])).
% 0.20/0.51  fof(f825,plain,(
% 0.20/0.51    spl2_104 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_104])])).
% 0.20/0.51  fof(f1572,plain,(
% 0.20/0.51    k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) | (~spl2_72 | ~spl2_104)),
% 0.20/0.51    inference(forward_demodulation,[],[f1567,f827])).
% 0.20/0.51  fof(f827,plain,(
% 0.20/0.51    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_104),
% 0.20/0.51    inference(avatar_component_clause,[],[f825])).
% 0.20/0.51  fof(f1567,plain,(
% 0.20/0.51    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) | ~spl2_72),
% 0.20/0.51    inference(superposition,[],[f174,f580])).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f172,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.51  fof(f172,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(superposition,[],[f68,f66])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f55,f56])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.51  fof(f836,plain,(
% 0.20/0.51    spl2_104 | ~spl2_3 | ~spl2_23 | ~spl2_50),
% 0.20/0.51    inference(avatar_split_clause,[],[f835,f429,f235,f82,f825])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.51  fof(f235,plain,(
% 0.20/0.51    spl2_23 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.20/0.51  fof(f429,plain,(
% 0.20/0.51    spl2_50 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 0.20/0.51  fof(f835,plain,(
% 0.20/0.51    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_23 | ~spl2_50)),
% 0.20/0.51    inference(forward_demodulation,[],[f820,f431])).
% 0.20/0.51  fof(f431,plain,(
% 0.20/0.51    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_50),
% 0.20/0.51    inference(avatar_component_clause,[],[f429])).
% 0.20/0.51  fof(f820,plain,(
% 0.20/0.51    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_23)),
% 0.20/0.51    inference(resolution,[],[f309,f237])).
% 0.20/0.51  fof(f237,plain,(
% 0.20/0.51    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_23),
% 0.20/0.51    inference(avatar_component_clause,[],[f235])).
% 0.20/0.51  fof(f309,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)) ) | ~spl2_3),
% 0.20/0.51    inference(resolution,[],[f65,f84])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f82])).
% 0.20/0.51  fof(f591,plain,(
% 0.20/0.51    spl2_72 | ~spl2_2 | ~spl2_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f589,f82,f76,f578])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.51  fof(f589,plain,(
% 0.20/0.51    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) | (~spl2_2 | ~spl2_3)),
% 0.20/0.51    inference(superposition,[],[f281,f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f76])).
% 0.20/0.51  fof(f281,plain,(
% 0.20/0.51    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) ) | ~spl2_3),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f84,f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f64,f56])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.20/0.51  fof(f584,plain,(
% 0.20/0.51    sK1 != k2_pre_topc(sK0,sK1) | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f583,plain,(
% 0.20/0.51    ~spl2_1 | ~spl2_3 | ~spl2_4 | spl2_46),
% 0.20/0.51    inference(avatar_split_clause,[],[f407,f403,f87,f82,f72])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    spl2_4 <=> l1_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.51  fof(f403,plain,(
% 0.20/0.51    spl2_46 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.20/0.51  fof(f407,plain,(
% 0.20/0.51    ~v4_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_4 | spl2_46)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f89,f84,f405,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.51  fof(f405,plain,(
% 0.20/0.51    sK1 != k2_pre_topc(sK0,sK1) | spl2_46),
% 0.20/0.51    inference(avatar_component_clause,[],[f403])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    l1_pre_topc(sK0) | ~spl2_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f87])).
% 0.20/0.51  fof(f457,plain,(
% 0.20/0.51    spl2_54 | ~spl2_3 | ~spl2_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f433,f87,f82,f454])).
% 0.20/0.51  fof(f454,plain,(
% 0.20/0.51    spl2_54 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 0.20/0.51  fof(f433,plain,(
% 0.20/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f89,f84,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.20/0.51  fof(f432,plain,(
% 0.20/0.51    spl2_50 | ~spl2_3 | ~spl2_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f408,f87,f82,f429])).
% 0.20/0.51  fof(f408,plain,(
% 0.20/0.51    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f89,f84,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 0.20/0.51  fof(f406,plain,(
% 0.20/0.51    ~spl2_46 | spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f401,f92,f87,f82,f72,f403])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    spl2_5 <=> v2_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.51  fof(f401,plain,(
% 0.20/0.51    sK1 != k2_pre_topc(sK0,sK1) | (spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f89,f94,f74,f84,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ~v4_pre_topc(sK1,sK0) | spl2_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f72])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    v2_pre_topc(sK0) | ~spl2_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f92])).
% 0.20/0.51  fof(f238,plain,(
% 0.20/0.51    spl2_23 | ~spl2_3 | ~spl2_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f220,f87,f82,f235])).
% 0.20/0.51  fof(f220,plain,(
% 0.20/0.51    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_4)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f89,f84,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    spl2_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f42,f92])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    v2_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f18])).
% 0.20/0.51  fof(f18,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    spl2_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f43,f87])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    spl2_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f44,f82])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    spl2_1 | spl2_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f45,f76,f72])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ~spl2_1 | ~spl2_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f46,f76,f72])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (31743)------------------------------
% 0.20/0.51  % (31743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31743)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (31743)Memory used [KB]: 7419
% 0.20/0.51  % (31743)Time elapsed: 0.061 s
% 0.20/0.51  % (31743)------------------------------
% 0.20/0.51  % (31743)------------------------------
% 0.20/0.51  % (31736)Success in time 0.151 s
%------------------------------------------------------------------------------
