%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:50 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 183 expanded)
%              Number of leaves         :   31 (  77 expanded)
%              Depth                    :    9
%              Number of atoms          :  273 ( 450 expanded)
%              Number of equality atoms :   70 ( 114 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1946,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f126,f131,f140,f141,f345,f354,f466,f501,f704,f705,f711,f1437,f1743,f1930,f1944])).

fof(f1944,plain,
    ( k2_pre_topc(sK0,sK1) != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | sK1 != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | v4_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1930,plain,
    ( spl3_93
    | ~ spl3_86 ),
    inference(avatar_split_clause,[],[f1925,f1740,f1927])).

fof(f1927,plain,
    ( spl3_93
  <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).

fof(f1740,plain,
    ( spl3_86
  <=> k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).

fof(f1925,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_86 ),
    inference(forward_demodulation,[],[f1908,f102])).

fof(f102,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f67,f82])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f67,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f1908,plain,
    ( k3_tarski(k2_tarski(sK1,k1_xboole_0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_86 ),
    inference(superposition,[],[f109,f1742])).

fof(f1742,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_86 ),
    inference(avatar_component_clause,[],[f1740])).

fof(f109,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0))) ),
    inference(definition_unfolding,[],[f85,f82,f80,f82])).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f85,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1743,plain,
    ( spl3_86
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f1677,f699,f1740])).

fof(f699,plain,
    ( spl3_44
  <=> k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f1677,plain,
    ( k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_44 ),
    inference(superposition,[],[f601,f701])).

fof(f701,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f699])).

fof(f601,plain,(
    ! [X2,X3] : k1_xboole_0 = k6_subset_1(k6_subset_1(X2,X3),X2) ),
    inference(resolution,[],[f593,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f593,plain,(
    ! [X2,X3] : r1_tarski(k6_subset_1(k6_subset_1(X2,X3),X2),k1_xboole_0) ),
    inference(resolution,[],[f293,f106])).

fof(f106,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f77,f80])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f293,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r1_tarski(k6_subset_1(X1,X0),k1_xboole_0) ) ),
    inference(superposition,[],[f114,f102])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f98,f82,f80])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f1437,plain,
    ( spl3_59
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f1432,f463,f351,f128,f1434])).

fof(f1434,plain,
    ( spl3_59
  <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f128,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f351,plain,
    ( spl3_11
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f463,plain,
    ( spl3_23
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f1432,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f1414,f465])).

fof(f465,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f463])).

fof(f1414,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(resolution,[],[f449,f353])).

fof(f353,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f351])).

fof(f449,plain,
    ( ! [X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X11) = k3_tarski(k2_tarski(sK1,X11)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f116,f130])).

fof(f130,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f101,f82])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f711,plain,
    ( spl3_44
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f709,f137,f128,f699])).

fof(f137,plain,
    ( spl3_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f709,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(superposition,[],[f323,f138])).

fof(f138,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f137])).

fof(f323,plain,
    ( ! [X7] : k7_subset_1(u1_struct_0(sK0),sK1,X7) = k6_subset_1(sK1,X7)
    | ~ spl3_3 ),
    inference(resolution,[],[f113,f130])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) ) ),
    inference(definition_unfolding,[],[f97,f80])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f705,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f704,plain,
    ( spl3_21
    | ~ spl3_4
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f358,f128,f118,f133,f425])).

fof(f425,plain,
    ( spl3_21
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f133,plain,
    ( spl3_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f118,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f358,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f73,f130])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f501,plain,
    ( spl3_25
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f491,f128,f118,f498])).

fof(f498,plain,
    ( spl3_25
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f491,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f71,f130])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f466,plain,
    ( spl3_23
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f456,f128,f118,f463])).

fof(f456,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f70,f130])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f354,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f349,f128,f118,f351])).

fof(f349,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(resolution,[],[f93,f130])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f345,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f340,f128,f118,f123,f342])).

fof(f342,plain,
    ( spl3_10
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f123,plain,
    ( spl3_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f340,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f92,f130])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f141,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f62,f137,f133])).

fof(f62,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f140,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f63,f137,f133])).

fof(f63,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f131,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f64,f128])).

fof(f64,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f126,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f65,f123])).

fof(f65,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f121,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f66,f118])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:46:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (30018)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (30010)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (30009)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (30025)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (30026)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (30005)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (30004)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.54  % (30017)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.34/0.54  % (30008)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.54  % (30006)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.34/0.54  % (30007)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.54  % (30029)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.54  % (30033)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.55  % (30032)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.55  % (30031)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.55  % (30030)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.55  % (30027)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.34/0.55  % (30021)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.55  % (30020)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.55  % (30021)Refutation not found, incomplete strategy% (30021)------------------------------
% 1.34/0.55  % (30021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (30021)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (30021)Memory used [KB]: 10618
% 1.34/0.55  % (30021)Time elapsed: 0.138 s
% 1.34/0.55  % (30021)------------------------------
% 1.34/0.55  % (30021)------------------------------
% 1.34/0.55  % (30019)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.48/0.55  % (30013)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.48/0.55  % (30024)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.48/0.55  % (30022)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.48/0.55  % (30023)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.48/0.56  % (30016)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.56  % (30015)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.48/0.56  % (30028)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.48/0.56  % (30014)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.48/0.56  % (30012)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.48/0.57  % (30011)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.97/0.63  % (30020)Refutation found. Thanks to Tanya!
% 1.97/0.63  % SZS status Theorem for theBenchmark
% 1.97/0.65  % SZS output start Proof for theBenchmark
% 1.97/0.65  fof(f1946,plain,(
% 1.97/0.65    $false),
% 1.97/0.65    inference(avatar_sat_refutation,[],[f121,f126,f131,f140,f141,f345,f354,f466,f501,f704,f705,f711,f1437,f1743,f1930,f1944])).
% 1.97/0.65  fof(f1944,plain,(
% 1.97/0.65    k2_pre_topc(sK0,sK1) != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | sK1 != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | v4_pre_topc(sK1,sK0) | ~v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 1.97/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.97/0.65  fof(f1930,plain,(
% 1.97/0.65    spl3_93 | ~spl3_86),
% 1.97/0.65    inference(avatar_split_clause,[],[f1925,f1740,f1927])).
% 1.97/0.65  fof(f1927,plain,(
% 1.97/0.65    spl3_93 <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).
% 1.97/0.65  fof(f1740,plain,(
% 1.97/0.65    spl3_86 <=> k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),sK1)),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).
% 1.97/0.65  fof(f1925,plain,(
% 1.97/0.65    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl3_86),
% 1.97/0.65    inference(forward_demodulation,[],[f1908,f102])).
% 1.97/0.65  fof(f102,plain,(
% 1.97/0.65    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 1.97/0.65    inference(definition_unfolding,[],[f67,f82])).
% 1.97/0.65  fof(f82,plain,(
% 1.97/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.97/0.65    inference(cnf_transformation,[],[f17])).
% 1.97/0.65  fof(f17,axiom,(
% 1.97/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.97/0.65  fof(f67,plain,(
% 1.97/0.65    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.97/0.65    inference(cnf_transformation,[],[f5])).
% 1.97/0.65  fof(f5,axiom,(
% 1.97/0.65    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.97/0.65  fof(f1908,plain,(
% 1.97/0.65    k3_tarski(k2_tarski(sK1,k1_xboole_0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl3_86),
% 1.97/0.65    inference(superposition,[],[f109,f1742])).
% 1.97/0.65  fof(f1742,plain,(
% 1.97/0.65    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),sK1) | ~spl3_86),
% 1.97/0.65    inference(avatar_component_clause,[],[f1740])).
% 1.97/0.65  fof(f109,plain,(
% 1.97/0.65    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0)))) )),
% 1.97/0.65    inference(definition_unfolding,[],[f85,f82,f80,f82])).
% 1.97/0.65  fof(f80,plain,(
% 1.97/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f24])).
% 1.97/0.65  fof(f24,axiom,(
% 1.97/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.97/0.65  fof(f85,plain,(
% 1.97/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f10])).
% 1.97/0.65  fof(f10,axiom,(
% 1.97/0.65    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.97/0.65  fof(f1743,plain,(
% 1.97/0.65    spl3_86 | ~spl3_44),
% 1.97/0.65    inference(avatar_split_clause,[],[f1677,f699,f1740])).
% 1.97/0.65  fof(f699,plain,(
% 1.97/0.65    spl3_44 <=> k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 1.97/0.65  fof(f1677,plain,(
% 1.97/0.65    k1_xboole_0 = k6_subset_1(k2_tops_1(sK0,sK1),sK1) | ~spl3_44),
% 1.97/0.65    inference(superposition,[],[f601,f701])).
% 1.97/0.65  fof(f701,plain,(
% 1.97/0.65    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl3_44),
% 1.97/0.65    inference(avatar_component_clause,[],[f699])).
% 1.97/0.65  fof(f601,plain,(
% 1.97/0.65    ( ! [X2,X3] : (k1_xboole_0 = k6_subset_1(k6_subset_1(X2,X3),X2)) )),
% 1.97/0.65    inference(resolution,[],[f593,f74])).
% 1.97/0.65  fof(f74,plain,(
% 1.97/0.65    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.97/0.65    inference(cnf_transformation,[],[f43])).
% 1.97/0.65  fof(f43,plain,(
% 1.97/0.65    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.97/0.65    inference(ennf_transformation,[],[f12])).
% 1.97/0.65  fof(f12,axiom,(
% 1.97/0.65    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.97/0.65  fof(f593,plain,(
% 1.97/0.65    ( ! [X2,X3] : (r1_tarski(k6_subset_1(k6_subset_1(X2,X3),X2),k1_xboole_0)) )),
% 1.97/0.65    inference(resolution,[],[f293,f106])).
% 1.97/0.65  fof(f106,plain,(
% 1.97/0.65    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 1.97/0.65    inference(definition_unfolding,[],[f77,f80])).
% 1.97/0.65  fof(f77,plain,(
% 1.97/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f8])).
% 1.97/0.65  fof(f8,axiom,(
% 1.97/0.65    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.97/0.65  fof(f293,plain,(
% 1.97/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | r1_tarski(k6_subset_1(X1,X0),k1_xboole_0)) )),
% 1.97/0.65    inference(superposition,[],[f114,f102])).
% 1.97/0.65  fof(f114,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 1.97/0.65    inference(definition_unfolding,[],[f98,f82,f80])).
% 1.97/0.65  fof(f98,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f56])).
% 1.97/0.65  fof(f56,plain,(
% 1.97/0.65    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.97/0.65    inference(ennf_transformation,[],[f13])).
% 1.97/0.65  fof(f13,axiom,(
% 1.97/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.97/0.65  fof(f1437,plain,(
% 1.97/0.65    spl3_59 | ~spl3_3 | ~spl3_11 | ~spl3_23),
% 1.97/0.65    inference(avatar_split_clause,[],[f1432,f463,f351,f128,f1434])).
% 1.97/0.65  fof(f1434,plain,(
% 1.97/0.65    spl3_59 <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 1.97/0.65  fof(f128,plain,(
% 1.97/0.65    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.97/0.65  fof(f351,plain,(
% 1.97/0.65    spl3_11 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.97/0.65  fof(f463,plain,(
% 1.97/0.65    spl3_23 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.97/0.65  fof(f1432,plain,(
% 1.97/0.65    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl3_3 | ~spl3_11 | ~spl3_23)),
% 1.97/0.65    inference(forward_demodulation,[],[f1414,f465])).
% 1.97/0.65  fof(f465,plain,(
% 1.97/0.65    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl3_23),
% 1.97/0.65    inference(avatar_component_clause,[],[f463])).
% 1.97/0.65  fof(f1414,plain,(
% 1.97/0.65    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl3_3 | ~spl3_11)),
% 1.97/0.65    inference(resolution,[],[f449,f353])).
% 1.97/0.65  fof(f353,plain,(
% 1.97/0.65    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_11),
% 1.97/0.65    inference(avatar_component_clause,[],[f351])).
% 1.97/0.65  fof(f449,plain,(
% 1.97/0.65    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X11) = k3_tarski(k2_tarski(sK1,X11))) ) | ~spl3_3),
% 1.97/0.65    inference(resolution,[],[f116,f130])).
% 1.97/0.65  fof(f130,plain,(
% 1.97/0.65    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 1.97/0.65    inference(avatar_component_clause,[],[f128])).
% 1.97/0.65  fof(f116,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))) )),
% 1.97/0.65    inference(definition_unfolding,[],[f101,f82])).
% 1.97/0.65  fof(f101,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f61])).
% 1.97/0.65  fof(f61,plain,(
% 1.97/0.65    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.97/0.65    inference(flattening,[],[f60])).
% 1.97/0.65  fof(f60,plain,(
% 1.97/0.65    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.97/0.65    inference(ennf_transformation,[],[f23])).
% 1.97/0.65  fof(f23,axiom,(
% 1.97/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.97/0.65  fof(f711,plain,(
% 1.97/0.65    spl3_44 | ~spl3_3 | ~spl3_5),
% 1.97/0.65    inference(avatar_split_clause,[],[f709,f137,f128,f699])).
% 1.97/0.65  fof(f137,plain,(
% 1.97/0.65    spl3_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.97/0.65  fof(f709,plain,(
% 1.97/0.65    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_5)),
% 1.97/0.65    inference(superposition,[],[f323,f138])).
% 1.97/0.65  fof(f138,plain,(
% 1.97/0.65    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl3_5),
% 1.97/0.65    inference(avatar_component_clause,[],[f137])).
% 1.97/0.65  fof(f323,plain,(
% 1.97/0.65    ( ! [X7] : (k7_subset_1(u1_struct_0(sK0),sK1,X7) = k6_subset_1(sK1,X7)) ) | ~spl3_3),
% 1.97/0.65    inference(resolution,[],[f113,f130])).
% 1.97/0.65  fof(f113,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)) )),
% 1.97/0.65    inference(definition_unfolding,[],[f97,f80])).
% 1.97/0.65  fof(f97,plain,(
% 1.97/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f55])).
% 1.97/0.65  fof(f55,plain,(
% 1.97/0.65    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.97/0.65    inference(ennf_transformation,[],[f25])).
% 1.97/0.65  fof(f25,axiom,(
% 1.97/0.65    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.97/0.65  fof(f705,plain,(
% 1.97/0.65    sK1 != k2_pre_topc(sK0,sK1) | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.97/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.97/0.65  fof(f704,plain,(
% 1.97/0.65    spl3_21 | ~spl3_4 | ~spl3_1 | ~spl3_3),
% 1.97/0.65    inference(avatar_split_clause,[],[f358,f128,f118,f133,f425])).
% 1.97/0.65  fof(f425,plain,(
% 1.97/0.65    spl3_21 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.97/0.65  fof(f133,plain,(
% 1.97/0.65    spl3_4 <=> v4_pre_topc(sK1,sK0)),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.97/0.65  fof(f118,plain,(
% 1.97/0.65    spl3_1 <=> l1_pre_topc(sK0)),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.97/0.65  fof(f358,plain,(
% 1.97/0.65    ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~spl3_3),
% 1.97/0.65    inference(resolution,[],[f73,f130])).
% 1.97/0.65  fof(f73,plain,(
% 1.97/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 1.97/0.65    inference(cnf_transformation,[],[f42])).
% 1.97/0.65  fof(f42,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.97/0.65    inference(flattening,[],[f41])).
% 1.97/0.65  fof(f41,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.97/0.65    inference(ennf_transformation,[],[f27])).
% 1.97/0.65  fof(f27,axiom,(
% 1.97/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.97/0.65  fof(f501,plain,(
% 1.97/0.65    spl3_25 | ~spl3_1 | ~spl3_3),
% 1.97/0.65    inference(avatar_split_clause,[],[f491,f128,f118,f498])).
% 1.97/0.65  fof(f498,plain,(
% 1.97/0.65    spl3_25 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.97/0.65  fof(f491,plain,(
% 1.97/0.65    ~l1_pre_topc(sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl3_3),
% 1.97/0.65    inference(resolution,[],[f71,f130])).
% 1.97/0.65  fof(f71,plain,(
% 1.97/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 1.97/0.65    inference(cnf_transformation,[],[f40])).
% 1.97/0.65  fof(f40,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.97/0.65    inference(ennf_transformation,[],[f30])).
% 1.97/0.65  fof(f30,axiom,(
% 1.97/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 1.97/0.65  fof(f466,plain,(
% 1.97/0.65    spl3_23 | ~spl3_1 | ~spl3_3),
% 1.97/0.65    inference(avatar_split_clause,[],[f456,f128,f118,f463])).
% 1.97/0.65  fof(f456,plain,(
% 1.97/0.65    ~l1_pre_topc(sK0) | k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl3_3),
% 1.97/0.65    inference(resolution,[],[f70,f130])).
% 1.97/0.65  fof(f70,plain,(
% 1.97/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 1.97/0.65    inference(cnf_transformation,[],[f39])).
% 1.97/0.65  fof(f39,plain,(
% 1.97/0.65    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.97/0.65    inference(ennf_transformation,[],[f32])).
% 1.97/0.65  fof(f32,axiom,(
% 1.97/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 1.97/0.65  fof(f354,plain,(
% 1.97/0.65    spl3_11 | ~spl3_1 | ~spl3_3),
% 1.97/0.65    inference(avatar_split_clause,[],[f349,f128,f118,f351])).
% 1.97/0.65  fof(f349,plain,(
% 1.97/0.65    ~l1_pre_topc(sK0) | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 1.97/0.65    inference(resolution,[],[f93,f130])).
% 1.97/0.65  fof(f93,plain,(
% 1.97/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.97/0.65    inference(cnf_transformation,[],[f53])).
% 1.97/0.65  fof(f53,plain,(
% 1.97/0.65    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.97/0.65    inference(flattening,[],[f52])).
% 1.97/0.65  fof(f52,plain,(
% 1.97/0.65    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.97/0.65    inference(ennf_transformation,[],[f28])).
% 1.97/0.65  fof(f28,axiom,(
% 1.97/0.65    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.97/0.65  fof(f345,plain,(
% 1.97/0.65    spl3_10 | ~spl3_2 | ~spl3_1 | ~spl3_3),
% 1.97/0.65    inference(avatar_split_clause,[],[f340,f128,f118,f123,f342])).
% 1.97/0.65  fof(f342,plain,(
% 1.97/0.65    spl3_10 <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.97/0.65  fof(f123,plain,(
% 1.97/0.65    spl3_2 <=> v2_pre_topc(sK0)),
% 1.97/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.97/0.65  fof(f340,plain,(
% 1.97/0.65    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~spl3_3),
% 1.97/0.65    inference(resolution,[],[f92,f130])).
% 1.97/0.65  fof(f92,plain,(
% 1.97/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v4_pre_topc(k2_pre_topc(X0,X1),X0)) )),
% 1.97/0.65    inference(cnf_transformation,[],[f51])).
% 1.97/0.65  fof(f51,plain,(
% 1.97/0.65    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.97/0.65    inference(flattening,[],[f50])).
% 1.97/0.65  fof(f50,plain,(
% 1.97/0.65    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.97/0.65    inference(ennf_transformation,[],[f29])).
% 1.97/0.65  fof(f29,axiom,(
% 1.97/0.65    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 1.97/0.65  fof(f141,plain,(
% 1.97/0.65    spl3_4 | spl3_5),
% 1.97/0.65    inference(avatar_split_clause,[],[f62,f137,f133])).
% 1.97/0.65  fof(f62,plain,(
% 1.97/0.65    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.97/0.65    inference(cnf_transformation,[],[f37])).
% 1.97/0.65  fof(f37,plain,(
% 1.97/0.65    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.97/0.65    inference(flattening,[],[f36])).
% 1.97/0.65  fof(f36,plain,(
% 1.97/0.65    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.97/0.65    inference(ennf_transformation,[],[f34])).
% 1.97/0.65  fof(f34,negated_conjecture,(
% 1.97/0.65    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.97/0.65    inference(negated_conjecture,[],[f33])).
% 1.97/0.65  fof(f33,conjecture,(
% 1.97/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.97/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 1.97/0.65  fof(f140,plain,(
% 1.97/0.65    ~spl3_4 | ~spl3_5),
% 1.97/0.65    inference(avatar_split_clause,[],[f63,f137,f133])).
% 1.97/0.65  fof(f63,plain,(
% 1.97/0.65    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 1.97/0.65    inference(cnf_transformation,[],[f37])).
% 1.97/0.65  fof(f131,plain,(
% 1.97/0.65    spl3_3),
% 1.97/0.65    inference(avatar_split_clause,[],[f64,f128])).
% 1.97/0.65  fof(f64,plain,(
% 1.97/0.65    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.97/0.65    inference(cnf_transformation,[],[f37])).
% 1.97/0.65  fof(f126,plain,(
% 1.97/0.65    spl3_2),
% 1.97/0.65    inference(avatar_split_clause,[],[f65,f123])).
% 1.97/0.65  fof(f65,plain,(
% 1.97/0.65    v2_pre_topc(sK0)),
% 1.97/0.65    inference(cnf_transformation,[],[f37])).
% 1.97/0.65  fof(f121,plain,(
% 1.97/0.65    spl3_1),
% 1.97/0.65    inference(avatar_split_clause,[],[f66,f118])).
% 1.97/0.65  fof(f66,plain,(
% 1.97/0.65    l1_pre_topc(sK0)),
% 1.97/0.65    inference(cnf_transformation,[],[f37])).
% 1.97/0.65  % SZS output end Proof for theBenchmark
% 1.97/0.65  % (30020)------------------------------
% 1.97/0.65  % (30020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.65  % (30020)Termination reason: Refutation
% 1.97/0.65  
% 1.97/0.65  % (30020)Memory used [KB]: 12025
% 1.97/0.65  % (30020)Time elapsed: 0.211 s
% 1.97/0.65  % (30020)------------------------------
% 1.97/0.65  % (30020)------------------------------
% 1.97/0.66  % (30003)Success in time 0.288 s
%------------------------------------------------------------------------------
