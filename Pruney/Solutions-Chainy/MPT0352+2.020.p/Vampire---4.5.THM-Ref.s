%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:17 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 246 expanded)
%              Number of leaves         :   39 ( 104 expanded)
%              Depth                    :    9
%              Number of atoms          :  348 ( 656 expanded)
%              Number of equality atoms :   32 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2590,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f80,f85,f90,f103,f108,f139,f205,f206,f220,f560,f576,f634,f650,f673,f721,f913,f998,f2587,f2589])).

fof(f2589,plain,
    ( sK0 != k3_tarski(k2_tarski(sK0,sK2))
    | ~ r1_tarski(sK1,sK0)
    | r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2587,plain,
    ( spl3_158
    | ~ spl3_69 ),
    inference(avatar_split_clause,[],[f2582,f958,f2584])).

fof(f2584,plain,
    ( spl3_158
  <=> sK0 = k3_tarski(k2_tarski(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_158])])).

fof(f958,plain,
    ( spl3_69
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f2582,plain,
    ( sK0 = k3_tarski(k2_tarski(sK0,sK2))
    | ~ spl3_69 ),
    inference(forward_demodulation,[],[f2564,f67])).

fof(f67,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f2564,plain,
    ( k3_tarski(k2_tarski(sK0,sK2)) = k3_tarski(k2_tarski(sK0,k1_xboole_0))
    | ~ spl3_69 ),
    inference(superposition,[],[f69,f960])).

fof(f960,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f958])).

fof(f69,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f53,f52,f52])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f998,plain,
    ( spl3_69
    | ~ spl3_68 ),
    inference(avatar_split_clause,[],[f956,f910,f958])).

fof(f910,plain,
    ( spl3_68
  <=> v1_xboole_0(k4_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f956,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | ~ spl3_68 ),
    inference(resolution,[],[f912,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f912,plain,
    ( v1_xboole_0(k4_xboole_0(sK2,sK0))
    | ~ spl3_68 ),
    inference(avatar_component_clause,[],[f910])).

fof(f913,plain,
    ( spl3_68
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f905,f215,f910])).

fof(f215,plain,
    ( spl3_17
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f905,plain,
    ( v1_xboole_0(k4_xboole_0(sK2,sK0))
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f49,f227,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f227,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK2,X0),sK0)
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f50,f217,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f217,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f215])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f721,plain,
    ( ~ spl3_51
    | spl3_1
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f716,f544,f72,f718])).

fof(f718,plain,
    ( spl3_51
  <=> r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f72,plain,
    ( spl3_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f544,plain,
    ( spl3_44
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f716,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK2)))
    | spl3_1
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f715,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f51,f52,f52])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f715,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK2,sK0)))
    | spl3_1
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f703,f69])).

fof(f703,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK2,k4_xboole_0(sK0,sK2))))
    | spl3_1
    | ~ spl3_44 ),
    inference(unit_resulting_resolution,[],[f74,f545,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f66,f52])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f545,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f544])).

fof(f74,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f673,plain,
    ( spl3_44
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f670,f528,f544])).

fof(f528,plain,
    ( spl3_41
  <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f670,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_41 ),
    inference(resolution,[],[f530,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f530,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f528])).

fof(f650,plain,
    ( spl3_41
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f644,f533,f528])).

fof(f533,plain,
    ( spl3_42
  <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f644,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl3_42 ),
    inference(resolution,[],[f535,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f535,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f533])).

fof(f634,plain,
    ( spl3_42
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f633,f201,f196,f76,f533])).

fof(f76,plain,
    ( spl3_2
  <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f196,plain,
    ( spl3_15
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f201,plain,
    ( spl3_16
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f633,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f632,f203])).

fof(f203,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f201])).

fof(f632,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f77,f198])).

fof(f198,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f196])).

fof(f77,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f576,plain,
    ( ~ spl3_1
    | spl3_42 ),
    inference(avatar_contradiction_clause,[],[f570])).

fof(f570,plain,
    ( $false
    | ~ spl3_1
    | spl3_42 ),
    inference(unit_resulting_resolution,[],[f73,f534,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f534,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl3_42 ),
    inference(avatar_component_clause,[],[f533])).

fof(f73,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f560,plain,
    ( ~ spl3_42
    | spl3_2
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f559,f201,f196,f76,f533])).

fof(f559,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl3_2
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f558,f203])).

fof(f558,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl3_2
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f78,f198])).

fof(f78,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f220,plain,
    ( spl3_17
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f219,f105,f215])).

fof(f105,plain,
    ( spl3_6
  <=> r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f219,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f212,f46])).

fof(f46,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f212,plain,
    ( r1_tarski(sK2,k3_tarski(k1_zfmisc_1(sK0)))
    | ~ spl3_6 ),
    inference(resolution,[],[f107,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f107,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f206,plain,
    ( spl3_15
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f194,f87,f196])).

fof(f87,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f194,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f61,f89])).

fof(f89,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f205,plain,
    ( spl3_16
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f193,f82,f201])).

fof(f82,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f193,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f61,f84])).

fof(f84,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f139,plain,
    ( spl3_10
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f138,f100,f134])).

fof(f134,plain,
    ( spl3_10
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f100,plain,
    ( spl3_5
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f138,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f131,f46])).

fof(f131,plain,
    ( r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0)))
    | ~ spl3_5 ),
    inference(resolution,[],[f102,f59])).

fof(f102,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f108,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f95,f82,f105])).

fof(f95,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f45,f84,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f45,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f103,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f96,f87,f100])).

fof(f96,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f45,f89,f54])).

fof(f90,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f41,f87])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | ~ r1_tarski(sK1,X2) )
        & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | r1_tarski(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | ~ r1_tarski(sK1,sK2) )
      & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | r1_tarski(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f85,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f42,f82])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f43,f76,f72])).

fof(f43,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f44,f76,f72])).

fof(f44,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (17694)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.45  % (17687)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.45  % (17684)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (17689)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (17688)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (17698)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (17690)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (17695)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (17696)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (17693)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (17685)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (17697)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (17686)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (17692)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (17699)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (17700)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (17691)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.29/0.52  % (17701)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.29/0.52  % (17690)Refutation found. Thanks to Tanya!
% 1.29/0.52  % SZS status Theorem for theBenchmark
% 1.29/0.52  % SZS output start Proof for theBenchmark
% 1.29/0.52  fof(f2590,plain,(
% 1.29/0.52    $false),
% 1.29/0.52    inference(avatar_sat_refutation,[],[f79,f80,f85,f90,f103,f108,f139,f205,f206,f220,f560,f576,f634,f650,f673,f721,f913,f998,f2587,f2589])).
% 1.29/0.52  fof(f2589,plain,(
% 1.29/0.52    sK0 != k3_tarski(k2_tarski(sK0,sK2)) | ~r1_tarski(sK1,sK0) | r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK2)))),
% 1.29/0.52    introduced(theory_tautology_sat_conflict,[])).
% 1.29/0.52  fof(f2587,plain,(
% 1.29/0.52    spl3_158 | ~spl3_69),
% 1.29/0.52    inference(avatar_split_clause,[],[f2582,f958,f2584])).
% 1.29/0.52  fof(f2584,plain,(
% 1.29/0.52    spl3_158 <=> sK0 = k3_tarski(k2_tarski(sK0,sK2))),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_158])])).
% 1.29/0.52  fof(f958,plain,(
% 1.29/0.52    spl3_69 <=> k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 1.29/0.52  fof(f2582,plain,(
% 1.29/0.52    sK0 = k3_tarski(k2_tarski(sK0,sK2)) | ~spl3_69),
% 1.29/0.52    inference(forward_demodulation,[],[f2564,f67])).
% 1.29/0.52  fof(f67,plain,(
% 1.29/0.52    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 1.29/0.52    inference(definition_unfolding,[],[f47,f52])).
% 1.29/0.52  fof(f52,plain,(
% 1.29/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.29/0.52    inference(cnf_transformation,[],[f14])).
% 1.29/0.52  fof(f14,axiom,(
% 1.29/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.29/0.52  fof(f47,plain,(
% 1.29/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.29/0.52    inference(cnf_transformation,[],[f5])).
% 1.29/0.52  fof(f5,axiom,(
% 1.29/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.29/0.52  fof(f2564,plain,(
% 1.29/0.52    k3_tarski(k2_tarski(sK0,sK2)) = k3_tarski(k2_tarski(sK0,k1_xboole_0)) | ~spl3_69),
% 1.29/0.52    inference(superposition,[],[f69,f960])).
% 1.29/0.52  fof(f960,plain,(
% 1.29/0.52    k1_xboole_0 = k4_xboole_0(sK2,sK0) | ~spl3_69),
% 1.29/0.52    inference(avatar_component_clause,[],[f958])).
% 1.29/0.52  fof(f69,plain,(
% 1.29/0.52    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0)))) )),
% 1.29/0.52    inference(definition_unfolding,[],[f53,f52,f52])).
% 1.29/0.52  fof(f53,plain,(
% 1.29/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.29/0.52    inference(cnf_transformation,[],[f9])).
% 1.29/0.52  fof(f9,axiom,(
% 1.29/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.29/0.52  fof(f998,plain,(
% 1.29/0.52    spl3_69 | ~spl3_68),
% 1.29/0.52    inference(avatar_split_clause,[],[f956,f910,f958])).
% 1.29/0.52  fof(f910,plain,(
% 1.29/0.52    spl3_68 <=> v1_xboole_0(k4_xboole_0(sK2,sK0))),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 1.29/0.52  fof(f956,plain,(
% 1.29/0.52    k1_xboole_0 = k4_xboole_0(sK2,sK0) | ~spl3_68),
% 1.29/0.52    inference(resolution,[],[f912,f48])).
% 1.29/0.52  fof(f48,plain,(
% 1.29/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.29/0.52    inference(cnf_transformation,[],[f22])).
% 1.29/0.52  fof(f22,plain,(
% 1.29/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.29/0.52    inference(ennf_transformation,[],[f2])).
% 1.29/0.52  fof(f2,axiom,(
% 1.29/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.29/0.52  fof(f912,plain,(
% 1.29/0.52    v1_xboole_0(k4_xboole_0(sK2,sK0)) | ~spl3_68),
% 1.29/0.52    inference(avatar_component_clause,[],[f910])).
% 1.29/0.52  fof(f913,plain,(
% 1.29/0.52    spl3_68 | ~spl3_17),
% 1.29/0.52    inference(avatar_split_clause,[],[f905,f215,f910])).
% 1.29/0.52  fof(f215,plain,(
% 1.29/0.52    spl3_17 <=> r1_tarski(sK2,sK0)),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.29/0.52  fof(f905,plain,(
% 1.29/0.52    v1_xboole_0(k4_xboole_0(sK2,sK0)) | ~spl3_17),
% 1.29/0.52    inference(unit_resulting_resolution,[],[f49,f227,f58])).
% 1.29/0.52  fof(f58,plain,(
% 1.29/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X1)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f25])).
% 1.29/0.52  fof(f25,plain,(
% 1.29/0.52    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.29/0.52    inference(flattening,[],[f24])).
% 1.29/0.52  fof(f24,plain,(
% 1.29/0.52    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.29/0.52    inference(ennf_transformation,[],[f10])).
% 1.29/0.52  fof(f10,axiom,(
% 1.29/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.29/0.52  fof(f227,plain,(
% 1.29/0.52    ( ! [X0] : (r1_tarski(k4_xboole_0(sK2,X0),sK0)) ) | ~spl3_17),
% 1.29/0.52    inference(unit_resulting_resolution,[],[f50,f217,f65])).
% 1.29/0.52  fof(f65,plain,(
% 1.29/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f32])).
% 1.29/0.52  fof(f32,plain,(
% 1.29/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.29/0.52    inference(flattening,[],[f31])).
% 1.29/0.52  fof(f31,plain,(
% 1.29/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.29/0.52    inference(ennf_transformation,[],[f6])).
% 1.29/0.52  fof(f6,axiom,(
% 1.29/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.29/0.52  fof(f217,plain,(
% 1.29/0.52    r1_tarski(sK2,sK0) | ~spl3_17),
% 1.29/0.52    inference(avatar_component_clause,[],[f215])).
% 1.29/0.52  fof(f50,plain,(
% 1.29/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f8])).
% 1.29/0.52  fof(f8,axiom,(
% 1.29/0.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.29/0.52  fof(f49,plain,(
% 1.29/0.52    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f12])).
% 1.29/0.52  fof(f12,axiom,(
% 1.29/0.52    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.29/0.52  fof(f721,plain,(
% 1.29/0.52    ~spl3_51 | spl3_1 | ~spl3_44),
% 1.29/0.52    inference(avatar_split_clause,[],[f716,f544,f72,f718])).
% 1.29/0.52  fof(f718,plain,(
% 1.29/0.52    spl3_51 <=> r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK2)))),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 1.29/0.52  fof(f72,plain,(
% 1.29/0.52    spl3_1 <=> r1_tarski(sK1,sK2)),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.29/0.52  fof(f544,plain,(
% 1.29/0.52    spl3_44 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 1.29/0.52  fof(f716,plain,(
% 1.29/0.52    ~r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK2))) | (spl3_1 | ~spl3_44)),
% 1.29/0.52    inference(forward_demodulation,[],[f715,f68])).
% 1.29/0.52  fof(f68,plain,(
% 1.29/0.52    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 1.29/0.52    inference(definition_unfolding,[],[f51,f52,f52])).
% 1.29/0.52  fof(f51,plain,(
% 1.29/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f1])).
% 1.29/0.52  fof(f1,axiom,(
% 1.29/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.29/0.52  fof(f715,plain,(
% 1.29/0.52    ~r1_tarski(sK1,k3_tarski(k2_tarski(sK2,sK0))) | (spl3_1 | ~spl3_44)),
% 1.29/0.52    inference(forward_demodulation,[],[f703,f69])).
% 1.29/0.52  fof(f703,plain,(
% 1.29/0.52    ~r1_tarski(sK1,k3_tarski(k2_tarski(sK2,k4_xboole_0(sK0,sK2)))) | (spl3_1 | ~spl3_44)),
% 1.29/0.52    inference(unit_resulting_resolution,[],[f74,f545,f70])).
% 1.29/0.52  fof(f70,plain,(
% 1.29/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | r1_tarski(X0,X1) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 1.29/0.52    inference(definition_unfolding,[],[f66,f52])).
% 1.29/0.52  fof(f66,plain,(
% 1.29/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.29/0.52    inference(cnf_transformation,[],[f34])).
% 1.29/0.52  fof(f34,plain,(
% 1.29/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.29/0.52    inference(flattening,[],[f33])).
% 1.29/0.52  fof(f33,plain,(
% 1.29/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.29/0.52    inference(ennf_transformation,[],[f11])).
% 1.29/0.52  fof(f11,axiom,(
% 1.29/0.52    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 1.29/0.52  fof(f545,plain,(
% 1.29/0.52    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_44),
% 1.29/0.52    inference(avatar_component_clause,[],[f544])).
% 1.29/0.52  fof(f74,plain,(
% 1.29/0.52    ~r1_tarski(sK1,sK2) | spl3_1),
% 1.29/0.52    inference(avatar_component_clause,[],[f72])).
% 1.29/0.52  fof(f673,plain,(
% 1.29/0.52    spl3_44 | ~spl3_41),
% 1.29/0.52    inference(avatar_split_clause,[],[f670,f528,f544])).
% 1.29/0.52  fof(f528,plain,(
% 1.29/0.52    spl3_41 <=> r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 1.29/0.52  fof(f670,plain,(
% 1.29/0.52    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_41),
% 1.29/0.52    inference(resolution,[],[f530,f60])).
% 1.29/0.52  fof(f60,plain,(
% 1.29/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f27])).
% 1.29/0.52  fof(f27,plain,(
% 1.29/0.52    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.29/0.52    inference(ennf_transformation,[],[f3])).
% 1.29/0.52  fof(f3,axiom,(
% 1.29/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.29/0.52  fof(f530,plain,(
% 1.29/0.52    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl3_41),
% 1.29/0.52    inference(avatar_component_clause,[],[f528])).
% 1.29/0.52  fof(f650,plain,(
% 1.29/0.52    spl3_41 | ~spl3_42),
% 1.29/0.52    inference(avatar_split_clause,[],[f644,f533,f528])).
% 1.29/0.52  fof(f533,plain,(
% 1.29/0.52    spl3_42 <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 1.29/0.52  fof(f644,plain,(
% 1.29/0.52    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl3_42),
% 1.29/0.52    inference(resolution,[],[f535,f64])).
% 1.29/0.52  fof(f64,plain,(
% 1.29/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f30])).
% 1.29/0.52  fof(f30,plain,(
% 1.29/0.52    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.29/0.52    inference(ennf_transformation,[],[f4])).
% 1.29/0.52  fof(f4,axiom,(
% 1.29/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.29/0.52  fof(f535,plain,(
% 1.29/0.52    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl3_42),
% 1.29/0.52    inference(avatar_component_clause,[],[f533])).
% 1.29/0.52  fof(f634,plain,(
% 1.29/0.52    spl3_42 | ~spl3_2 | ~spl3_15 | ~spl3_16),
% 1.29/0.52    inference(avatar_split_clause,[],[f633,f201,f196,f76,f533])).
% 1.29/0.52  fof(f76,plain,(
% 1.29/0.52    spl3_2 <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.29/0.52  fof(f196,plain,(
% 1.29/0.52    spl3_15 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.29/0.52  fof(f201,plain,(
% 1.29/0.52    spl3_16 <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.29/0.52  fof(f633,plain,(
% 1.29/0.52    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | (~spl3_2 | ~spl3_15 | ~spl3_16)),
% 1.29/0.52    inference(forward_demodulation,[],[f632,f203])).
% 1.29/0.52  fof(f203,plain,(
% 1.29/0.52    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl3_16),
% 1.29/0.52    inference(avatar_component_clause,[],[f201])).
% 1.29/0.52  fof(f632,plain,(
% 1.29/0.52    r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | (~spl3_2 | ~spl3_15)),
% 1.29/0.52    inference(forward_demodulation,[],[f77,f198])).
% 1.29/0.52  fof(f198,plain,(
% 1.29/0.52    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_15),
% 1.29/0.52    inference(avatar_component_clause,[],[f196])).
% 1.29/0.52  fof(f77,plain,(
% 1.29/0.52    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~spl3_2),
% 1.29/0.52    inference(avatar_component_clause,[],[f76])).
% 1.29/0.52  fof(f576,plain,(
% 1.29/0.52    ~spl3_1 | spl3_42),
% 1.29/0.52    inference(avatar_contradiction_clause,[],[f570])).
% 1.29/0.52  fof(f570,plain,(
% 1.29/0.52    $false | (~spl3_1 | spl3_42)),
% 1.29/0.52    inference(unit_resulting_resolution,[],[f73,f534,f62])).
% 1.29/0.52  fof(f62,plain,(
% 1.29/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))) )),
% 1.29/0.52    inference(cnf_transformation,[],[f29])).
% 1.29/0.52  fof(f29,plain,(
% 1.29/0.52    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.29/0.52    inference(ennf_transformation,[],[f7])).
% 1.29/0.52  fof(f7,axiom,(
% 1.29/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
% 1.29/0.52  fof(f534,plain,(
% 1.29/0.52    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | spl3_42),
% 1.29/0.52    inference(avatar_component_clause,[],[f533])).
% 1.29/0.52  fof(f73,plain,(
% 1.29/0.52    r1_tarski(sK1,sK2) | ~spl3_1),
% 1.29/0.52    inference(avatar_component_clause,[],[f72])).
% 1.29/0.52  fof(f560,plain,(
% 1.29/0.52    ~spl3_42 | spl3_2 | ~spl3_15 | ~spl3_16),
% 1.29/0.52    inference(avatar_split_clause,[],[f559,f201,f196,f76,f533])).
% 1.29/0.52  fof(f559,plain,(
% 1.29/0.52    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | (spl3_2 | ~spl3_15 | ~spl3_16)),
% 1.29/0.52    inference(forward_demodulation,[],[f558,f203])).
% 1.29/0.52  fof(f558,plain,(
% 1.29/0.52    ~r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | (spl3_2 | ~spl3_15)),
% 1.29/0.52    inference(forward_demodulation,[],[f78,f198])).
% 1.29/0.52  fof(f78,plain,(
% 1.29/0.52    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | spl3_2),
% 1.29/0.52    inference(avatar_component_clause,[],[f76])).
% 1.29/0.52  fof(f220,plain,(
% 1.29/0.52    spl3_17 | ~spl3_6),
% 1.29/0.52    inference(avatar_split_clause,[],[f219,f105,f215])).
% 1.29/0.52  fof(f105,plain,(
% 1.29/0.52    spl3_6 <=> r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.29/0.52  fof(f219,plain,(
% 1.29/0.52    r1_tarski(sK2,sK0) | ~spl3_6),
% 1.29/0.52    inference(forward_demodulation,[],[f212,f46])).
% 1.29/0.52  fof(f46,plain,(
% 1.29/0.52    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.29/0.52    inference(cnf_transformation,[],[f15])).
% 1.29/0.52  fof(f15,axiom,(
% 1.29/0.52    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 1.29/0.52  fof(f212,plain,(
% 1.29/0.52    r1_tarski(sK2,k3_tarski(k1_zfmisc_1(sK0))) | ~spl3_6),
% 1.29/0.52    inference(resolution,[],[f107,f59])).
% 1.29/0.52  fof(f59,plain,(
% 1.29/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 1.29/0.52    inference(cnf_transformation,[],[f26])).
% 1.29/0.52  fof(f26,plain,(
% 1.29/0.52    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.29/0.52    inference(ennf_transformation,[],[f13])).
% 1.29/0.52  fof(f13,axiom,(
% 1.29/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.29/0.52  fof(f107,plain,(
% 1.29/0.52    r2_hidden(sK2,k1_zfmisc_1(sK0)) | ~spl3_6),
% 1.29/0.52    inference(avatar_component_clause,[],[f105])).
% 1.29/0.52  fof(f206,plain,(
% 1.29/0.52    spl3_15 | ~spl3_4),
% 1.29/0.52    inference(avatar_split_clause,[],[f194,f87,f196])).
% 1.29/0.52  fof(f87,plain,(
% 1.29/0.52    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.29/0.52  fof(f194,plain,(
% 1.29/0.52    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_4),
% 1.29/0.52    inference(resolution,[],[f61,f89])).
% 1.29/0.52  fof(f89,plain,(
% 1.29/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 1.29/0.52    inference(avatar_component_clause,[],[f87])).
% 1.29/0.52  fof(f61,plain,(
% 1.29/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f28])).
% 1.29/0.52  fof(f28,plain,(
% 1.29/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.52    inference(ennf_transformation,[],[f17])).
% 1.29/0.52  fof(f17,axiom,(
% 1.29/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.29/0.52  fof(f205,plain,(
% 1.29/0.52    spl3_16 | ~spl3_3),
% 1.29/0.52    inference(avatar_split_clause,[],[f193,f82,f201])).
% 1.29/0.52  fof(f82,plain,(
% 1.29/0.52    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.29/0.52  fof(f193,plain,(
% 1.29/0.52    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl3_3),
% 1.29/0.52    inference(resolution,[],[f61,f84])).
% 1.29/0.52  fof(f84,plain,(
% 1.29/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_3),
% 1.29/0.52    inference(avatar_component_clause,[],[f82])).
% 1.29/0.52  fof(f139,plain,(
% 1.29/0.52    spl3_10 | ~spl3_5),
% 1.29/0.52    inference(avatar_split_clause,[],[f138,f100,f134])).
% 1.29/0.52  fof(f134,plain,(
% 1.29/0.52    spl3_10 <=> r1_tarski(sK1,sK0)),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.29/0.52  fof(f100,plain,(
% 1.29/0.52    spl3_5 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.29/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.29/0.52  fof(f138,plain,(
% 1.29/0.52    r1_tarski(sK1,sK0) | ~spl3_5),
% 1.29/0.52    inference(forward_demodulation,[],[f131,f46])).
% 1.29/0.52  fof(f131,plain,(
% 1.29/0.52    r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0))) | ~spl3_5),
% 1.29/0.52    inference(resolution,[],[f102,f59])).
% 1.29/0.52  fof(f102,plain,(
% 1.29/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_5),
% 1.29/0.52    inference(avatar_component_clause,[],[f100])).
% 1.29/0.52  fof(f108,plain,(
% 1.29/0.52    spl3_6 | ~spl3_3),
% 1.29/0.52    inference(avatar_split_clause,[],[f95,f82,f105])).
% 1.29/0.52  fof(f95,plain,(
% 1.29/0.52    r2_hidden(sK2,k1_zfmisc_1(sK0)) | ~spl3_3),
% 1.29/0.52    inference(unit_resulting_resolution,[],[f45,f84,f54])).
% 1.29/0.52  fof(f54,plain,(
% 1.29/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.29/0.52    inference(cnf_transformation,[],[f40])).
% 1.29/0.52  fof(f40,plain,(
% 1.29/0.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.29/0.52    inference(nnf_transformation,[],[f23])).
% 1.29/0.52  fof(f23,plain,(
% 1.29/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.29/0.52    inference(ennf_transformation,[],[f16])).
% 1.29/0.52  fof(f16,axiom,(
% 1.29/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.29/0.52  fof(f45,plain,(
% 1.29/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.29/0.52    inference(cnf_transformation,[],[f18])).
% 1.29/0.52  fof(f18,axiom,(
% 1.29/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.29/0.52  fof(f103,plain,(
% 1.29/0.52    spl3_5 | ~spl3_4),
% 1.29/0.52    inference(avatar_split_clause,[],[f96,f87,f100])).
% 1.29/0.52  fof(f96,plain,(
% 1.29/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 1.29/0.52    inference(unit_resulting_resolution,[],[f45,f89,f54])).
% 1.29/0.52  fof(f90,plain,(
% 1.29/0.52    spl3_4),
% 1.29/0.52    inference(avatar_split_clause,[],[f41,f87])).
% 1.29/0.52  fof(f41,plain,(
% 1.29/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.29/0.52    inference(cnf_transformation,[],[f39])).
% 1.29/0.52  fof(f39,plain,(
% 1.29/0.52    ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.29/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f38,f37])).
% 1.29/0.52  fof(f37,plain,(
% 1.29/0.52    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.29/0.52    introduced(choice_axiom,[])).
% 1.29/0.52  fof(f38,plain,(
% 1.29/0.52    ? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.29/0.52    introduced(choice_axiom,[])).
% 1.29/0.52  fof(f36,plain,(
% 1.29/0.52    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.52    inference(flattening,[],[f35])).
% 1.29/0.52  fof(f35,plain,(
% 1.29/0.52    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.52    inference(nnf_transformation,[],[f21])).
% 1.29/0.52  fof(f21,plain,(
% 1.29/0.52    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.29/0.52    inference(ennf_transformation,[],[f20])).
% 1.29/0.52  fof(f20,negated_conjecture,(
% 1.29/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.29/0.52    inference(negated_conjecture,[],[f19])).
% 1.29/0.52  fof(f19,conjecture,(
% 1.29/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 1.29/0.52  fof(f85,plain,(
% 1.29/0.52    spl3_3),
% 1.29/0.52    inference(avatar_split_clause,[],[f42,f82])).
% 1.29/0.52  fof(f42,plain,(
% 1.29/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.29/0.52    inference(cnf_transformation,[],[f39])).
% 1.29/0.52  fof(f80,plain,(
% 1.29/0.52    spl3_1 | spl3_2),
% 1.29/0.52    inference(avatar_split_clause,[],[f43,f76,f72])).
% 1.29/0.52  fof(f43,plain,(
% 1.29/0.52    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 1.29/0.52    inference(cnf_transformation,[],[f39])).
% 1.29/0.52  fof(f79,plain,(
% 1.29/0.52    ~spl3_1 | ~spl3_2),
% 1.29/0.52    inference(avatar_split_clause,[],[f44,f76,f72])).
% 1.29/0.52  fof(f44,plain,(
% 1.29/0.52    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 1.29/0.52    inference(cnf_transformation,[],[f39])).
% 1.29/0.52  % SZS output end Proof for theBenchmark
% 1.29/0.52  % (17690)------------------------------
% 1.29/0.52  % (17690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.52  % (17690)Termination reason: Refutation
% 1.29/0.52  
% 1.29/0.52  % (17690)Memory used [KB]: 7675
% 1.29/0.52  % (17690)Time elapsed: 0.075 s
% 1.29/0.52  % (17690)------------------------------
% 1.29/0.52  % (17690)------------------------------
% 1.29/0.52  % (17683)Success in time 0.164 s
%------------------------------------------------------------------------------
