%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:51 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 184 expanded)
%              Number of leaves         :   27 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :  237 ( 413 expanded)
%              Number of equality atoms :   34 (  78 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f628,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f250,f264,f271,f294,f303,f308,f317,f561,f573,f626])).

fof(f626,plain,
    ( spl5_13
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f377,f74,f137])).

fof(f137,plain,
    ( spl5_13
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f74,plain,
    ( spl5_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f377,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f241,f76])).

fof(f76,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f241,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(global_subsumption,[],[f33,f240])).

fof(f240,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ) ),
    inference(forward_demodulation,[],[f235,f52])).

fof(f52,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f32,f51])).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f34,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f32,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f235,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
      | r1_tarski(X0,k3_subset_1(X1,k1_xboole_0)) ) ),
    inference(resolution,[],[f45,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X2,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f573,plain,
    ( spl5_1
    | ~ spl5_31
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f572,f558,f300,f59])).

fof(f59,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f300,plain,
    ( spl5_31
  <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f558,plain,
    ( spl5_58
  <=> sK0 = k3_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f572,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_31
    | ~ spl5_58 ),
    inference(forward_demodulation,[],[f563,f172])).

fof(f172,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f165,f52])).

fof(f165,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f42,f33])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f563,plain,
    ( sK1 = k3_subset_1(sK0,sK0)
    | ~ spl5_31
    | ~ spl5_58 ),
    inference(backward_demodulation,[],[f302,f560])).

fof(f560,plain,
    ( sK0 = k3_subset_1(sK0,sK1)
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f558])).

fof(f302,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f300])).

fof(f561,plain,
    ( spl5_58
    | ~ spl5_32
    | ~ spl5_33
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f548,f300,f314,f305,f558])).

fof(f305,plain,
    ( spl5_32
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f314,plain,
    ( spl5_33
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f548,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | sK0 = k3_subset_1(sK0,sK1)
    | ~ spl5_31 ),
    inference(superposition,[],[f201,f302])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1 ) ),
    inference(forward_demodulation,[],[f53,f52])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k1_xboole_0) = X1
      | ~ r1_tarski(k3_subset_1(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f44,f51])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_subset_1(X0) = X1
      | ~ r1_tarski(k3_subset_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f317,plain,
    ( spl5_33
    | ~ spl5_3
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f309,f243,f69,f314])).

fof(f69,plain,
    ( spl5_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f243,plain,
    ( spl5_23
  <=> r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f309,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ spl5_3
    | ~ spl5_23 ),
    inference(resolution,[],[f245,f142])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f50,f71])).

fof(f71,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f245,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f243])).

fof(f308,plain,
    ( spl5_32
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f296,f247,f305])).

fof(f247,plain,
    ( spl5_24
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f296,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_24 ),
    inference(resolution,[],[f248,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f248,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f247])).

fof(f303,plain,
    ( spl5_31
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f295,f247,f300])).

fof(f295,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl5_24 ),
    inference(resolution,[],[f248,f42])).

fof(f294,plain,
    ( spl5_24
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f292,f268,f247])).

fof(f268,plain,
    ( spl5_27
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f292,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_27 ),
    inference(resolution,[],[f270,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f36,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f270,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f268])).

fof(f271,plain,
    ( spl5_27
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f266,f261,f268])).

fof(f261,plain,
    ( spl5_26
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f266,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_26 ),
    inference(resolution,[],[f263,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f263,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f261])).

fof(f264,plain,
    ( spl5_26
    | ~ spl5_3
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f259,f137,f69,f261])).

fof(f259,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_3
    | ~ spl5_13 ),
    inference(resolution,[],[f142,f139])).

fof(f139,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f250,plain,
    ( spl5_23
    | ~ spl5_24
    | ~ spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f236,f64,f74,f247,f243])).

fof(f64,plain,
    ( spl5_2
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f236,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ spl5_2 ),
    inference(resolution,[],[f45,f66])).

fof(f66,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f77,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f26,f74])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(f72,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f27,f69])).

fof(f27,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:32:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (11789)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (11779)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (11777)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (11795)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (11781)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (11778)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (11793)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (11797)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (11805)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (11782)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (11804)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (11780)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (11794)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.55  % (11785)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.55  % (11796)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.55  % (11807)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.43/0.55  % (11802)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.55  % (11787)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.56  % (11799)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.43/0.56  % (11788)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.43/0.56  % (11798)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.56  % (11786)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.43/0.56  % (11792)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.43/0.56  % (11791)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.43/0.56  % (11784)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.43/0.56  % (11783)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.43/0.56  % (11790)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.43/0.56  % (11799)Refutation not found, incomplete strategy% (11799)------------------------------
% 1.43/0.56  % (11799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (11799)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (11799)Memory used [KB]: 10746
% 1.43/0.56  % (11799)Time elapsed: 0.073 s
% 1.43/0.56  % (11799)------------------------------
% 1.43/0.56  % (11799)------------------------------
% 1.43/0.57  % (11793)Refutation found. Thanks to Tanya!
% 1.43/0.57  % SZS status Theorem for theBenchmark
% 1.43/0.57  % SZS output start Proof for theBenchmark
% 1.43/0.57  fof(f628,plain,(
% 1.43/0.57    $false),
% 1.43/0.57    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f250,f264,f271,f294,f303,f308,f317,f561,f573,f626])).
% 1.43/0.57  fof(f626,plain,(
% 1.43/0.57    spl5_13 | ~spl5_4),
% 1.43/0.57    inference(avatar_split_clause,[],[f377,f74,f137])).
% 1.43/0.57  fof(f137,plain,(
% 1.43/0.57    spl5_13 <=> r1_tarski(sK2,sK0)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.43/0.57  fof(f74,plain,(
% 1.43/0.57    spl5_4 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.43/0.57  fof(f377,plain,(
% 1.43/0.57    r1_tarski(sK2,sK0) | ~spl5_4),
% 1.43/0.57    inference(resolution,[],[f241,f76])).
% 1.43/0.57  fof(f76,plain,(
% 1.43/0.57    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl5_4),
% 1.43/0.57    inference(avatar_component_clause,[],[f74])).
% 1.43/0.57  fof(f241,plain,(
% 1.43/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.43/0.57    inference(global_subsumption,[],[f33,f240])).
% 1.43/0.57  fof(f240,plain,(
% 1.43/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))) )),
% 1.43/0.57    inference(forward_demodulation,[],[f235,f52])).
% 1.43/0.57  fof(f52,plain,(
% 1.43/0.57    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.43/0.57    inference(definition_unfolding,[],[f32,f51])).
% 1.43/0.57  fof(f51,plain,(
% 1.43/0.57    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.43/0.57    inference(definition_unfolding,[],[f34,f31])).
% 1.43/0.57  fof(f31,plain,(
% 1.43/0.57    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f6])).
% 1.43/0.57  fof(f6,axiom,(
% 1.43/0.57    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.43/0.57  fof(f34,plain,(
% 1.43/0.57    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f10])).
% 1.43/0.57  fof(f10,axiom,(
% 1.43/0.57    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 1.43/0.57  fof(f32,plain,(
% 1.43/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.43/0.57    inference(cnf_transformation,[],[f7])).
% 1.43/0.57  fof(f7,axiom,(
% 1.43/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.43/0.57  fof(f235,plain,(
% 1.43/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | r1_tarski(X0,k3_subset_1(X1,k1_xboole_0))) )),
% 1.43/0.57    inference(resolution,[],[f45,f30])).
% 1.43/0.57  fof(f30,plain,(
% 1.43/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f3])).
% 1.43/0.57  fof(f3,axiom,(
% 1.43/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.43/0.57  fof(f45,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X2,k3_subset_1(X0,X1))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f23])).
% 1.43/0.57  fof(f23,plain,(
% 1.43/0.57    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.43/0.57    inference(flattening,[],[f22])).
% 1.43/0.57  fof(f22,plain,(
% 1.43/0.57    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.43/0.57    inference(ennf_transformation,[],[f11])).
% 1.43/0.57  fof(f11,axiom,(
% 1.43/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).
% 1.43/0.57  fof(f33,plain,(
% 1.43/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f13])).
% 1.43/0.57  fof(f13,axiom,(
% 1.43/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.43/0.57  fof(f573,plain,(
% 1.43/0.57    spl5_1 | ~spl5_31 | ~spl5_58),
% 1.43/0.57    inference(avatar_split_clause,[],[f572,f558,f300,f59])).
% 1.43/0.57  fof(f59,plain,(
% 1.43/0.57    spl5_1 <=> k1_xboole_0 = sK1),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.43/0.57  fof(f300,plain,(
% 1.43/0.57    spl5_31 <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 1.43/0.57  fof(f558,plain,(
% 1.43/0.57    spl5_58 <=> sK0 = k3_subset_1(sK0,sK1)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 1.43/0.57  fof(f572,plain,(
% 1.43/0.57    k1_xboole_0 = sK1 | (~spl5_31 | ~spl5_58)),
% 1.43/0.57    inference(forward_demodulation,[],[f563,f172])).
% 1.43/0.57  fof(f172,plain,(
% 1.43/0.57    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.43/0.57    inference(forward_demodulation,[],[f165,f52])).
% 1.43/0.57  fof(f165,plain,(
% 1.43/0.57    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 1.43/0.57    inference(resolution,[],[f42,f33])).
% 1.43/0.57  fof(f42,plain,(
% 1.43/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.43/0.57    inference(cnf_transformation,[],[f20])).
% 1.43/0.57  fof(f20,plain,(
% 1.43/0.57    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.43/0.57    inference(ennf_transformation,[],[f9])).
% 1.43/0.57  fof(f9,axiom,(
% 1.43/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.43/0.57  fof(f563,plain,(
% 1.43/0.57    sK1 = k3_subset_1(sK0,sK0) | (~spl5_31 | ~spl5_58)),
% 1.43/0.57    inference(backward_demodulation,[],[f302,f560])).
% 1.43/0.57  fof(f560,plain,(
% 1.43/0.57    sK0 = k3_subset_1(sK0,sK1) | ~spl5_58),
% 1.43/0.57    inference(avatar_component_clause,[],[f558])).
% 1.43/0.57  fof(f302,plain,(
% 1.43/0.57    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl5_31),
% 1.43/0.57    inference(avatar_component_clause,[],[f300])).
% 1.43/0.57  fof(f561,plain,(
% 1.43/0.57    spl5_58 | ~spl5_32 | ~spl5_33 | ~spl5_31),
% 1.43/0.57    inference(avatar_split_clause,[],[f548,f300,f314,f305,f558])).
% 1.43/0.57  fof(f305,plain,(
% 1.43/0.57    spl5_32 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 1.43/0.57  fof(f314,plain,(
% 1.43/0.57    spl5_33 <=> r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 1.43/0.57  fof(f548,plain,(
% 1.43/0.57    ~r1_tarski(sK1,k3_subset_1(sK0,sK1)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | sK0 = k3_subset_1(sK0,sK1) | ~spl5_31),
% 1.43/0.57    inference(superposition,[],[f201,f302])).
% 1.43/0.57  fof(f201,plain,(
% 1.43/0.57    ( ! [X0,X1] : (~r1_tarski(k3_subset_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1) )),
% 1.43/0.57    inference(forward_demodulation,[],[f53,f52])).
% 1.43/0.57  fof(f53,plain,(
% 1.43/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k1_xboole_0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) )),
% 1.43/0.57    inference(definition_unfolding,[],[f44,f51])).
% 1.43/0.57  fof(f44,plain,(
% 1.43/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f21])).
% 1.43/0.57  fof(f21,plain,(
% 1.43/0.57    ! [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.43/0.57    inference(ennf_transformation,[],[f12])).
% 1.43/0.57  fof(f12,axiom,(
% 1.43/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 1.43/0.57  fof(f317,plain,(
% 1.43/0.57    spl5_33 | ~spl5_3 | ~spl5_23),
% 1.43/0.57    inference(avatar_split_clause,[],[f309,f243,f69,f314])).
% 1.43/0.57  fof(f69,plain,(
% 1.43/0.57    spl5_3 <=> r1_tarski(sK1,sK2)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.43/0.57  fof(f243,plain,(
% 1.43/0.57    spl5_23 <=> r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.43/0.57  fof(f309,plain,(
% 1.43/0.57    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | (~spl5_3 | ~spl5_23)),
% 1.43/0.57    inference(resolution,[],[f245,f142])).
% 1.43/0.57  fof(f142,plain,(
% 1.43/0.57    ( ! [X0] : (~r1_tarski(sK2,X0) | r1_tarski(sK1,X0)) ) | ~spl5_3),
% 1.43/0.57    inference(resolution,[],[f50,f71])).
% 1.43/0.57  fof(f71,plain,(
% 1.43/0.57    r1_tarski(sK1,sK2) | ~spl5_3),
% 1.43/0.57    inference(avatar_component_clause,[],[f69])).
% 1.43/0.57  fof(f50,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f25])).
% 1.43/0.57  fof(f25,plain,(
% 1.43/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.43/0.57    inference(flattening,[],[f24])).
% 1.43/0.57  fof(f24,plain,(
% 1.43/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.43/0.57    inference(ennf_transformation,[],[f2])).
% 1.43/0.57  fof(f2,axiom,(
% 1.43/0.57    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.43/0.57  fof(f245,plain,(
% 1.43/0.57    r1_tarski(sK2,k3_subset_1(sK0,sK1)) | ~spl5_23),
% 1.43/0.57    inference(avatar_component_clause,[],[f243])).
% 1.43/0.57  fof(f308,plain,(
% 1.43/0.57    spl5_32 | ~spl5_24),
% 1.43/0.57    inference(avatar_split_clause,[],[f296,f247,f305])).
% 1.43/0.57  fof(f247,plain,(
% 1.43/0.57    spl5_24 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.43/0.57  fof(f296,plain,(
% 1.43/0.57    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl5_24),
% 1.43/0.57    inference(resolution,[],[f248,f41])).
% 1.43/0.57  fof(f41,plain,(
% 1.43/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f19])).
% 1.43/0.57  fof(f19,plain,(
% 1.43/0.57    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.43/0.57    inference(ennf_transformation,[],[f8])).
% 1.43/0.57  fof(f8,axiom,(
% 1.43/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.43/0.57  fof(f248,plain,(
% 1.43/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_24),
% 1.43/0.57    inference(avatar_component_clause,[],[f247])).
% 1.43/0.57  fof(f303,plain,(
% 1.43/0.57    spl5_31 | ~spl5_24),
% 1.43/0.57    inference(avatar_split_clause,[],[f295,f247,f300])).
% 1.43/0.57  fof(f295,plain,(
% 1.43/0.57    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl5_24),
% 1.43/0.57    inference(resolution,[],[f248,f42])).
% 1.43/0.57  fof(f294,plain,(
% 1.43/0.57    spl5_24 | ~spl5_27),
% 1.43/0.57    inference(avatar_split_clause,[],[f292,f268,f247])).
% 1.43/0.57  fof(f268,plain,(
% 1.43/0.57    spl5_27 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.43/0.57  fof(f292,plain,(
% 1.43/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_27),
% 1.43/0.57    inference(resolution,[],[f270,f78])).
% 1.43/0.57  fof(f78,plain,(
% 1.43/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.43/0.57    inference(global_subsumption,[],[f36,f39])).
% 1.43/0.57  fof(f39,plain,(
% 1.43/0.57    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f18])).
% 1.43/0.57  fof(f18,plain,(
% 1.43/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.43/0.57    inference(ennf_transformation,[],[f5])).
% 1.43/0.57  fof(f5,axiom,(
% 1.43/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.43/0.57  fof(f36,plain,(
% 1.43/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f1])).
% 1.43/0.57  fof(f1,axiom,(
% 1.43/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.43/0.57  fof(f270,plain,(
% 1.43/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl5_27),
% 1.43/0.57    inference(avatar_component_clause,[],[f268])).
% 1.43/0.57  fof(f271,plain,(
% 1.43/0.57    spl5_27 | ~spl5_26),
% 1.43/0.57    inference(avatar_split_clause,[],[f266,f261,f268])).
% 1.43/0.57  fof(f261,plain,(
% 1.43/0.57    spl5_26 <=> r1_tarski(sK1,sK0)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.43/0.57  fof(f266,plain,(
% 1.43/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl5_26),
% 1.43/0.57    inference(resolution,[],[f263,f57])).
% 1.43/0.57  fof(f57,plain,(
% 1.43/0.57    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 1.43/0.57    inference(equality_resolution,[],[f46])).
% 1.43/0.57  fof(f46,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.43/0.57    inference(cnf_transformation,[],[f4])).
% 1.43/0.57  fof(f4,axiom,(
% 1.43/0.57    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.43/0.57  fof(f263,plain,(
% 1.43/0.57    r1_tarski(sK1,sK0) | ~spl5_26),
% 1.43/0.57    inference(avatar_component_clause,[],[f261])).
% 1.43/0.57  fof(f264,plain,(
% 1.43/0.57    spl5_26 | ~spl5_3 | ~spl5_13),
% 1.43/0.57    inference(avatar_split_clause,[],[f259,f137,f69,f261])).
% 1.43/0.57  fof(f259,plain,(
% 1.43/0.57    r1_tarski(sK1,sK0) | (~spl5_3 | ~spl5_13)),
% 1.43/0.57    inference(resolution,[],[f142,f139])).
% 1.43/0.57  fof(f139,plain,(
% 1.43/0.57    r1_tarski(sK2,sK0) | ~spl5_13),
% 1.43/0.57    inference(avatar_component_clause,[],[f137])).
% 1.43/0.57  fof(f250,plain,(
% 1.43/0.57    spl5_23 | ~spl5_24 | ~spl5_4 | ~spl5_2),
% 1.43/0.57    inference(avatar_split_clause,[],[f236,f64,f74,f247,f243])).
% 1.43/0.57  fof(f64,plain,(
% 1.43/0.57    spl5_2 <=> r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.43/0.57  fof(f236,plain,(
% 1.43/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | r1_tarski(sK2,k3_subset_1(sK0,sK1)) | ~spl5_2),
% 1.43/0.57    inference(resolution,[],[f45,f66])).
% 1.43/0.57  fof(f66,plain,(
% 1.43/0.57    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~spl5_2),
% 1.43/0.57    inference(avatar_component_clause,[],[f64])).
% 1.43/0.57  fof(f77,plain,(
% 1.43/0.57    spl5_4),
% 1.43/0.57    inference(avatar_split_clause,[],[f26,f74])).
% 1.43/0.57  fof(f26,plain,(
% 1.43/0.57    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.43/0.57    inference(cnf_transformation,[],[f17])).
% 1.43/0.57  fof(f17,plain,(
% 1.43/0.57    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.43/0.57    inference(flattening,[],[f16])).
% 1.43/0.57  fof(f16,plain,(
% 1.43/0.57    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.43/0.57    inference(ennf_transformation,[],[f15])).
% 1.43/0.57  fof(f15,negated_conjecture,(
% 1.43/0.57    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.43/0.57    inference(negated_conjecture,[],[f14])).
% 1.43/0.57  fof(f14,conjecture,(
% 1.43/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).
% 1.43/0.57  fof(f72,plain,(
% 1.43/0.57    spl5_3),
% 1.43/0.57    inference(avatar_split_clause,[],[f27,f69])).
% 1.43/0.57  fof(f27,plain,(
% 1.43/0.57    r1_tarski(sK1,sK2)),
% 1.43/0.57    inference(cnf_transformation,[],[f17])).
% 1.43/0.57  fof(f67,plain,(
% 1.43/0.57    spl5_2),
% 1.43/0.57    inference(avatar_split_clause,[],[f28,f64])).
% 1.43/0.57  fof(f28,plain,(
% 1.43/0.57    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.43/0.57    inference(cnf_transformation,[],[f17])).
% 1.43/0.57  fof(f62,plain,(
% 1.43/0.57    ~spl5_1),
% 1.43/0.57    inference(avatar_split_clause,[],[f29,f59])).
% 1.43/0.57  fof(f29,plain,(
% 1.43/0.57    k1_xboole_0 != sK1),
% 1.43/0.57    inference(cnf_transformation,[],[f17])).
% 1.43/0.57  % SZS output end Proof for theBenchmark
% 1.43/0.57  % (11793)------------------------------
% 1.43/0.57  % (11793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (11793)Termination reason: Refutation
% 1.43/0.57  
% 1.43/0.57  % (11793)Memory used [KB]: 11129
% 1.43/0.57  % (11793)Time elapsed: 0.153 s
% 1.43/0.57  % (11793)------------------------------
% 1.43/0.57  % (11793)------------------------------
% 1.43/0.57  % (11800)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.43/0.57  % (11794)Refutation not found, incomplete strategy% (11794)------------------------------
% 1.43/0.57  % (11794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (11794)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.57  
% 1.43/0.57  % (11794)Memory used [KB]: 10618
% 1.43/0.57  % (11794)Time elapsed: 0.158 s
% 1.43/0.57  % (11794)------------------------------
% 1.43/0.57  % (11794)------------------------------
% 1.43/0.57  % (11806)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.61/0.58  % (11803)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.61/0.58  % (11772)Success in time 0.21 s
%------------------------------------------------------------------------------
