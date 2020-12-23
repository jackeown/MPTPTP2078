%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:24 EST 2020

% Result     : Theorem 3.48s
% Output     : Refutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  250 ( 626 expanded)
%              Number of leaves         :   54 ( 236 expanded)
%              Depth                    :   13
%              Number of atoms          :  655 (1685 expanded)
%              Number of equality atoms :   91 ( 259 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5398,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f101,f106,f111,f116,f121,f126,f131,f136,f311,f323,f337,f361,f424,f497,f541,f701,f731,f743,f751,f772,f818,f1106,f3125,f4006,f4043,f4078,f4356,f4621,f5329,f5334,f5348,f5397])).

fof(f5397,plain,
    ( spl8_188
    | ~ spl8_44
    | ~ spl8_187 ),
    inference(avatar_split_clause,[],[f5390,f5326,f815,f5331])).

fof(f5331,plain,
    ( spl8_188
  <=> r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_188])])).

fof(f815,plain,
    ( spl8_44
  <=> r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f5326,plain,
    ( spl8_187
  <=> k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_187])])).

fof(f5390,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_tarski(k1_xboole_0))
    | ~ spl8_187 ),
    inference(superposition,[],[f68,f5328])).

fof(f5328,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0),k1_tarski(k1_xboole_0))
    | ~ spl8_187 ),
    inference(avatar_component_clause,[],[f5326])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f5348,plain,
    ( k1_tarski(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | sK1 != k7_subset_1(sK1,sK1,k1_zfmisc_1(k1_xboole_0))
    | sK1 = k7_subset_1(sK1,sK1,k1_tarski(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f5334,plain,
    ( spl8_186
    | spl8_22
    | ~ spl8_188
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f5315,f358,f5331,f413,f5322])).

fof(f5322,plain,
    ( spl8_186
  <=> k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_186])])).

fof(f413,plain,
    ( spl8_22
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f358,plain,
    ( spl8_21
  <=> k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f5315,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_tarski(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | ~ spl8_21 ),
    inference(superposition,[],[f899,f360])).

fof(f360,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f358])).

fof(f899,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_tarski(sK2(X0)))
      | v1_xboole_0(X0)
      | k1_tarski(sK2(X0)) = X0 ) ),
    inference(resolution,[],[f386,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f386,plain,(
    ! [X2] :
      ( r1_tarski(k1_tarski(sK2(X2)),X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f179,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f179,plain,(
    ! [X2] :
      ( m1_subset_1(k1_tarski(sK2(X2)),k1_zfmisc_1(X2))
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f62,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f5329,plain,
    ( spl8_22
    | spl8_186
    | spl8_187
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f5320,f358,f5326,f5322,f413])).

fof(f5320,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0),k1_tarski(k1_xboole_0))
    | k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f5319,f360])).

fof(f5319,plain,
    ( k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0),k1_tarski(sK2(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f5311,f360])).

fof(f5311,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(sK2(k1_zfmisc_1(k1_xboole_0)))
    | k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0),k1_tarski(sK2(k1_zfmisc_1(k1_xboole_0)))) ),
    inference(resolution,[],[f899,f511])).

fof(f511,plain,(
    ! [X8] :
      ( r1_tarski(k1_zfmisc_1(k1_xboole_0),X8)
      | k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0),X8) ) ),
    inference(resolution,[],[f186,f214])).

fof(f214,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f65,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f186,plain,(
    ! [X6,X7] :
      ( r1_tarski(sK5(k1_zfmisc_1(X6),X7),X6)
      | r1_tarski(k1_zfmisc_1(X6),X7) ) ),
    inference(resolution,[],[f67,f88])).

fof(f88,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4621,plain,
    ( spl8_151
    | ~ spl8_146 ),
    inference(avatar_split_clause,[],[f4616,f4353,f4618])).

fof(f4618,plain,
    ( spl8_151
  <=> sK1 = k7_subset_1(sK1,sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_151])])).

fof(f4353,plain,
    ( spl8_146
  <=> k1_xboole_0 = k3_xboole_0(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_146])])).

fof(f4616,plain,
    ( sK1 = k7_subset_1(sK1,sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_146 ),
    inference(forward_demodulation,[],[f4614,f250])).

fof(f250,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f82,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f82,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f48,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f4614,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k7_subset_1(sK1,sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_146 ),
    inference(superposition,[],[f288,f4355])).

fof(f4355,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_146 ),
    inference(avatar_component_clause,[],[f4353])).

fof(f288,plain,(
    ! [X2,X3] : k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(resolution,[],[f85,f139])).

fof(f139,plain,(
    ! [X1] : m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(resolution,[],[f73,f86])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f75,f56])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f4356,plain,
    ( spl8_146
    | ~ spl8_121 ),
    inference(avatar_split_clause,[],[f4343,f4075,f4353])).

fof(f4075,plain,
    ( spl8_121
  <=> r1_xboole_0(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_121])])).

fof(f4343,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_121 ),
    inference(resolution,[],[f4098,f214])).

fof(f4098,plain,
    ( ! [X2] : r1_tarski(k3_xboole_0(sK1,k1_zfmisc_1(k1_xboole_0)),X2)
    | ~ spl8_121 ),
    inference(resolution,[],[f4077,f187])).

fof(f187,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_xboole_0(X8,X9)
      | r1_tarski(k3_xboole_0(X8,X9),X10) ) ),
    inference(resolution,[],[f67,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f4077,plain,
    ( r1_xboole_0(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_121 ),
    inference(avatar_component_clause,[],[f4075])).

fof(f4078,plain,
    ( spl8_121
    | ~ spl8_114 ),
    inference(avatar_split_clause,[],[f4062,f4022,f4075])).

fof(f4022,plain,
    ( spl8_114
  <=> r1_xboole_0(k1_zfmisc_1(k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_114])])).

fof(f4062,plain,
    ( r1_xboole_0(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_114 ),
    inference(resolution,[],[f4024,f582])).

fof(f582,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f578])).

fof(f578,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0)
      | r1_xboole_0(X1,X0) ) ),
    inference(resolution,[],[f200,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f200,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(sK4(X9,X10),X11)
      | ~ r1_xboole_0(X10,X11)
      | r1_xboole_0(X9,X10) ) ),
    inference(resolution,[],[f59,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4024,plain,
    ( r1_xboole_0(k1_zfmisc_1(k1_xboole_0),sK1)
    | ~ spl8_114 ),
    inference(avatar_component_clause,[],[f4022])).

fof(f4043,plain,
    ( spl8_114
    | ~ spl8_9
    | ~ spl8_113 ),
    inference(avatar_split_clause,[],[f4018,f4003,f133,f4022])).

fof(f133,plain,
    ( spl8_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f4003,plain,
    ( spl8_113
  <=> k1_xboole_0 = k3_xboole_0(k1_zfmisc_1(k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).

fof(f4018,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | r1_xboole_0(k1_zfmisc_1(k1_xboole_0),sK1)
    | ~ spl8_113 ),
    inference(superposition,[],[f266,f4005])).

fof(f4005,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_zfmisc_1(k1_xboole_0),sK1)
    | ~ spl8_113 ),
    inference(avatar_component_clause,[],[f4003])).

fof(f266,plain,(
    ! [X12,X13] :
      ( ~ v1_xboole_0(k3_xboole_0(X12,X13))
      | r1_xboole_0(X12,X13) ) ),
    inference(resolution,[],[f58,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4006,plain,
    ( spl8_113
    | ~ spl8_17
    | spl8_18 ),
    inference(avatar_split_clause,[],[f4001,f316,f309,f4003])).

fof(f309,plain,
    ( spl8_17
  <=> ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f316,plain,
    ( spl8_18
  <=> sP7(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f4001,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_zfmisc_1(k1_xboole_0),sK1)
    | ~ spl8_17
    | spl8_18 ),
    inference(resolution,[],[f3825,f318])).

fof(f318,plain,
    ( ~ sP7(sK1)
    | spl8_18 ),
    inference(avatar_component_clause,[],[f316])).

fof(f3825,plain,
    ( ! [X28] :
        ( sP7(X28)
        | k1_xboole_0 = k3_xboole_0(k1_zfmisc_1(k1_xboole_0),X28) )
    | ~ spl8_17 ),
    inference(resolution,[],[f3598,f214])).

fof(f3598,plain,
    ( ! [X8,X7] :
        ( r1_tarski(k3_xboole_0(k1_zfmisc_1(k1_xboole_0),X7),X8)
        | sP7(X7) )
    | ~ spl8_17 ),
    inference(resolution,[],[f3553,f187])).

fof(f3553,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X0)
        | sP7(X0) )
    | ~ spl8_17 ),
    inference(duplicate_literal_removal,[],[f3535])).

fof(f3535,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X0)
        | r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X0)
        | sP7(X0) )
    | ~ spl8_17 ),
    inference(resolution,[],[f1694,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(sK4(X0,X1))
      | r1_xboole_0(X0,X1)
      | sP7(X1) ) ),
    inference(resolution,[],[f61,f90])).

fof(f90,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X2)
      | sP7(X1) ) ),
    inference(cnf_transformation,[],[f90_D])).

fof(f90_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ v1_xboole_0(X2) )
    <=> ~ sP7(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f1694,plain,
    ( ! [X14] :
        ( v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0),X14))
        | r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X14) )
    | ~ spl8_17 ),
    inference(resolution,[],[f458,f310])).

fof(f310,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_xboole_0)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f309])).

fof(f458,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(sK4(k1_zfmisc_1(X0),X1)),X0)
      | r1_xboole_0(k1_zfmisc_1(X0),X1)
      | v1_xboole_0(sK4(k1_zfmisc_1(X0),X1)) ) ),
    inference(resolution,[],[f169,f244])).

fof(f244,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | r2_hidden(sK2(X8),X9)
      | v1_xboole_0(X8) ) ),
    inference(resolution,[],[f66,f53])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f169,plain,(
    ! [X4,X5] :
      ( r1_tarski(sK4(k1_zfmisc_1(X4),X5),X4)
      | r1_xboole_0(k1_zfmisc_1(X4),X5) ) ),
    inference(resolution,[],[f60,f88])).

fof(f3125,plain,
    ( spl8_2
    | ~ spl8_1
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f3113,f320,f93,f98])).

fof(f98,plain,
    ( spl8_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f93,plain,
    ( spl8_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f320,plain,
    ( spl8_19
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f3113,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_19 ),
    inference(resolution,[],[f322,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f322,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f320])).

fof(f1106,plain,
    ( ~ spl8_57
    | spl8_38 ),
    inference(avatar_split_clause,[],[f1089,f740,f1103])).

fof(f1103,plain,
    ( spl8_57
  <=> sK1 = k7_subset_1(sK1,sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f740,plain,
    ( spl8_38
  <=> sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f1089,plain,
    ( sK1 != k7_subset_1(sK1,sK1,k1_tarski(k1_xboole_0))
    | spl8_38 ),
    inference(superposition,[],[f742,f288])).

fof(f742,plain,
    ( sK1 != k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0)))
    | spl8_38 ),
    inference(avatar_component_clause,[],[f740])).

fof(f818,plain,
    ( spl8_24
    | spl8_44
    | ~ spl8_41 ),
    inference(avatar_split_clause,[],[f809,f769,f815,f433])).

fof(f433,plain,
    ( spl8_24
  <=> v1_xboole_0(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f769,plain,
    ( spl8_41
  <=> k1_xboole_0 = sK2(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f809,plain,
    ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | v1_xboole_0(k1_tarski(k1_xboole_0))
    | ~ spl8_41 ),
    inference(superposition,[],[f53,f771])).

fof(f771,plain,
    ( k1_xboole_0 = sK2(k1_tarski(k1_xboole_0))
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f769])).

fof(f772,plain,
    ( spl8_41
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f759,f437,f769])).

fof(f437,plain,
    ( spl8_25
  <=> ! [X6] : r2_hidden(sK2(k1_tarski(k1_xboole_0)),k1_zfmisc_1(X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f759,plain,
    ( k1_xboole_0 = sK2(k1_tarski(k1_xboole_0))
    | ~ spl8_25 ),
    inference(resolution,[],[f475,f214])).

fof(f475,plain,
    ( ! [X1] : r1_tarski(sK2(k1_tarski(k1_xboole_0)),X1)
    | ~ spl8_25 ),
    inference(resolution,[],[f438,f88])).

fof(f438,plain,
    ( ! [X6] : r2_hidden(sK2(k1_tarski(k1_xboole_0)),k1_zfmisc_1(X6))
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f437])).

fof(f751,plain,
    ( spl8_24
    | spl8_25 ),
    inference(avatar_split_clause,[],[f747,f437,f433])).

fof(f747,plain,(
    ! [X3] :
      ( r2_hidden(sK2(k1_tarski(k1_xboole_0)),k1_zfmisc_1(X3))
      | v1_xboole_0(k1_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f193,f244])).

fof(f193,plain,(
    ! [X0] : r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f178,f74])).

fof(f178,plain,(
    ! [X1] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(resolution,[],[f62,f143])).

fof(f143,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f89,f46])).

fof(f89,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f743,plain,
    ( ~ spl8_38
    | spl8_3
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f733,f728,f103,f740])).

fof(f103,plain,
    ( spl8_3
  <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f728,plain,
    ( spl8_36
  <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f733,plain,
    ( sK1 != k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0)))
    | spl8_3
    | ~ spl8_36 ),
    inference(superposition,[],[f105,f730])).

fof(f730,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0)))
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f728])).

fof(f105,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f731,plain,
    ( spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | spl8_8
    | ~ spl8_1
    | spl8_36
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f726,f108,f728,f93,f128,f118,f113,f98])).

fof(f113,plain,
    ( spl8_5
  <=> v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f118,plain,
    ( spl8_6
  <=> v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f128,plain,
    ( spl8_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f108,plain,
    ( spl8_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f726,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0)))
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f717,f289])).

fof(f289,plain,
    ( ! [X4] : k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,X4) = k5_xboole_0(sK1,k3_xboole_0(sK1,X4))
    | ~ spl8_4 ),
    inference(resolution,[],[f85,f110])).

fof(f110,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f717,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0))
    | ~ spl8_4 ),
    inference(resolution,[],[f84,f110])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v2_struct_0(X0)
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) ) ),
    inference(definition_unfolding,[],[f52,f49,f49,f49,f49])).

fof(f49,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

fof(f701,plain,
    ( spl8_3
    | ~ spl8_4
    | ~ spl8_9
    | ~ spl8_29 ),
    inference(avatar_split_clause,[],[f700,f538,f133,f108,f103])).

fof(f538,plain,
    ( spl8_29
  <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f700,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl8_4
    | ~ spl8_9
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f699,f250])).

fof(f699,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl8_4
    | ~ spl8_9
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f698,f283])).

fof(f283,plain,
    ( ! [X6] : k1_xboole_0 = k3_xboole_0(X6,k1_xboole_0)
    | ~ spl8_9 ),
    inference(resolution,[],[f254,f214])).

fof(f254,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,k1_xboole_0),X1)
    | ~ spl8_9 ),
    inference(resolution,[],[f249,f185])).

fof(f185,plain,(
    ! [X4,X5] :
      ( ~ v1_xboole_0(X4)
      | r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f67,f54])).

fof(f249,plain,
    ( ! [X1] : v1_xboole_0(k3_xboole_0(X1,k1_xboole_0))
    | ~ spl8_9 ),
    inference(resolution,[],[f159,f176])).

fof(f176,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl8_9 ),
    inference(resolution,[],[f173,f135])).

fof(f135,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f173,plain,(
    ! [X2,X3] :
      ( ~ v1_xboole_0(X3)
      | r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f61,f54])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f57,f53])).

fof(f698,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))
    | ~ spl8_4
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f540,f289])).

fof(f540,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_xboole_0)
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f538])).

fof(f541,plain,
    ( spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | spl8_8
    | ~ spl8_1
    | spl8_29
    | ~ spl8_4
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f529,f454,f108,f538,f93,f128,f118,f113,f98])).

fof(f454,plain,
    ( spl8_27
  <=> k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f529,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_xboole_0)
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_27 ),
    inference(resolution,[],[f517,f110])).

fof(f517,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
        | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_xboole_0)
        | ~ l1_struct_0(X0)
        | v1_xboole_0(X1)
        | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
        | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
        | v2_struct_0(X0) )
    | ~ spl8_27 ),
    inference(backward_demodulation,[],[f84,f456])).

fof(f456,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f454])).

fof(f497,plain,
    ( spl8_27
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f496,f433,f454])).

fof(f496,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | ~ spl8_24 ),
    inference(resolution,[],[f489,f214])).

fof(f489,plain,
    ( ! [X0] : r1_tarski(k1_tarski(k1_xboole_0),X0)
    | ~ spl8_24 ),
    inference(resolution,[],[f435,f185])).

fof(f435,plain,
    ( v1_xboole_0(k1_tarski(k1_xboole_0))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f433])).

fof(f424,plain,(
    ~ spl8_22 ),
    inference(avatar_contradiction_clause,[],[f420])).

fof(f420,plain,
    ( $false
    | ~ spl8_22 ),
    inference(resolution,[],[f415,f146])).

fof(f146,plain,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(resolution,[],[f143,f54])).

fof(f415,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f413])).

fof(f361,plain,(
    spl8_21 ),
    inference(avatar_split_clause,[],[f356,f358])).

fof(f356,plain,(
    k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f352,f214])).

fof(f352,plain,(
    ! [X0] : r1_tarski(sK2(k1_zfmisc_1(X0)),X0) ),
    inference(global_subsumption,[],[f146,f142])).

fof(f142,plain,(
    ! [X0] :
      ( r1_tarski(sK2(k1_zfmisc_1(X0)),X0)
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f88,f53])).

fof(f337,plain,
    ( ~ spl8_9
    | ~ spl8_16 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | ~ spl8_9
    | ~ spl8_16 ),
    inference(resolution,[],[f307,f171])).

fof(f171,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl8_9 ),
    inference(resolution,[],[f168,f135])).

fof(f168,plain,(
    ! [X2,X3] :
      ( ~ v1_xboole_0(X2)
      | r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f60,f54])).

fof(f307,plain,
    ( ! [X1] : ~ r1_xboole_0(k1_xboole_0,X1)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl8_16
  <=> ! [X1] : ~ r1_xboole_0(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f323,plain,
    ( ~ spl8_18
    | spl8_19
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f312,f108,f128,f123,f118,f113,f320,f316])).

fof(f123,plain,
    ( spl8_7
  <=> v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f312,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ sP7(sK1)
    | ~ spl8_4 ),
    inference(resolution,[],[f91,f110])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | v1_xboole_0(X0)
      | ~ sP7(X1) ) ),
    inference(general_splitting,[],[f83,f90_D])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(definition_unfolding,[],[f50,f49,f49,f49,f49])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

fof(f311,plain,
    ( spl8_16
    | spl8_17
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f300,f133,f309,f306])).

fof(f300,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | ~ r1_xboole_0(k1_xboole_0,X1) )
    | ~ spl8_9 ),
    inference(superposition,[],[f57,f260])).

fof(f260,plain,
    ( ! [X6] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X6)
    | ~ spl8_9 ),
    inference(resolution,[],[f251,f214])).

fof(f251,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(k1_xboole_0,X0),X1)
    | ~ spl8_9 ),
    inference(resolution,[],[f248,f185])).

fof(f248,plain,
    ( ! [X0] : v1_xboole_0(k3_xboole_0(k1_xboole_0,X0))
    | ~ spl8_9 ),
    inference(resolution,[],[f159,f171])).

fof(f136,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f45,f133])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f131,plain,(
    ~ spl8_8 ),
    inference(avatar_split_clause,[],[f37,f128])).

fof(f37,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

fof(f126,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f80,f123])).

fof(f80,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f38,f49])).

fof(f38,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f121,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f79,f118])).

fof(f79,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f39,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f116,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f78,f113])).

fof(f78,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f40,f49])).

fof(f40,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f111,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f77,f108])).

fof(f77,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f25])).

fof(f106,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f42,f103])).

fof(f42,plain,(
    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f101,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f43,f98])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f96,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f44,f93])).

fof(f44,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:33:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (26724)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (26715)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (26719)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (26725)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (26723)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (26725)Refutation not found, incomplete strategy% (26725)------------------------------
% 0.20/0.52  % (26725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26725)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26725)Memory used [KB]: 10746
% 0.20/0.52  % (26725)Time elapsed: 0.097 s
% 0.20/0.52  % (26725)------------------------------
% 0.20/0.52  % (26725)------------------------------
% 0.20/0.52  % (26731)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (26726)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (26718)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (26737)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (26716)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (26717)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (26739)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (26735)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (26720)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (26728)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (26727)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (26737)Refutation not found, incomplete strategy% (26737)------------------------------
% 0.20/0.54  % (26737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (26737)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (26737)Memory used [KB]: 10746
% 0.20/0.54  % (26737)Time elapsed: 0.091 s
% 0.20/0.54  % (26737)------------------------------
% 0.20/0.54  % (26737)------------------------------
% 0.20/0.54  % (26717)Refutation not found, incomplete strategy% (26717)------------------------------
% 0.20/0.54  % (26717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (26717)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (26717)Memory used [KB]: 10746
% 0.20/0.54  % (26717)Time elapsed: 0.125 s
% 0.20/0.54  % (26717)------------------------------
% 0.20/0.54  % (26717)------------------------------
% 0.20/0.55  % (26736)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (26733)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (26738)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (26729)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (26722)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (26730)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (26743)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (26744)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.56  % (26721)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.56  % (26732)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.56  % (26742)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.56  % (26740)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.50/0.56  % (26734)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.56  % (26741)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.14/0.66  % (26745)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.26/0.67  % (26746)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.26/0.67  % (26747)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.83/0.82  % (26720)Time limit reached!
% 2.83/0.82  % (26720)------------------------------
% 2.83/0.82  % (26720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.83/0.82  % (26720)Termination reason: Time limit
% 2.83/0.82  % (26720)Termination phase: Saturation
% 2.83/0.82  
% 2.83/0.82  % (26720)Memory used [KB]: 8699
% 2.83/0.82  % (26720)Time elapsed: 0.400 s
% 2.83/0.82  % (26720)------------------------------
% 2.83/0.82  % (26720)------------------------------
% 3.48/0.85  % (26731)Refutation found. Thanks to Tanya!
% 3.48/0.85  % SZS status Theorem for theBenchmark
% 3.48/0.85  % SZS output start Proof for theBenchmark
% 3.48/0.85  fof(f5398,plain,(
% 3.48/0.85    $false),
% 3.48/0.85    inference(avatar_sat_refutation,[],[f96,f101,f106,f111,f116,f121,f126,f131,f136,f311,f323,f337,f361,f424,f497,f541,f701,f731,f743,f751,f772,f818,f1106,f3125,f4006,f4043,f4078,f4356,f4621,f5329,f5334,f5348,f5397])).
% 3.48/0.85  fof(f5397,plain,(
% 3.48/0.85    spl8_188 | ~spl8_44 | ~spl8_187),
% 3.48/0.85    inference(avatar_split_clause,[],[f5390,f5326,f815,f5331])).
% 3.48/0.85  fof(f5331,plain,(
% 3.48/0.85    spl8_188 <=> r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_tarski(k1_xboole_0))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_188])])).
% 3.48/0.85  fof(f815,plain,(
% 3.48/0.85    spl8_44 <=> r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).
% 3.48/0.85  fof(f5326,plain,(
% 3.48/0.85    spl8_187 <=> k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0),k1_tarski(k1_xboole_0))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_187])])).
% 3.48/0.85  fof(f5390,plain,(
% 3.48/0.85    ~r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) | r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_tarski(k1_xboole_0)) | ~spl8_187),
% 3.48/0.85    inference(superposition,[],[f68,f5328])).
% 3.48/0.85  fof(f5328,plain,(
% 3.48/0.85    k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0),k1_tarski(k1_xboole_0)) | ~spl8_187),
% 3.48/0.85    inference(avatar_component_clause,[],[f5326])).
% 3.48/0.85  fof(f68,plain,(
% 3.48/0.85    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 3.48/0.85    inference(cnf_transformation,[],[f35])).
% 3.48/0.85  fof(f35,plain,(
% 3.48/0.85    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.48/0.85    inference(ennf_transformation,[],[f2])).
% 3.48/0.85  fof(f2,axiom,(
% 3.48/0.85    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.48/0.85  fof(f5348,plain,(
% 3.48/0.85    k1_tarski(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) | sK1 != k7_subset_1(sK1,sK1,k1_zfmisc_1(k1_xboole_0)) | sK1 = k7_subset_1(sK1,sK1,k1_tarski(k1_xboole_0))),
% 3.48/0.85    introduced(theory_tautology_sat_conflict,[])).
% 3.48/0.85  fof(f5334,plain,(
% 3.48/0.85    spl8_186 | spl8_22 | ~spl8_188 | ~spl8_21),
% 3.48/0.85    inference(avatar_split_clause,[],[f5315,f358,f5331,f413,f5322])).
% 3.48/0.85  fof(f5322,plain,(
% 3.48/0.85    spl8_186 <=> k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_186])])).
% 3.48/0.85  fof(f413,plain,(
% 3.48/0.85    spl8_22 <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 3.48/0.85  fof(f358,plain,(
% 3.48/0.85    spl8_21 <=> k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 3.48/0.85  fof(f5315,plain,(
% 3.48/0.85    ~r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_tarski(k1_xboole_0)) | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) | ~spl8_21),
% 3.48/0.85    inference(superposition,[],[f899,f360])).
% 3.48/0.85  fof(f360,plain,(
% 3.48/0.85    k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0)) | ~spl8_21),
% 3.48/0.85    inference(avatar_component_clause,[],[f358])).
% 3.48/0.85  fof(f899,plain,(
% 3.48/0.85    ( ! [X0] : (~r1_tarski(X0,k1_tarski(sK2(X0))) | v1_xboole_0(X0) | k1_tarski(sK2(X0)) = X0) )),
% 3.48/0.85    inference(resolution,[],[f386,f65])).
% 3.48/0.85  fof(f65,plain,(
% 3.48/0.85    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 3.48/0.85    inference(cnf_transformation,[],[f6])).
% 3.48/0.85  fof(f6,axiom,(
% 3.48/0.85    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.48/0.85  fof(f386,plain,(
% 3.48/0.85    ( ! [X2] : (r1_tarski(k1_tarski(sK2(X2)),X2) | v1_xboole_0(X2)) )),
% 3.48/0.85    inference(resolution,[],[f179,f74])).
% 3.48/0.85  fof(f74,plain,(
% 3.48/0.85    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.48/0.85    inference(cnf_transformation,[],[f15])).
% 3.48/0.85  fof(f15,axiom,(
% 3.48/0.85    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.48/0.85  fof(f179,plain,(
% 3.48/0.85    ( ! [X2] : (m1_subset_1(k1_tarski(sK2(X2)),k1_zfmisc_1(X2)) | v1_xboole_0(X2)) )),
% 3.48/0.85    inference(resolution,[],[f62,f53])).
% 3.48/0.85  fof(f53,plain,(
% 3.48/0.85    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 3.48/0.85    inference(cnf_transformation,[],[f1])).
% 3.48/0.85  fof(f1,axiom,(
% 3.48/0.85    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 3.48/0.85  fof(f62,plain,(
% 3.48/0.85    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 3.48/0.85    inference(cnf_transformation,[],[f34])).
% 3.48/0.85  fof(f34,plain,(
% 3.48/0.85    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 3.48/0.85    inference(ennf_transformation,[],[f14])).
% 3.48/0.85  fof(f14,axiom,(
% 3.48/0.85    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 3.48/0.85  fof(f5329,plain,(
% 3.48/0.85    spl8_22 | spl8_186 | spl8_187 | ~spl8_21),
% 3.48/0.85    inference(avatar_split_clause,[],[f5320,f358,f5326,f5322,f413])).
% 3.48/0.85  fof(f5320,plain,(
% 3.48/0.85    k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0),k1_tarski(k1_xboole_0)) | k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | ~spl8_21),
% 3.48/0.85    inference(forward_demodulation,[],[f5319,f360])).
% 3.48/0.85  fof(f5319,plain,(
% 3.48/0.85    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0),k1_tarski(sK2(k1_zfmisc_1(k1_xboole_0)))) | ~spl8_21),
% 3.48/0.85    inference(forward_demodulation,[],[f5311,f360])).
% 3.48/0.85  fof(f5311,plain,(
% 3.48/0.85    v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | k1_zfmisc_1(k1_xboole_0) = k1_tarski(sK2(k1_zfmisc_1(k1_xboole_0))) | k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0),k1_tarski(sK2(k1_zfmisc_1(k1_xboole_0))))),
% 3.48/0.85    inference(resolution,[],[f899,f511])).
% 3.48/0.85  fof(f511,plain,(
% 3.48/0.85    ( ! [X8] : (r1_tarski(k1_zfmisc_1(k1_xboole_0),X8) | k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0),X8)) )),
% 3.48/0.85    inference(resolution,[],[f186,f214])).
% 3.48/0.85  fof(f214,plain,(
% 3.48/0.85    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 3.48/0.85    inference(resolution,[],[f65,f46])).
% 3.48/0.85  fof(f46,plain,(
% 3.48/0.85    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.48/0.85    inference(cnf_transformation,[],[f9])).
% 3.48/0.85  fof(f9,axiom,(
% 3.48/0.85    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 3.48/0.85  fof(f186,plain,(
% 3.48/0.85    ( ! [X6,X7] : (r1_tarski(sK5(k1_zfmisc_1(X6),X7),X6) | r1_tarski(k1_zfmisc_1(X6),X7)) )),
% 3.48/0.85    inference(resolution,[],[f67,f88])).
% 3.48/0.85  fof(f88,plain,(
% 3.48/0.85    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 3.48/0.85    inference(equality_resolution,[],[f70])).
% 3.48/0.85  fof(f70,plain,(
% 3.48/0.85    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.48/0.85    inference(cnf_transformation,[],[f12])).
% 3.48/0.85  fof(f12,axiom,(
% 3.48/0.85    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 3.48/0.85  fof(f67,plain,(
% 3.48/0.85    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.48/0.85    inference(cnf_transformation,[],[f35])).
% 3.48/0.85  fof(f4621,plain,(
% 3.48/0.85    spl8_151 | ~spl8_146),
% 3.48/0.85    inference(avatar_split_clause,[],[f4616,f4353,f4618])).
% 3.48/0.85  fof(f4618,plain,(
% 3.48/0.85    spl8_151 <=> sK1 = k7_subset_1(sK1,sK1,k1_zfmisc_1(k1_xboole_0))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_151])])).
% 3.48/0.85  fof(f4353,plain,(
% 3.48/0.85    spl8_146 <=> k1_xboole_0 = k3_xboole_0(sK1,k1_zfmisc_1(k1_xboole_0))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_146])])).
% 3.48/0.85  fof(f4616,plain,(
% 3.48/0.85    sK1 = k7_subset_1(sK1,sK1,k1_zfmisc_1(k1_xboole_0)) | ~spl8_146),
% 3.48/0.85    inference(forward_demodulation,[],[f4614,f250])).
% 3.48/0.85  fof(f250,plain,(
% 3.48/0.85    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.48/0.85    inference(forward_demodulation,[],[f82,f81])).
% 3.48/0.85  fof(f81,plain,(
% 3.48/0.85    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 3.48/0.85    inference(definition_unfolding,[],[f47,f56])).
% 3.48/0.85  fof(f56,plain,(
% 3.48/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.48/0.85    inference(cnf_transformation,[],[f7])).
% 3.48/0.85  fof(f7,axiom,(
% 3.48/0.85    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.48/0.85  fof(f47,plain,(
% 3.48/0.85    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 3.48/0.85    inference(cnf_transformation,[],[f10])).
% 3.48/0.85  fof(f10,axiom,(
% 3.48/0.85    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 3.48/0.85  fof(f82,plain,(
% 3.48/0.85    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 3.48/0.85    inference(definition_unfolding,[],[f48,f76])).
% 3.48/0.85  fof(f76,plain,(
% 3.48/0.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.48/0.85    inference(definition_unfolding,[],[f55,f56])).
% 3.48/0.85  fof(f55,plain,(
% 3.48/0.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.48/0.85    inference(cnf_transformation,[],[f11])).
% 3.48/0.85  fof(f11,axiom,(
% 3.48/0.85    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.48/0.85  fof(f48,plain,(
% 3.48/0.85    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.48/0.85    inference(cnf_transformation,[],[f8])).
% 3.48/0.85  fof(f8,axiom,(
% 3.48/0.85    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 3.48/0.85  fof(f4614,plain,(
% 3.48/0.85    k5_xboole_0(sK1,k1_xboole_0) = k7_subset_1(sK1,sK1,k1_zfmisc_1(k1_xboole_0)) | ~spl8_146),
% 3.48/0.85    inference(superposition,[],[f288,f4355])).
% 3.48/0.85  fof(f4355,plain,(
% 3.48/0.85    k1_xboole_0 = k3_xboole_0(sK1,k1_zfmisc_1(k1_xboole_0)) | ~spl8_146),
% 3.48/0.85    inference(avatar_component_clause,[],[f4353])).
% 3.48/0.85  fof(f288,plain,(
% 3.48/0.85    ( ! [X2,X3] : (k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 3.48/0.85    inference(resolution,[],[f85,f139])).
% 3.48/0.85  fof(f139,plain,(
% 3.48/0.85    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 3.48/0.85    inference(resolution,[],[f73,f86])).
% 3.48/0.85  fof(f86,plain,(
% 3.48/0.85    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.48/0.85    inference(equality_resolution,[],[f64])).
% 3.48/0.85  fof(f64,plain,(
% 3.48/0.85    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.48/0.85    inference(cnf_transformation,[],[f6])).
% 3.48/0.85  fof(f73,plain,(
% 3.48/0.85    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.48/0.85    inference(cnf_transformation,[],[f15])).
% 3.48/0.85  fof(f85,plain,(
% 3.48/0.85    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 3.48/0.85    inference(definition_unfolding,[],[f75,f56])).
% 3.48/0.85  fof(f75,plain,(
% 3.48/0.85    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 3.48/0.85    inference(cnf_transformation,[],[f36])).
% 3.48/0.85  fof(f36,plain,(
% 3.48/0.85    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/0.85    inference(ennf_transformation,[],[f13])).
% 3.48/0.85  fof(f13,axiom,(
% 3.48/0.85    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.48/0.85  fof(f4356,plain,(
% 3.48/0.85    spl8_146 | ~spl8_121),
% 3.48/0.85    inference(avatar_split_clause,[],[f4343,f4075,f4353])).
% 3.48/0.85  fof(f4075,plain,(
% 3.48/0.85    spl8_121 <=> r1_xboole_0(sK1,k1_zfmisc_1(k1_xboole_0))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_121])])).
% 3.48/0.85  fof(f4343,plain,(
% 3.48/0.85    k1_xboole_0 = k3_xboole_0(sK1,k1_zfmisc_1(k1_xboole_0)) | ~spl8_121),
% 3.48/0.85    inference(resolution,[],[f4098,f214])).
% 3.48/0.85  fof(f4098,plain,(
% 3.48/0.85    ( ! [X2] : (r1_tarski(k3_xboole_0(sK1,k1_zfmisc_1(k1_xboole_0)),X2)) ) | ~spl8_121),
% 3.48/0.85    inference(resolution,[],[f4077,f187])).
% 3.48/0.85  fof(f187,plain,(
% 3.48/0.85    ( ! [X10,X8,X9] : (~r1_xboole_0(X8,X9) | r1_tarski(k3_xboole_0(X8,X9),X10)) )),
% 3.48/0.85    inference(resolution,[],[f67,f57])).
% 3.48/0.85  fof(f57,plain,(
% 3.48/0.85    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.48/0.85    inference(cnf_transformation,[],[f32])).
% 3.48/0.85  fof(f32,plain,(
% 3.48/0.85    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.48/0.85    inference(ennf_transformation,[],[f22])).
% 3.48/0.85  fof(f22,plain,(
% 3.48/0.85    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.48/0.85    inference(rectify,[],[f5])).
% 3.48/0.85  fof(f5,axiom,(
% 3.48/0.85    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 3.48/0.85  fof(f4077,plain,(
% 3.48/0.85    r1_xboole_0(sK1,k1_zfmisc_1(k1_xboole_0)) | ~spl8_121),
% 3.48/0.85    inference(avatar_component_clause,[],[f4075])).
% 3.48/0.85  fof(f4078,plain,(
% 3.48/0.85    spl8_121 | ~spl8_114),
% 3.48/0.85    inference(avatar_split_clause,[],[f4062,f4022,f4075])).
% 3.48/0.85  fof(f4022,plain,(
% 3.48/0.85    spl8_114 <=> r1_xboole_0(k1_zfmisc_1(k1_xboole_0),sK1)),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_114])])).
% 3.48/0.85  fof(f4062,plain,(
% 3.48/0.85    r1_xboole_0(sK1,k1_zfmisc_1(k1_xboole_0)) | ~spl8_114),
% 3.48/0.85    inference(resolution,[],[f4024,f582])).
% 3.48/0.85  fof(f582,plain,(
% 3.48/0.85    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 3.48/0.85    inference(duplicate_literal_removal,[],[f578])).
% 3.48/0.85  fof(f578,plain,(
% 3.48/0.85    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) | r1_xboole_0(X1,X0)) )),
% 3.48/0.85    inference(resolution,[],[f200,f60])).
% 3.48/0.85  fof(f60,plain,(
% 3.48/0.85    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.48/0.85    inference(cnf_transformation,[],[f33])).
% 3.48/0.85  fof(f33,plain,(
% 3.48/0.85    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.48/0.85    inference(ennf_transformation,[],[f23])).
% 3.48/0.85  fof(f23,plain,(
% 3.48/0.85    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.48/0.85    inference(rectify,[],[f4])).
% 3.48/0.85  fof(f4,axiom,(
% 3.48/0.85    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 3.48/0.85  fof(f200,plain,(
% 3.48/0.85    ( ! [X10,X11,X9] : (~r2_hidden(sK4(X9,X10),X11) | ~r1_xboole_0(X10,X11) | r1_xboole_0(X9,X10)) )),
% 3.48/0.85    inference(resolution,[],[f59,f61])).
% 3.48/0.85  fof(f61,plain,(
% 3.48/0.85    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.48/0.85    inference(cnf_transformation,[],[f33])).
% 3.48/0.85  fof(f59,plain,(
% 3.48/0.85    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 3.48/0.85    inference(cnf_transformation,[],[f33])).
% 3.48/0.85  fof(f4024,plain,(
% 3.48/0.85    r1_xboole_0(k1_zfmisc_1(k1_xboole_0),sK1) | ~spl8_114),
% 3.48/0.85    inference(avatar_component_clause,[],[f4022])).
% 3.48/0.85  fof(f4043,plain,(
% 3.48/0.85    spl8_114 | ~spl8_9 | ~spl8_113),
% 3.48/0.85    inference(avatar_split_clause,[],[f4018,f4003,f133,f4022])).
% 3.48/0.85  fof(f133,plain,(
% 3.48/0.85    spl8_9 <=> v1_xboole_0(k1_xboole_0)),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 3.48/0.85  fof(f4003,plain,(
% 3.48/0.85    spl8_113 <=> k1_xboole_0 = k3_xboole_0(k1_zfmisc_1(k1_xboole_0),sK1)),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).
% 3.48/0.85  fof(f4018,plain,(
% 3.48/0.85    ~v1_xboole_0(k1_xboole_0) | r1_xboole_0(k1_zfmisc_1(k1_xboole_0),sK1) | ~spl8_113),
% 3.48/0.85    inference(superposition,[],[f266,f4005])).
% 3.48/0.85  fof(f4005,plain,(
% 3.48/0.85    k1_xboole_0 = k3_xboole_0(k1_zfmisc_1(k1_xboole_0),sK1) | ~spl8_113),
% 3.48/0.85    inference(avatar_component_clause,[],[f4003])).
% 3.48/0.85  fof(f266,plain,(
% 3.48/0.85    ( ! [X12,X13] : (~v1_xboole_0(k3_xboole_0(X12,X13)) | r1_xboole_0(X12,X13)) )),
% 3.48/0.85    inference(resolution,[],[f58,f54])).
% 3.48/0.85  fof(f54,plain,(
% 3.48/0.85    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.48/0.85    inference(cnf_transformation,[],[f1])).
% 3.48/0.85  fof(f58,plain,(
% 3.48/0.85    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.48/0.85    inference(cnf_transformation,[],[f32])).
% 3.48/0.85  fof(f4006,plain,(
% 3.48/0.85    spl8_113 | ~spl8_17 | spl8_18),
% 3.48/0.85    inference(avatar_split_clause,[],[f4001,f316,f309,f4003])).
% 3.48/0.85  fof(f309,plain,(
% 3.48/0.85    spl8_17 <=> ! [X2] : ~r2_hidden(X2,k1_xboole_0)),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 3.48/0.85  fof(f316,plain,(
% 3.48/0.85    spl8_18 <=> sP7(sK1)),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 3.48/0.85  fof(f4001,plain,(
% 3.48/0.85    k1_xboole_0 = k3_xboole_0(k1_zfmisc_1(k1_xboole_0),sK1) | (~spl8_17 | spl8_18)),
% 3.48/0.85    inference(resolution,[],[f3825,f318])).
% 3.48/0.85  fof(f318,plain,(
% 3.48/0.85    ~sP7(sK1) | spl8_18),
% 3.48/0.85    inference(avatar_component_clause,[],[f316])).
% 3.48/0.85  fof(f3825,plain,(
% 3.48/0.85    ( ! [X28] : (sP7(X28) | k1_xboole_0 = k3_xboole_0(k1_zfmisc_1(k1_xboole_0),X28)) ) | ~spl8_17),
% 3.48/0.85    inference(resolution,[],[f3598,f214])).
% 3.48/0.85  fof(f3598,plain,(
% 3.48/0.85    ( ! [X8,X7] : (r1_tarski(k3_xboole_0(k1_zfmisc_1(k1_xboole_0),X7),X8) | sP7(X7)) ) | ~spl8_17),
% 3.48/0.85    inference(resolution,[],[f3553,f187])).
% 3.48/0.85  fof(f3553,plain,(
% 3.48/0.85    ( ! [X0] : (r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X0) | sP7(X0)) ) | ~spl8_17),
% 3.48/0.85    inference(duplicate_literal_removal,[],[f3535])).
% 3.48/0.85  fof(f3535,plain,(
% 3.48/0.85    ( ! [X0] : (r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X0) | r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X0) | sP7(X0)) ) | ~spl8_17),
% 3.48/0.85    inference(resolution,[],[f1694,f172])).
% 3.48/0.85  fof(f172,plain,(
% 3.48/0.85    ( ! [X0,X1] : (~v1_xboole_0(sK4(X0,X1)) | r1_xboole_0(X0,X1) | sP7(X1)) )),
% 3.48/0.85    inference(resolution,[],[f61,f90])).
% 3.48/0.85  fof(f90,plain,(
% 3.48/0.85    ( ! [X2,X1] : (~r2_hidden(X2,X1) | ~v1_xboole_0(X2) | sP7(X1)) )),
% 3.48/0.85    inference(cnf_transformation,[],[f90_D])).
% 3.48/0.85  fof(f90_D,plain,(
% 3.48/0.85    ( ! [X1] : (( ! [X2] : (~r2_hidden(X2,X1) | ~v1_xboole_0(X2)) ) <=> ~sP7(X1)) )),
% 3.48/0.85    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 3.48/0.85  fof(f1694,plain,(
% 3.48/0.85    ( ! [X14] : (v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0),X14)) | r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X14)) ) | ~spl8_17),
% 3.48/0.85    inference(resolution,[],[f458,f310])).
% 3.48/0.85  fof(f310,plain,(
% 3.48/0.85    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) ) | ~spl8_17),
% 3.48/0.85    inference(avatar_component_clause,[],[f309])).
% 3.48/0.85  fof(f458,plain,(
% 3.48/0.85    ( ! [X0,X1] : (r2_hidden(sK2(sK4(k1_zfmisc_1(X0),X1)),X0) | r1_xboole_0(k1_zfmisc_1(X0),X1) | v1_xboole_0(sK4(k1_zfmisc_1(X0),X1))) )),
% 3.48/0.85    inference(resolution,[],[f169,f244])).
% 3.48/0.85  fof(f244,plain,(
% 3.48/0.85    ( ! [X8,X9] : (~r1_tarski(X8,X9) | r2_hidden(sK2(X8),X9) | v1_xboole_0(X8)) )),
% 3.48/0.85    inference(resolution,[],[f66,f53])).
% 3.48/0.85  fof(f66,plain,(
% 3.48/0.85    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.48/0.85    inference(cnf_transformation,[],[f35])).
% 3.48/0.85  fof(f169,plain,(
% 3.48/0.85    ( ! [X4,X5] : (r1_tarski(sK4(k1_zfmisc_1(X4),X5),X4) | r1_xboole_0(k1_zfmisc_1(X4),X5)) )),
% 3.48/0.85    inference(resolution,[],[f60,f88])).
% 3.48/0.85  fof(f3125,plain,(
% 3.48/0.85    spl8_2 | ~spl8_1 | ~spl8_19),
% 3.48/0.85    inference(avatar_split_clause,[],[f3113,f320,f93,f98])).
% 3.48/0.85  fof(f98,plain,(
% 3.48/0.85    spl8_2 <=> v2_struct_0(sK0)),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 3.48/0.85  fof(f93,plain,(
% 3.48/0.85    spl8_1 <=> l1_struct_0(sK0)),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 3.48/0.85  fof(f320,plain,(
% 3.48/0.85    spl8_19 <=> v1_xboole_0(k2_struct_0(sK0))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 3.48/0.85  fof(f3113,plain,(
% 3.48/0.85    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl8_19),
% 3.48/0.85    inference(resolution,[],[f322,f51])).
% 3.48/0.85  fof(f51,plain,(
% 3.48/0.85    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.48/0.85    inference(cnf_transformation,[],[f29])).
% 3.48/0.85  fof(f29,plain,(
% 3.48/0.85    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.48/0.85    inference(flattening,[],[f28])).
% 3.48/0.85  fof(f28,plain,(
% 3.48/0.85    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.48/0.85    inference(ennf_transformation,[],[f16])).
% 3.48/0.85  fof(f16,axiom,(
% 3.48/0.85    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 3.48/0.85  fof(f322,plain,(
% 3.48/0.85    v1_xboole_0(k2_struct_0(sK0)) | ~spl8_19),
% 3.48/0.85    inference(avatar_component_clause,[],[f320])).
% 3.48/0.85  fof(f1106,plain,(
% 3.48/0.85    ~spl8_57 | spl8_38),
% 3.48/0.85    inference(avatar_split_clause,[],[f1089,f740,f1103])).
% 3.48/0.85  fof(f1103,plain,(
% 3.48/0.85    spl8_57 <=> sK1 = k7_subset_1(sK1,sK1,k1_tarski(k1_xboole_0))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).
% 3.48/0.85  fof(f740,plain,(
% 3.48/0.85    spl8_38 <=> sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0)))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 3.48/0.85  fof(f1089,plain,(
% 3.48/0.85    sK1 != k7_subset_1(sK1,sK1,k1_tarski(k1_xboole_0)) | spl8_38),
% 3.48/0.85    inference(superposition,[],[f742,f288])).
% 3.48/0.85  fof(f742,plain,(
% 3.48/0.85    sK1 != k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0))) | spl8_38),
% 3.48/0.85    inference(avatar_component_clause,[],[f740])).
% 3.48/0.85  fof(f818,plain,(
% 3.48/0.85    spl8_24 | spl8_44 | ~spl8_41),
% 3.48/0.85    inference(avatar_split_clause,[],[f809,f769,f815,f433])).
% 3.48/0.85  fof(f433,plain,(
% 3.48/0.85    spl8_24 <=> v1_xboole_0(k1_tarski(k1_xboole_0))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 3.48/0.85  fof(f769,plain,(
% 3.48/0.85    spl8_41 <=> k1_xboole_0 = sK2(k1_tarski(k1_xboole_0))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 3.48/0.85  fof(f809,plain,(
% 3.48/0.85    r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) | v1_xboole_0(k1_tarski(k1_xboole_0)) | ~spl8_41),
% 3.48/0.85    inference(superposition,[],[f53,f771])).
% 3.48/0.85  fof(f771,plain,(
% 3.48/0.85    k1_xboole_0 = sK2(k1_tarski(k1_xboole_0)) | ~spl8_41),
% 3.48/0.85    inference(avatar_component_clause,[],[f769])).
% 3.48/0.85  fof(f772,plain,(
% 3.48/0.85    spl8_41 | ~spl8_25),
% 3.48/0.85    inference(avatar_split_clause,[],[f759,f437,f769])).
% 3.48/0.85  fof(f437,plain,(
% 3.48/0.85    spl8_25 <=> ! [X6] : r2_hidden(sK2(k1_tarski(k1_xboole_0)),k1_zfmisc_1(X6))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 3.48/0.85  fof(f759,plain,(
% 3.48/0.85    k1_xboole_0 = sK2(k1_tarski(k1_xboole_0)) | ~spl8_25),
% 3.48/0.85    inference(resolution,[],[f475,f214])).
% 3.48/0.85  fof(f475,plain,(
% 3.48/0.85    ( ! [X1] : (r1_tarski(sK2(k1_tarski(k1_xboole_0)),X1)) ) | ~spl8_25),
% 3.48/0.85    inference(resolution,[],[f438,f88])).
% 3.48/0.85  fof(f438,plain,(
% 3.48/0.85    ( ! [X6] : (r2_hidden(sK2(k1_tarski(k1_xboole_0)),k1_zfmisc_1(X6))) ) | ~spl8_25),
% 3.48/0.85    inference(avatar_component_clause,[],[f437])).
% 3.48/0.85  fof(f751,plain,(
% 3.48/0.85    spl8_24 | spl8_25),
% 3.48/0.85    inference(avatar_split_clause,[],[f747,f437,f433])).
% 3.48/0.85  fof(f747,plain,(
% 3.48/0.85    ( ! [X3] : (r2_hidden(sK2(k1_tarski(k1_xboole_0)),k1_zfmisc_1(X3)) | v1_xboole_0(k1_tarski(k1_xboole_0))) )),
% 3.48/0.85    inference(resolution,[],[f193,f244])).
% 3.48/0.85  fof(f193,plain,(
% 3.48/0.85    ( ! [X0] : (r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(X0))) )),
% 3.48/0.85    inference(resolution,[],[f178,f74])).
% 3.48/0.85  fof(f178,plain,(
% 3.48/0.85    ( ! [X1] : (m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))) )),
% 3.48/0.85    inference(resolution,[],[f62,f143])).
% 3.48/0.85  fof(f143,plain,(
% 3.48/0.85    ( ! [X0] : (r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.48/0.85    inference(resolution,[],[f89,f46])).
% 3.48/0.85  fof(f89,plain,(
% 3.48/0.85    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 3.48/0.85    inference(equality_resolution,[],[f69])).
% 3.48/0.85  fof(f69,plain,(
% 3.48/0.85    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.48/0.85    inference(cnf_transformation,[],[f12])).
% 3.48/0.85  fof(f743,plain,(
% 3.48/0.85    ~spl8_38 | spl8_3 | ~spl8_36),
% 3.48/0.85    inference(avatar_split_clause,[],[f733,f728,f103,f740])).
% 3.48/0.85  fof(f103,plain,(
% 3.48/0.85    spl8_3 <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 3.48/0.85  fof(f728,plain,(
% 3.48/0.85    spl8_36 <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0)))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 3.48/0.85  fof(f733,plain,(
% 3.48/0.85    sK1 != k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0))) | (spl8_3 | ~spl8_36)),
% 3.48/0.85    inference(superposition,[],[f105,f730])).
% 3.48/0.85  fof(f730,plain,(
% 3.48/0.85    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0))) | ~spl8_36),
% 3.48/0.85    inference(avatar_component_clause,[],[f728])).
% 3.48/0.85  fof(f105,plain,(
% 3.48/0.85    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl8_3),
% 3.48/0.85    inference(avatar_component_clause,[],[f103])).
% 3.48/0.85  fof(f731,plain,(
% 3.48/0.85    spl8_2 | ~spl8_5 | ~spl8_6 | spl8_8 | ~spl8_1 | spl8_36 | ~spl8_4),
% 3.48/0.85    inference(avatar_split_clause,[],[f726,f108,f728,f93,f128,f118,f113,f98])).
% 3.48/0.85  fof(f113,plain,(
% 3.48/0.85    spl8_5 <=> v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 3.48/0.85  fof(f118,plain,(
% 3.48/0.85    spl8_6 <=> v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 3.48/0.85  fof(f128,plain,(
% 3.48/0.85    spl8_8 <=> v1_xboole_0(sK1)),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 3.48/0.85  fof(f108,plain,(
% 3.48/0.85    spl8_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 3.48/0.85  fof(f726,plain,(
% 3.48/0.85    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tarski(k1_xboole_0))) | ~l1_struct_0(sK0) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v2_struct_0(sK0) | ~spl8_4),
% 3.48/0.85    inference(forward_demodulation,[],[f717,f289])).
% 3.48/0.85  fof(f289,plain,(
% 3.48/0.85    ( ! [X4] : (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,X4) = k5_xboole_0(sK1,k3_xboole_0(sK1,X4))) ) | ~spl8_4),
% 3.48/0.85    inference(resolution,[],[f85,f110])).
% 3.48/0.85  fof(f110,plain,(
% 3.48/0.85    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~spl8_4),
% 3.48/0.85    inference(avatar_component_clause,[],[f108])).
% 3.48/0.85  fof(f717,plain,(
% 3.48/0.85    ~l1_struct_0(sK0) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v2_struct_0(sK0) | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0)) | ~spl8_4),
% 3.48/0.85    inference(resolution,[],[f84,f110])).
% 3.48/0.85  fof(f84,plain,(
% 3.48/0.85    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v2_struct_0(X0) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0))) )),
% 3.48/0.85    inference(definition_unfolding,[],[f52,f49,f49,f49,f49])).
% 3.48/0.85  fof(f49,plain,(
% 3.48/0.85    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 3.48/0.85    inference(cnf_transformation,[],[f17])).
% 3.48/0.85  fof(f17,axiom,(
% 3.48/0.85    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 3.48/0.85  fof(f52,plain,(
% 3.48/0.85    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )),
% 3.48/0.85    inference(cnf_transformation,[],[f31])).
% 3.48/0.85  fof(f31,plain,(
% 3.48/0.85    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.48/0.85    inference(flattening,[],[f30])).
% 3.48/0.85  fof(f30,plain,(
% 3.48/0.85    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.48/0.85    inference(ennf_transformation,[],[f18])).
% 3.48/0.85  fof(f18,axiom,(
% 3.48/0.85    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).
% 3.48/0.85  fof(f701,plain,(
% 3.48/0.85    spl8_3 | ~spl8_4 | ~spl8_9 | ~spl8_29),
% 3.48/0.85    inference(avatar_split_clause,[],[f700,f538,f133,f108,f103])).
% 3.48/0.85  fof(f538,plain,(
% 3.48/0.85    spl8_29 <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_xboole_0)),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 3.48/0.85  fof(f700,plain,(
% 3.48/0.85    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | (~spl8_4 | ~spl8_9 | ~spl8_29)),
% 3.48/0.85    inference(forward_demodulation,[],[f699,f250])).
% 3.48/0.85  fof(f699,plain,(
% 3.48/0.85    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k1_xboole_0) | (~spl8_4 | ~spl8_9 | ~spl8_29)),
% 3.48/0.85    inference(forward_demodulation,[],[f698,f283])).
% 3.48/0.85  fof(f283,plain,(
% 3.48/0.85    ( ! [X6] : (k1_xboole_0 = k3_xboole_0(X6,k1_xboole_0)) ) | ~spl8_9),
% 3.48/0.85    inference(resolution,[],[f254,f214])).
% 3.48/0.85  fof(f254,plain,(
% 3.48/0.85    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,k1_xboole_0),X1)) ) | ~spl8_9),
% 3.48/0.85    inference(resolution,[],[f249,f185])).
% 3.48/0.85  fof(f185,plain,(
% 3.48/0.85    ( ! [X4,X5] : (~v1_xboole_0(X4) | r1_tarski(X4,X5)) )),
% 3.48/0.85    inference(resolution,[],[f67,f54])).
% 3.48/0.85  fof(f249,plain,(
% 3.48/0.85    ( ! [X1] : (v1_xboole_0(k3_xboole_0(X1,k1_xboole_0))) ) | ~spl8_9),
% 3.48/0.85    inference(resolution,[],[f159,f176])).
% 3.48/0.85  fof(f176,plain,(
% 3.48/0.85    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl8_9),
% 3.48/0.85    inference(resolution,[],[f173,f135])).
% 3.48/0.85  fof(f135,plain,(
% 3.48/0.85    v1_xboole_0(k1_xboole_0) | ~spl8_9),
% 3.48/0.85    inference(avatar_component_clause,[],[f133])).
% 3.48/0.85  fof(f173,plain,(
% 3.48/0.85    ( ! [X2,X3] : (~v1_xboole_0(X3) | r1_xboole_0(X2,X3)) )),
% 3.48/0.85    inference(resolution,[],[f61,f54])).
% 3.48/0.85  fof(f159,plain,(
% 3.48/0.85    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1))) )),
% 3.48/0.85    inference(resolution,[],[f57,f53])).
% 3.48/0.85  fof(f698,plain,(
% 3.48/0.85    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) | (~spl8_4 | ~spl8_29)),
% 3.48/0.85    inference(forward_demodulation,[],[f540,f289])).
% 3.48/0.85  fof(f540,plain,(
% 3.48/0.85    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_xboole_0) | ~spl8_29),
% 3.48/0.85    inference(avatar_component_clause,[],[f538])).
% 3.48/0.85  fof(f541,plain,(
% 3.48/0.85    spl8_2 | ~spl8_5 | ~spl8_6 | spl8_8 | ~spl8_1 | spl8_29 | ~spl8_4 | ~spl8_27),
% 3.48/0.85    inference(avatar_split_clause,[],[f529,f454,f108,f538,f93,f128,f118,f113,f98])).
% 3.48/0.85  fof(f454,plain,(
% 3.48/0.85    spl8_27 <=> k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 3.48/0.85  fof(f529,plain,(
% 3.48/0.85    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_xboole_0) | ~l1_struct_0(sK0) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v2_struct_0(sK0) | (~spl8_4 | ~spl8_27)),
% 3.48/0.85    inference(resolution,[],[f517,f110])).
% 3.48/0.85  fof(f517,plain,(
% 3.48/0.85    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_xboole_0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v2_struct_0(X0)) ) | ~spl8_27),
% 3.48/0.85    inference(backward_demodulation,[],[f84,f456])).
% 3.48/0.85  fof(f456,plain,(
% 3.48/0.85    k1_xboole_0 = k1_tarski(k1_xboole_0) | ~spl8_27),
% 3.48/0.85    inference(avatar_component_clause,[],[f454])).
% 3.48/0.85  fof(f497,plain,(
% 3.48/0.85    spl8_27 | ~spl8_24),
% 3.48/0.85    inference(avatar_split_clause,[],[f496,f433,f454])).
% 3.48/0.85  fof(f496,plain,(
% 3.48/0.85    k1_xboole_0 = k1_tarski(k1_xboole_0) | ~spl8_24),
% 3.48/0.85    inference(resolution,[],[f489,f214])).
% 3.48/0.85  fof(f489,plain,(
% 3.48/0.85    ( ! [X0] : (r1_tarski(k1_tarski(k1_xboole_0),X0)) ) | ~spl8_24),
% 3.48/0.85    inference(resolution,[],[f435,f185])).
% 3.48/0.85  fof(f435,plain,(
% 3.48/0.85    v1_xboole_0(k1_tarski(k1_xboole_0)) | ~spl8_24),
% 3.48/0.85    inference(avatar_component_clause,[],[f433])).
% 3.48/0.85  fof(f424,plain,(
% 3.48/0.85    ~spl8_22),
% 3.48/0.85    inference(avatar_contradiction_clause,[],[f420])).
% 3.48/0.85  fof(f420,plain,(
% 3.48/0.85    $false | ~spl8_22),
% 3.48/0.85    inference(resolution,[],[f415,f146])).
% 3.48/0.85  fof(f146,plain,(
% 3.48/0.85    ( ! [X1] : (~v1_xboole_0(k1_zfmisc_1(X1))) )),
% 3.48/0.85    inference(resolution,[],[f143,f54])).
% 3.48/0.85  fof(f415,plain,(
% 3.48/0.85    v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | ~spl8_22),
% 3.48/0.85    inference(avatar_component_clause,[],[f413])).
% 3.48/0.85  fof(f361,plain,(
% 3.48/0.85    spl8_21),
% 3.48/0.85    inference(avatar_split_clause,[],[f356,f358])).
% 3.48/0.85  fof(f356,plain,(
% 3.48/0.85    k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0))),
% 3.48/0.85    inference(resolution,[],[f352,f214])).
% 3.48/0.85  fof(f352,plain,(
% 3.48/0.85    ( ! [X0] : (r1_tarski(sK2(k1_zfmisc_1(X0)),X0)) )),
% 3.48/0.85    inference(global_subsumption,[],[f146,f142])).
% 3.48/0.85  fof(f142,plain,(
% 3.48/0.85    ( ! [X0] : (r1_tarski(sK2(k1_zfmisc_1(X0)),X0) | v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.48/0.85    inference(resolution,[],[f88,f53])).
% 3.48/0.85  fof(f337,plain,(
% 3.48/0.85    ~spl8_9 | ~spl8_16),
% 3.48/0.85    inference(avatar_contradiction_clause,[],[f332])).
% 3.48/0.85  fof(f332,plain,(
% 3.48/0.85    $false | (~spl8_9 | ~spl8_16)),
% 3.48/0.85    inference(resolution,[],[f307,f171])).
% 3.48/0.85  fof(f171,plain,(
% 3.48/0.85    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | ~spl8_9),
% 3.48/0.85    inference(resolution,[],[f168,f135])).
% 3.48/0.85  fof(f168,plain,(
% 3.48/0.85    ( ! [X2,X3] : (~v1_xboole_0(X2) | r1_xboole_0(X2,X3)) )),
% 3.48/0.85    inference(resolution,[],[f60,f54])).
% 3.48/0.85  fof(f307,plain,(
% 3.48/0.85    ( ! [X1] : (~r1_xboole_0(k1_xboole_0,X1)) ) | ~spl8_16),
% 3.48/0.85    inference(avatar_component_clause,[],[f306])).
% 3.48/0.85  fof(f306,plain,(
% 3.48/0.85    spl8_16 <=> ! [X1] : ~r1_xboole_0(k1_xboole_0,X1)),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 3.48/0.85  fof(f323,plain,(
% 3.48/0.85    ~spl8_18 | spl8_19 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_4),
% 3.48/0.85    inference(avatar_split_clause,[],[f312,f108,f128,f123,f118,f113,f320,f316])).
% 3.48/0.85  fof(f123,plain,(
% 3.48/0.85    spl8_7 <=> v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 3.48/0.85    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 3.48/0.85  fof(f312,plain,(
% 3.48/0.85    v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(k2_struct_0(sK0)) | ~sP7(sK1) | ~spl8_4),
% 3.48/0.85    inference(resolution,[],[f91,f110])).
% 3.48/0.85  fof(f91,plain,(
% 3.48/0.85    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X0) | ~sP7(X1)) )),
% 3.48/0.85    inference(general_splitting,[],[f83,f90_D])).
% 3.48/0.85  fof(f83,plain,(
% 3.48/0.85    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2)) )),
% 3.48/0.85    inference(definition_unfolding,[],[f50,f49,f49,f49,f49])).
% 3.48/0.85  fof(f50,plain,(
% 3.48/0.85    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2)) )),
% 3.48/0.85    inference(cnf_transformation,[],[f27])).
% 3.48/0.85  fof(f27,plain,(
% 3.48/0.85    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.48/0.85    inference(flattening,[],[f26])).
% 3.48/0.85  fof(f26,plain,(
% 3.48/0.85    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 3.48/0.85    inference(ennf_transformation,[],[f19])).
% 3.48/0.85  fof(f19,axiom,(
% 3.48/0.85    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).
% 3.48/0.85  fof(f311,plain,(
% 3.48/0.85    spl8_16 | spl8_17 | ~spl8_9),
% 3.48/0.85    inference(avatar_split_clause,[],[f300,f133,f309,f306])).
% 3.48/0.85  fof(f300,plain,(
% 3.48/0.85    ( ! [X2,X1] : (~r2_hidden(X2,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,X1)) ) | ~spl8_9),
% 3.48/0.85    inference(superposition,[],[f57,f260])).
% 3.48/0.85  fof(f260,plain,(
% 3.48/0.85    ( ! [X6] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X6)) ) | ~spl8_9),
% 3.48/0.85    inference(resolution,[],[f251,f214])).
% 3.48/0.85  fof(f251,plain,(
% 3.48/0.85    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(k1_xboole_0,X0),X1)) ) | ~spl8_9),
% 3.48/0.85    inference(resolution,[],[f248,f185])).
% 3.48/0.85  fof(f248,plain,(
% 3.48/0.85    ( ! [X0] : (v1_xboole_0(k3_xboole_0(k1_xboole_0,X0))) ) | ~spl8_9),
% 3.48/0.85    inference(resolution,[],[f159,f171])).
% 3.48/0.85  fof(f136,plain,(
% 3.48/0.85    spl8_9),
% 3.48/0.85    inference(avatar_split_clause,[],[f45,f133])).
% 3.48/0.85  fof(f45,plain,(
% 3.48/0.85    v1_xboole_0(k1_xboole_0)),
% 3.48/0.85    inference(cnf_transformation,[],[f3])).
% 3.48/0.85  fof(f3,axiom,(
% 3.48/0.85    v1_xboole_0(k1_xboole_0)),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 3.48/0.85  fof(f131,plain,(
% 3.48/0.85    ~spl8_8),
% 3.48/0.85    inference(avatar_split_clause,[],[f37,f128])).
% 3.48/0.85  fof(f37,plain,(
% 3.48/0.85    ~v1_xboole_0(sK1)),
% 3.48/0.85    inference(cnf_transformation,[],[f25])).
% 3.48/0.85  fof(f25,plain,(
% 3.48/0.85    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 3.48/0.85    inference(flattening,[],[f24])).
% 3.48/0.85  fof(f24,plain,(
% 3.48/0.85    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 3.48/0.85    inference(ennf_transformation,[],[f21])).
% 3.48/0.85  fof(f21,negated_conjecture,(
% 3.48/0.85    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 3.48/0.85    inference(negated_conjecture,[],[f20])).
% 3.48/0.85  fof(f20,conjecture,(
% 3.48/0.85    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 3.48/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).
% 3.48/0.85  fof(f126,plain,(
% 3.48/0.85    spl8_7),
% 3.48/0.85    inference(avatar_split_clause,[],[f80,f123])).
% 3.48/0.85  fof(f80,plain,(
% 3.48/0.85    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 3.48/0.85    inference(definition_unfolding,[],[f38,f49])).
% 3.48/0.85  fof(f38,plain,(
% 3.48/0.85    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 3.48/0.85    inference(cnf_transformation,[],[f25])).
% 3.48/0.85  fof(f121,plain,(
% 3.48/0.85    spl8_6),
% 3.48/0.85    inference(avatar_split_clause,[],[f79,f118])).
% 3.48/0.85  fof(f79,plain,(
% 3.48/0.85    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 3.48/0.85    inference(definition_unfolding,[],[f39,f49])).
% 3.48/0.85  fof(f39,plain,(
% 3.48/0.85    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 3.48/0.85    inference(cnf_transformation,[],[f25])).
% 3.48/0.85  fof(f116,plain,(
% 3.48/0.85    spl8_5),
% 3.48/0.85    inference(avatar_split_clause,[],[f78,f113])).
% 3.48/0.85  fof(f78,plain,(
% 3.48/0.85    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 3.48/0.85    inference(definition_unfolding,[],[f40,f49])).
% 3.48/0.85  fof(f40,plain,(
% 3.48/0.85    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 3.48/0.85    inference(cnf_transformation,[],[f25])).
% 3.48/0.85  fof(f111,plain,(
% 3.48/0.85    spl8_4),
% 3.48/0.85    inference(avatar_split_clause,[],[f77,f108])).
% 3.48/0.85  fof(f77,plain,(
% 3.48/0.85    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 3.48/0.85    inference(definition_unfolding,[],[f41,f49])).
% 3.48/0.85  fof(f41,plain,(
% 3.48/0.85    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 3.48/0.85    inference(cnf_transformation,[],[f25])).
% 3.48/0.85  fof(f106,plain,(
% 3.48/0.85    ~spl8_3),
% 3.48/0.85    inference(avatar_split_clause,[],[f42,f103])).
% 3.48/0.85  fof(f42,plain,(
% 3.48/0.85    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 3.48/0.85    inference(cnf_transformation,[],[f25])).
% 3.48/0.85  fof(f101,plain,(
% 3.48/0.85    ~spl8_2),
% 3.48/0.85    inference(avatar_split_clause,[],[f43,f98])).
% 3.48/0.85  fof(f43,plain,(
% 3.48/0.85    ~v2_struct_0(sK0)),
% 3.48/0.85    inference(cnf_transformation,[],[f25])).
% 3.48/0.85  fof(f96,plain,(
% 3.48/0.85    spl8_1),
% 3.48/0.85    inference(avatar_split_clause,[],[f44,f93])).
% 3.48/0.85  fof(f44,plain,(
% 3.48/0.85    l1_struct_0(sK0)),
% 3.48/0.85    inference(cnf_transformation,[],[f25])).
% 3.48/0.85  % SZS output end Proof for theBenchmark
% 3.48/0.85  % (26731)------------------------------
% 3.48/0.85  % (26731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.48/0.85  % (26731)Termination reason: Refutation
% 3.48/0.85  
% 3.48/0.85  % (26731)Memory used [KB]: 14839
% 3.48/0.85  % (26731)Time elapsed: 0.428 s
% 3.48/0.85  % (26731)------------------------------
% 3.48/0.85  % (26731)------------------------------
% 3.48/0.88  % (26714)Success in time 0.501 s
%------------------------------------------------------------------------------
