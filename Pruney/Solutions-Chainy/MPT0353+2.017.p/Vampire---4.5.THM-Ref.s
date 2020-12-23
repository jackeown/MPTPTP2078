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
% DateTime   : Thu Dec  3 12:44:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 154 expanded)
%              Number of leaves         :   25 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  198 ( 338 expanded)
%              Number of equality atoms :   64 ( 110 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f793,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f61,f70,f75,f88,f111,f116,f131,f149,f160,f789,f792])).

fof(f792,plain,
    ( ~ spl3_17
    | spl3_46 ),
    inference(avatar_contradiction_clause,[],[f791])).

fof(f791,plain,
    ( $false
    | ~ spl3_17
    | spl3_46 ),
    inference(trivial_inequality_removal,[],[f790])).

fof(f790,plain,
    ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2)
    | ~ spl3_17
    | spl3_46 ),
    inference(superposition,[],[f788,f376])).

fof(f376,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k3_xboole_0(sK1,k4_xboole_0(sK0,X0))
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f370,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f370,plain,
    ( ! [X0] : k3_xboole_0(sK1,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k3_xboole_0(sK1,X0))
    | ~ spl3_17 ),
    inference(superposition,[],[f153,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f153,plain,
    ( ! [X1] : k4_xboole_0(sK1,k3_xboole_0(X1,sK1)) = k3_xboole_0(sK1,k4_xboole_0(sK0,X1))
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f151,f24])).

fof(f151,plain,
    ( ! [X1] : k3_xboole_0(k4_xboole_0(sK0,X1),sK1) = k4_xboole_0(sK1,k3_xboole_0(X1,sK1))
    | ~ spl3_17 ),
    inference(superposition,[],[f30,f148])).

fof(f148,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_17
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).

fof(f788,plain,
    ( k4_xboole_0(sK1,sK2) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_46 ),
    inference(avatar_component_clause,[],[f786])).

fof(f786,plain,
    ( spl3_46
  <=> k4_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f789,plain,
    ( ~ spl3_46
    | ~ spl3_9
    | spl3_18 ),
    inference(avatar_split_clause,[],[f784,f157,f85,f786])).

fof(f85,plain,
    ( spl3_9
  <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f157,plain,
    ( spl3_18
  <=> k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f784,plain,
    ( k4_xboole_0(sK1,sK2) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_9
    | spl3_18 ),
    inference(superposition,[],[f159,f89])).

fof(f89,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,k4_xboole_0(sK0,sK2)) = k3_xboole_0(X0,k4_xboole_0(sK0,sK2))
    | ~ spl3_9 ),
    inference(resolution,[],[f87,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f87,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f159,plain,
    ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f157])).

fof(f160,plain,
    ( ~ spl3_18
    | spl3_1
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f155,f58,f44,f34,f157])).

fof(f34,plain,
    ( spl3_1
  <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f44,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f58,plain,
    ( spl3_5
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f155,plain,
    ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2)
    | spl3_1
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f154,f63])).

fof(f63,plain,
    ( ! [X1] : k7_subset_1(sK0,sK1,X1) = k4_xboole_0(sK1,X1)
    | ~ spl3_3 ),
    inference(resolution,[],[f46,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f46,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f154,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2))
    | spl3_1
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f36,f60])).

fof(f60,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f58])).

% (10360)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
fof(f36,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f149,plain,
    ( spl3_17
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f144,f128,f108,f146])).

fof(f108,plain,
    ( spl3_12
  <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f128,plain,
    ( spl3_15
  <=> k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f144,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f130,f110])).

fof(f110,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f130,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f128])).

fof(f131,plain,
    ( spl3_15
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f126,f113,f128])).

fof(f113,plain,
    ( spl3_13
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f126,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,sK1)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f120,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f120,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_13 ),
    inference(resolution,[],[f115,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f115,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f113])).

fof(f116,plain,
    ( ~ spl3_3
    | spl3_13
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f106,f72,f113,f44])).

fof(f72,plain,
    ( spl3_7
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f106,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_7 ),
    inference(superposition,[],[f27,f74])).

fof(f74,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f111,plain,
    ( spl3_12
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f105,f72,f67,f108])).

fof(f67,plain,
    ( spl3_6
  <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f105,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f69,f74])).

fof(f69,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f88,plain,
    ( ~ spl3_2
    | spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f78,f58,f85,f39])).

fof(f39,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f78,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_5 ),
    inference(superposition,[],[f27,f60])).

fof(f75,plain,
    ( spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f65,f44,f72])).

fof(f65,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f46,f28])).

fof(f70,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f64,f44,f67])).

fof(f64,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f46,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f61,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f51,f39,f58])).

fof(f51,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f41,f28])).

fof(f41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f47,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f39])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f34])).

fof(f23,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:43:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (10355)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.45  % (10363)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (10363)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (10354)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (10365)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (10359)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f793,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f37,f42,f47,f61,f70,f75,f88,f111,f116,f131,f149,f160,f789,f792])).
% 0.21/0.48  fof(f792,plain,(
% 0.21/0.48    ~spl3_17 | spl3_46),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f791])).
% 0.21/0.48  fof(f791,plain,(
% 0.21/0.48    $false | (~spl3_17 | spl3_46)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f790])).
% 0.21/0.48  fof(f790,plain,(
% 0.21/0.48    k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) | (~spl3_17 | spl3_46)),
% 0.21/0.48    inference(superposition,[],[f788,f376])).
% 0.21/0.48  fof(f376,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(sK1,X0) = k3_xboole_0(sK1,k4_xboole_0(sK0,X0))) ) | ~spl3_17),
% 0.21/0.48    inference(forward_demodulation,[],[f370,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.48  fof(f370,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(sK1,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k3_xboole_0(sK1,X0))) ) | ~spl3_17),
% 0.21/0.48    inference(superposition,[],[f153,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    ( ! [X1] : (k4_xboole_0(sK1,k3_xboole_0(X1,sK1)) = k3_xboole_0(sK1,k4_xboole_0(sK0,X1))) ) | ~spl3_17),
% 0.21/0.48    inference(forward_demodulation,[],[f151,f24])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ( ! [X1] : (k3_xboole_0(k4_xboole_0(sK0,X1),sK1) = k4_xboole_0(sK1,k3_xboole_0(X1,sK1))) ) | ~spl3_17),
% 0.21/0.48    inference(superposition,[],[f30,f148])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f146])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    spl3_17 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).
% 0.21/0.48  fof(f788,plain,(
% 0.21/0.48    k4_xboole_0(sK1,sK2) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_46),
% 0.21/0.48    inference(avatar_component_clause,[],[f786])).
% 0.21/0.48  fof(f786,plain,(
% 0.21/0.48    spl3_46 <=> k4_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.21/0.48  fof(f789,plain,(
% 0.21/0.48    ~spl3_46 | ~spl3_9 | spl3_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f784,f157,f85,f786])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl3_9 <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    spl3_18 <=> k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.48  fof(f784,plain,(
% 0.21/0.48    k4_xboole_0(sK1,sK2) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | (~spl3_9 | spl3_18)),
% 0.21/0.48    inference(superposition,[],[f159,f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X0] : (k9_subset_1(sK0,X0,k4_xboole_0(sK0,sK2)) = k3_xboole_0(X0,k4_xboole_0(sK0,sK2))) ) | ~spl3_9),
% 0.21/0.48    inference(resolution,[],[f87,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f85])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) | spl3_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f157])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    ~spl3_18 | spl3_1 | ~spl3_3 | ~spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f155,f58,f44,f34,f157])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    spl3_1 <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl3_5 <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) | (spl3_1 | ~spl3_3 | ~spl3_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f154,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X1] : (k7_subset_1(sK0,sK1,X1) = k4_xboole_0(sK1,X1)) ) | ~spl3_3),
% 0.21/0.48    inference(resolution,[],[f46,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f44])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) | (spl3_1 | ~spl3_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f36,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f58])).
% 0.21/0.48  % (10360)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f34])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    spl3_17 | ~spl3_12 | ~spl3_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f144,f128,f108,f146])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    spl3_12 <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    spl3_15 <=> k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    sK1 = k3_xboole_0(sK0,sK1) | (~spl3_12 | ~spl3_15)),
% 0.21/0.48    inference(forward_demodulation,[],[f130,f110])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f108])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,sK1) | ~spl3_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f128])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl3_15 | ~spl3_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f126,f113,f128])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl3_13 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,sK1) | ~spl3_13),
% 0.21/0.48    inference(forward_demodulation,[],[f120,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_13),
% 0.21/0.48    inference(resolution,[],[f115,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f113])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ~spl3_3 | spl3_13 | ~spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f106,f72,f113,f44])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl3_7 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_7),
% 0.21/0.48    inference(superposition,[],[f27,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f72])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    spl3_12 | ~spl3_6 | ~spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f105,f72,f67,f108])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl3_6 <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_6 | ~spl3_7)),
% 0.21/0.48    inference(backward_demodulation,[],[f69,f74])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f67])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ~spl3_2 | spl3_9 | ~spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f78,f58,f85,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_5),
% 0.21/0.48    inference(superposition,[],[f27,f60])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl3_7 | ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f65,f44,f72])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_3),
% 0.21/0.48    inference(resolution,[],[f46,f28])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl3_6 | ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f64,f44,f67])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl3_3),
% 0.21/0.48    inference(resolution,[],[f46,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl3_5 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f51,f39,f58])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl3_2),
% 0.21/0.48    inference(resolution,[],[f41,f28])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f39])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f44])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f19,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f22,f39])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f34])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (10363)------------------------------
% 0.21/0.48  % (10363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10363)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (10363)Memory used [KB]: 11129
% 0.21/0.48  % (10363)Time elapsed: 0.065 s
% 0.21/0.48  % (10363)------------------------------
% 0.21/0.48  % (10363)------------------------------
% 0.21/0.48  % (10351)Success in time 0.115 s
%------------------------------------------------------------------------------
