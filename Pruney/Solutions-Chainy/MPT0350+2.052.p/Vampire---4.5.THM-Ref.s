%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:57 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 288 expanded)
%              Number of leaves         :   41 ( 123 expanded)
%              Depth                    :    9
%              Number of atoms          :  350 ( 598 expanded)
%              Number of equality atoms :   82 ( 150 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f940,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f89,f94,f101,f106,f124,f144,f151,f158,f177,f199,f250,f272,f277,f293,f310,f364,f383,f419,f429,f440,f887,f903,f932])).

fof(f932,plain,
    ( spl3_24
    | ~ spl3_99
    | ~ spl3_101 ),
    inference(avatar_contradiction_clause,[],[f931])).

fof(f931,plain,
    ( $false
    | spl3_24
    | ~ spl3_99
    | ~ spl3_101 ),
    inference(subsumption_resolution,[],[f930,f271])).

fof(f271,plain,
    ( sK0 != k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl3_24
  <=> sK0 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f930,plain,
    ( sK0 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_99
    | ~ spl3_101 ),
    inference(forward_demodulation,[],[f929,f40])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f929,plain,
    ( k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_99
    | ~ spl3_101 ),
    inference(backward_demodulation,[],[f896,f922])).

fof(f922,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_101 ),
    inference(superposition,[],[f902,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f902,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl3_101 ),
    inference(avatar_component_clause,[],[f900])).

fof(f900,plain,
    ( spl3_101
  <=> k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).

fof(f896,plain,
    ( k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
    | ~ spl3_99 ),
    inference(superposition,[],[f49,f886])).

fof(f886,plain,
    ( sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_99 ),
    inference(avatar_component_clause,[],[f884])).

fof(f884,plain,
    ( spl3_99
  <=> sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f903,plain,
    ( spl3_101
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f391,f380,f900])).

fof(f380,plain,
    ( spl3_39
  <=> r1_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f391,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl3_39 ),
    inference(resolution,[],[f382,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f382,plain,
    ( r1_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f380])).

fof(f887,plain,
    ( spl3_99
    | ~ spl3_29
    | ~ spl3_46
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f491,f437,f426,f307,f884])).

fof(f307,plain,
    ( spl3_29
  <=> r1_tarski(k5_xboole_0(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f426,plain,
    ( spl3_46
  <=> k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f437,plain,
    ( spl3_48
  <=> r1_xboole_0(k5_xboole_0(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f491,plain,
    ( sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_29
    | ~ spl3_46
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f480,f488])).

fof(f488,plain,
    ( sK0 = k2_xboole_0(sK0,sK1)
    | ~ spl3_29
    | ~ spl3_46
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f487,f40])).

fof(f487,plain,
    ( k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_29
    | ~ spl3_46
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f479,f447])).

fof(f447,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK1)
    | ~ spl3_29
    | ~ spl3_48 ),
    inference(backward_demodulation,[],[f312,f446])).

fof(f446,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK1,sK1),sK1)
    | ~ spl3_48 ),
    inference(resolution,[],[f439,f58])).

fof(f439,plain,
    ( r1_xboole_0(k5_xboole_0(sK1,sK1),sK1)
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f437])).

fof(f312,plain,
    ( k5_xboole_0(sK1,sK1) = k3_xboole_0(k5_xboole_0(sK1,sK1),sK1)
    | ~ spl3_29 ),
    inference(resolution,[],[f309,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f309,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK1),sK1)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f307])).

fof(f479,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK0,sK1)
    | ~ spl3_46 ),
    inference(superposition,[],[f428,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f428,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK0,sK1)
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f426])).

fof(f480,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,sK1)
    | ~ spl3_46 ),
    inference(superposition,[],[f428,f45])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f440,plain,
    ( spl3_48
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f430,f416,f437])).

fof(f416,plain,
    ( spl3_44
  <=> k5_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f430,plain,
    ( r1_xboole_0(k5_xboole_0(sK1,sK1),sK1)
    | ~ spl3_44 ),
    inference(superposition,[],[f42,f418])).

fof(f418,plain,
    ( k5_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK1)
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f416])).

fof(f42,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f429,plain,
    ( spl3_46
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f205,f196,f426])).

fof(f196,plain,
    ( spl3_16
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f205,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK0,sK1)
    | ~ spl3_16 ),
    inference(superposition,[],[f49,f198])).

fof(f198,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f196])).

fof(f419,plain,
    ( spl3_44
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f258,f247,f416])).

fof(f247,plain,
    ( spl3_21
  <=> sK1 = k3_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f258,plain,
    ( k5_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK1)
    | ~ spl3_21 ),
    inference(superposition,[],[f48,f249])).

fof(f249,plain,
    ( sK1 = k3_xboole_0(sK1,sK1)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f247])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f383,plain,
    ( spl3_39
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f370,f361,f380])).

fof(f361,plain,
    ( spl3_37
  <=> k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f370,plain,
    ( r1_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl3_37 ),
    inference(superposition,[],[f42,f363])).

fof(f363,plain,
    ( k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f361])).

fof(f364,plain,
    ( spl3_37
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f207,f196,f361])).

fof(f207,plain,
    ( k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl3_16 ),
    inference(superposition,[],[f48,f198])).

fof(f310,plain,
    ( spl3_29
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f304,f290,f307])).

fof(f290,plain,
    ( spl3_27
  <=> r2_hidden(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f304,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK1),sK1)
    | ~ spl3_27 ),
    inference(resolution,[],[f292,f70])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f292,plain,
    ( r2_hidden(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f290])).

fof(f293,plain,
    ( spl3_27
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f283,f274,f290])).

fof(f274,plain,
    ( spl3_25
  <=> m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f283,plain,
    ( r2_hidden(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1))
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f281,f38])).

fof(f38,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f281,plain,
    ( r2_hidden(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ spl3_25 ),
    inference(resolution,[],[f276,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f276,plain,
    ( m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f274])).

fof(f277,plain,
    ( spl3_25
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f259,f247,f174,f274])).

fof(f174,plain,
    ( spl3_13
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f259,plain,
    ( m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1))
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(backward_demodulation,[],[f187,f258])).

fof(f187,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK1),k1_zfmisc_1(sK1))
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f185,f184])).

fof(f184,plain,
    ( k4_xboole_0(sK1,sK1) = k3_subset_1(sK1,sK1)
    | ~ spl3_13 ),
    inference(resolution,[],[f176,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f176,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f174])).

fof(f185,plain,
    ( m1_subset_1(k3_subset_1(sK1,sK1),k1_zfmisc_1(sK1))
    | ~ spl3_13 ),
    inference(resolution,[],[f176,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f272,plain,
    ( ~ spl3_24
    | spl3_10
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f214,f196,f148,f269])).

fof(f148,plain,
    ( spl3_10
  <=> sK0 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f214,plain,
    ( sK0 != k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | spl3_10
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f150,f207])).

fof(f150,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f148])).

fof(f250,plain,
    ( spl3_21
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f153,f141,f247])).

fof(f141,plain,
    ( spl3_9
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f153,plain,
    ( sK1 = k3_xboole_0(sK1,sK1)
    | ~ spl3_9 ),
    inference(resolution,[],[f143,f54])).

fof(f143,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f141])).

fof(f199,plain,
    ( spl3_16
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f127,f121,f196])).

fof(f121,plain,
    ( spl3_7
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f127,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_7 ),
    inference(superposition,[],[f123,f44])).

fof(f123,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f177,plain,
    ( spl3_13
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f166,f155,f174])).

fof(f155,plain,
    ( spl3_11
  <=> r2_hidden(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f166,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f165,f38])).

fof(f165,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1))
    | m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl3_11 ),
    inference(resolution,[],[f157,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f157,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f155])).

fof(f158,plain,
    ( spl3_11
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f152,f141,f155])).

fof(f152,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK1))
    | ~ spl3_9 ),
    inference(resolution,[],[f143,f71])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f151,plain,
    ( ~ spl3_10
    | ~ spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f126,f98,f86,f74,f148])).

fof(f74,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f86,plain,
    ( spl3_2
  <=> sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f98,plain,
    ( spl3_4
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f126,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f125,f100])).

fof(f100,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f125,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_1
    | spl3_2 ),
    inference(superposition,[],[f88,f78])).

fof(f78,plain,
    ( ! [X0] :
        ( k4_subset_1(sK0,sK1,X0) = k2_xboole_0(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl3_1 ),
    inference(resolution,[],[f76,f65])).

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
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f76,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f88,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f144,plain,
    ( spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f132,f121,f141])).

fof(f132,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl3_7 ),
    inference(superposition,[],[f43,f123])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f124,plain,
    ( spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f119,f103,f121])).

fof(f103,plain,
    ( spl3_5
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f119,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f105,f54])).

fof(f105,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f106,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f95,f91,f103])).

fof(f91,plain,
    ( spl3_3
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f95,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f93,f70])).

fof(f93,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f101,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f83,f74,f98])).

fof(f83,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f80,f79])).

fof(f79,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f76,f56])).

fof(f80,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(resolution,[],[f76,f55])).

fof(f94,plain,
    ( spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f84,f74,f91])).

fof(f84,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f81,f38])).

fof(f81,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(resolution,[],[f76,f53])).

fof(f89,plain,
    ( ~ spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f82,f74,f86])).

fof(f82,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f72,f79])).

fof(f72,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f37,f39])).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f37,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f77,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f36,f74])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:55:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (7574)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (7561)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.50  % (7586)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (7577)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (7562)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (7565)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (7570)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (7567)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (7568)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (7563)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (7566)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (7573)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (7588)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.52  % (7583)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (7579)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (7591)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (7587)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (7578)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (7582)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (7572)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (7575)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (7564)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (7571)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (7585)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.42/0.54  % (7585)Refutation not found, incomplete strategy% (7585)------------------------------
% 1.42/0.54  % (7585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (7585)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (7585)Memory used [KB]: 10746
% 1.42/0.54  % (7585)Time elapsed: 0.138 s
% 1.42/0.54  % (7585)------------------------------
% 1.42/0.54  % (7585)------------------------------
% 1.42/0.54  % (7580)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.54  % (7592)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.55  % (7579)Refutation not found, incomplete strategy% (7579)------------------------------
% 1.42/0.55  % (7579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (7579)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (7579)Memory used [KB]: 10618
% 1.42/0.55  % (7579)Time elapsed: 0.140 s
% 1.42/0.55  % (7579)------------------------------
% 1.42/0.55  % (7579)------------------------------
% 1.42/0.55  % (7590)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.42/0.55  % (7581)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.42/0.55  % (7589)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.55  % (7576)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.55/0.57  % (7582)Refutation found. Thanks to Tanya!
% 1.55/0.57  % SZS status Theorem for theBenchmark
% 1.55/0.57  % SZS output start Proof for theBenchmark
% 1.55/0.57  fof(f940,plain,(
% 1.55/0.57    $false),
% 1.55/0.57    inference(avatar_sat_refutation,[],[f77,f89,f94,f101,f106,f124,f144,f151,f158,f177,f199,f250,f272,f277,f293,f310,f364,f383,f419,f429,f440,f887,f903,f932])).
% 1.55/0.57  fof(f932,plain,(
% 1.55/0.57    spl3_24 | ~spl3_99 | ~spl3_101),
% 1.55/0.57    inference(avatar_contradiction_clause,[],[f931])).
% 1.55/0.57  fof(f931,plain,(
% 1.55/0.57    $false | (spl3_24 | ~spl3_99 | ~spl3_101)),
% 1.55/0.57    inference(subsumption_resolution,[],[f930,f271])).
% 1.55/0.57  fof(f271,plain,(
% 1.55/0.57    sK0 != k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | spl3_24),
% 1.55/0.57    inference(avatar_component_clause,[],[f269])).
% 1.55/0.57  fof(f269,plain,(
% 1.55/0.57    spl3_24 <=> sK0 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.55/0.57  fof(f930,plain,(
% 1.55/0.57    sK0 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | (~spl3_99 | ~spl3_101)),
% 1.55/0.57    inference(forward_demodulation,[],[f929,f40])).
% 1.55/0.57  fof(f40,plain,(
% 1.55/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.55/0.57    inference(cnf_transformation,[],[f8])).
% 1.55/0.57  fof(f8,axiom,(
% 1.55/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.55/0.57  fof(f929,plain,(
% 1.55/0.57    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) | (~spl3_99 | ~spl3_101)),
% 1.55/0.57    inference(backward_demodulation,[],[f896,f922])).
% 1.55/0.57  fof(f922,plain,(
% 1.55/0.57    k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~spl3_101),
% 1.55/0.57    inference(superposition,[],[f902,f44])).
% 1.55/0.57  fof(f44,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f1])).
% 1.55/0.57  fof(f1,axiom,(
% 1.55/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.55/0.57  fof(f902,plain,(
% 1.55/0.57    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1) | ~spl3_101),
% 1.55/0.57    inference(avatar_component_clause,[],[f900])).
% 1.55/0.57  fof(f900,plain,(
% 1.55/0.57    spl3_101 <=> k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).
% 1.55/0.57  fof(f896,plain,(
% 1.55/0.57    k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | ~spl3_99),
% 1.55/0.57    inference(superposition,[],[f49,f886])).
% 1.55/0.57  fof(f886,plain,(
% 1.55/0.57    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~spl3_99),
% 1.55/0.57    inference(avatar_component_clause,[],[f884])).
% 1.55/0.57  fof(f884,plain,(
% 1.55/0.57    spl3_99 <=> sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).
% 1.55/0.57  fof(f49,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f11])).
% 1.55/0.57  fof(f11,axiom,(
% 1.55/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.55/0.57  fof(f903,plain,(
% 1.55/0.57    spl3_101 | ~spl3_39),
% 1.55/0.57    inference(avatar_split_clause,[],[f391,f380,f900])).
% 1.55/0.57  fof(f380,plain,(
% 1.55/0.57    spl3_39 <=> r1_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 1.55/0.57  fof(f391,plain,(
% 1.55/0.57    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1) | ~spl3_39),
% 1.55/0.57    inference(resolution,[],[f382,f58])).
% 1.55/0.57  fof(f58,plain,(
% 1.55/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.55/0.57    inference(cnf_transformation,[],[f3])).
% 1.55/0.57  fof(f3,axiom,(
% 1.55/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.55/0.57  fof(f382,plain,(
% 1.55/0.57    r1_xboole_0(k5_xboole_0(sK0,sK1),sK1) | ~spl3_39),
% 1.55/0.57    inference(avatar_component_clause,[],[f380])).
% 1.55/0.57  fof(f887,plain,(
% 1.55/0.57    spl3_99 | ~spl3_29 | ~spl3_46 | ~spl3_48),
% 1.55/0.57    inference(avatar_split_clause,[],[f491,f437,f426,f307,f884])).
% 1.55/0.57  fof(f307,plain,(
% 1.55/0.57    spl3_29 <=> r1_tarski(k5_xboole_0(sK1,sK1),sK1)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 1.55/0.57  fof(f426,plain,(
% 1.55/0.57    spl3_46 <=> k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK0,sK1)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 1.55/0.57  fof(f437,plain,(
% 1.55/0.57    spl3_48 <=> r1_xboole_0(k5_xboole_0(sK1,sK1),sK1)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 1.55/0.57  fof(f491,plain,(
% 1.55/0.57    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | (~spl3_29 | ~spl3_46 | ~spl3_48)),
% 1.55/0.57    inference(forward_demodulation,[],[f480,f488])).
% 1.55/0.57  fof(f488,plain,(
% 1.55/0.57    sK0 = k2_xboole_0(sK0,sK1) | (~spl3_29 | ~spl3_46 | ~spl3_48)),
% 1.55/0.57    inference(forward_demodulation,[],[f487,f40])).
% 1.55/0.57  fof(f487,plain,(
% 1.55/0.57    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k1_xboole_0) | (~spl3_29 | ~spl3_46 | ~spl3_48)),
% 1.55/0.57    inference(forward_demodulation,[],[f479,f447])).
% 1.55/0.57  fof(f447,plain,(
% 1.55/0.57    k1_xboole_0 = k5_xboole_0(sK1,sK1) | (~spl3_29 | ~spl3_48)),
% 1.55/0.57    inference(backward_demodulation,[],[f312,f446])).
% 1.55/0.57  fof(f446,plain,(
% 1.55/0.57    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK1,sK1),sK1) | ~spl3_48),
% 1.55/0.57    inference(resolution,[],[f439,f58])).
% 1.55/0.57  fof(f439,plain,(
% 1.55/0.57    r1_xboole_0(k5_xboole_0(sK1,sK1),sK1) | ~spl3_48),
% 1.55/0.57    inference(avatar_component_clause,[],[f437])).
% 1.55/0.57  fof(f312,plain,(
% 1.55/0.57    k5_xboole_0(sK1,sK1) = k3_xboole_0(k5_xboole_0(sK1,sK1),sK1) | ~spl3_29),
% 1.55/0.57    inference(resolution,[],[f309,f54])).
% 1.55/0.57  fof(f54,plain,(
% 1.55/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.55/0.57    inference(cnf_transformation,[],[f31])).
% 1.55/0.57  fof(f31,plain,(
% 1.55/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.55/0.57    inference(ennf_transformation,[],[f6])).
% 1.55/0.57  fof(f6,axiom,(
% 1.55/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.55/0.57  fof(f309,plain,(
% 1.55/0.57    r1_tarski(k5_xboole_0(sK1,sK1),sK1) | ~spl3_29),
% 1.55/0.57    inference(avatar_component_clause,[],[f307])).
% 1.55/0.57  fof(f479,plain,(
% 1.55/0.57    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK0,sK1) | ~spl3_46),
% 1.55/0.57    inference(superposition,[],[f428,f64])).
% 1.55/0.57  fof(f64,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f10])).
% 1.55/0.57  fof(f10,axiom,(
% 1.55/0.57    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.55/0.57  fof(f428,plain,(
% 1.55/0.57    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK0,sK1) | ~spl3_46),
% 1.55/0.57    inference(avatar_component_clause,[],[f426])).
% 1.55/0.57  fof(f480,plain,(
% 1.55/0.57    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,sK1) | ~spl3_46),
% 1.55/0.57    inference(superposition,[],[f428,f45])).
% 1.55/0.57  fof(f45,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f2])).
% 1.55/0.57  fof(f2,axiom,(
% 1.55/0.57    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.55/0.57  fof(f440,plain,(
% 1.55/0.57    spl3_48 | ~spl3_44),
% 1.55/0.57    inference(avatar_split_clause,[],[f430,f416,f437])).
% 1.55/0.57  fof(f416,plain,(
% 1.55/0.57    spl3_44 <=> k5_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK1)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 1.55/0.57  fof(f430,plain,(
% 1.55/0.57    r1_xboole_0(k5_xboole_0(sK1,sK1),sK1) | ~spl3_44),
% 1.55/0.57    inference(superposition,[],[f42,f418])).
% 1.55/0.57  fof(f418,plain,(
% 1.55/0.57    k5_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK1) | ~spl3_44),
% 1.55/0.57    inference(avatar_component_clause,[],[f416])).
% 1.55/0.57  fof(f42,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f9])).
% 1.55/0.57  fof(f9,axiom,(
% 1.55/0.57    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.55/0.57  fof(f429,plain,(
% 1.55/0.57    spl3_46 | ~spl3_16),
% 1.55/0.57    inference(avatar_split_clause,[],[f205,f196,f426])).
% 1.55/0.57  fof(f196,plain,(
% 1.55/0.57    spl3_16 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.55/0.57  fof(f205,plain,(
% 1.55/0.57    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK0,sK1) | ~spl3_16),
% 1.55/0.57    inference(superposition,[],[f49,f198])).
% 1.55/0.57  fof(f198,plain,(
% 1.55/0.57    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_16),
% 1.55/0.57    inference(avatar_component_clause,[],[f196])).
% 1.55/0.57  fof(f419,plain,(
% 1.55/0.57    spl3_44 | ~spl3_21),
% 1.55/0.57    inference(avatar_split_clause,[],[f258,f247,f416])).
% 1.55/0.57  fof(f247,plain,(
% 1.55/0.57    spl3_21 <=> sK1 = k3_xboole_0(sK1,sK1)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.55/0.57  fof(f258,plain,(
% 1.55/0.57    k5_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK1) | ~spl3_21),
% 1.55/0.57    inference(superposition,[],[f48,f249])).
% 1.55/0.57  fof(f249,plain,(
% 1.55/0.57    sK1 = k3_xboole_0(sK1,sK1) | ~spl3_21),
% 1.55/0.57    inference(avatar_component_clause,[],[f247])).
% 1.55/0.57  fof(f48,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f4])).
% 1.55/0.57  fof(f4,axiom,(
% 1.55/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.55/0.57  fof(f383,plain,(
% 1.55/0.57    spl3_39 | ~spl3_37),
% 1.55/0.57    inference(avatar_split_clause,[],[f370,f361,f380])).
% 1.55/0.57  fof(f361,plain,(
% 1.55/0.57    spl3_37 <=> k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 1.55/0.57  fof(f370,plain,(
% 1.55/0.57    r1_xboole_0(k5_xboole_0(sK0,sK1),sK1) | ~spl3_37),
% 1.55/0.57    inference(superposition,[],[f42,f363])).
% 1.55/0.57  fof(f363,plain,(
% 1.55/0.57    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) | ~spl3_37),
% 1.55/0.57    inference(avatar_component_clause,[],[f361])).
% 1.55/0.57  fof(f364,plain,(
% 1.55/0.57    spl3_37 | ~spl3_16),
% 1.55/0.57    inference(avatar_split_clause,[],[f207,f196,f361])).
% 1.55/0.57  fof(f207,plain,(
% 1.55/0.57    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK1) | ~spl3_16),
% 1.55/0.57    inference(superposition,[],[f48,f198])).
% 1.55/0.57  fof(f310,plain,(
% 1.55/0.57    spl3_29 | ~spl3_27),
% 1.55/0.57    inference(avatar_split_clause,[],[f304,f290,f307])).
% 1.55/0.57  fof(f290,plain,(
% 1.55/0.57    spl3_27 <=> r2_hidden(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 1.55/0.57  fof(f304,plain,(
% 1.55/0.57    r1_tarski(k5_xboole_0(sK1,sK1),sK1) | ~spl3_27),
% 1.55/0.57    inference(resolution,[],[f292,f70])).
% 1.55/0.57  fof(f70,plain,(
% 1.55/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.55/0.57    inference(equality_resolution,[],[f60])).
% 1.55/0.57  fof(f60,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.55/0.57    inference(cnf_transformation,[],[f18])).
% 1.55/0.57  fof(f18,axiom,(
% 1.55/0.57    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.55/0.57  fof(f292,plain,(
% 1.55/0.57    r2_hidden(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1)) | ~spl3_27),
% 1.55/0.57    inference(avatar_component_clause,[],[f290])).
% 1.55/0.57  fof(f293,plain,(
% 1.55/0.57    spl3_27 | ~spl3_25),
% 1.55/0.57    inference(avatar_split_clause,[],[f283,f274,f290])).
% 1.55/0.57  fof(f274,plain,(
% 1.55/0.57    spl3_25 <=> m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.55/0.57  fof(f283,plain,(
% 1.55/0.57    r2_hidden(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1)) | ~spl3_25),
% 1.55/0.57    inference(subsumption_resolution,[],[f281,f38])).
% 1.55/0.57  fof(f38,plain,(
% 1.55/0.57    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f24])).
% 1.55/0.57  fof(f24,axiom,(
% 1.55/0.57    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.55/0.57  fof(f281,plain,(
% 1.55/0.57    r2_hidden(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) | ~spl3_25),
% 1.55/0.57    inference(resolution,[],[f276,f53])).
% 1.55/0.57  fof(f53,plain,(
% 1.55/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f30])).
% 1.55/0.57  fof(f30,plain,(
% 1.55/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.55/0.57    inference(ennf_transformation,[],[f20])).
% 1.55/0.57  fof(f20,axiom,(
% 1.55/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.55/0.57  fof(f276,plain,(
% 1.55/0.57    m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1)) | ~spl3_25),
% 1.55/0.57    inference(avatar_component_clause,[],[f274])).
% 1.55/0.57  fof(f277,plain,(
% 1.55/0.57    spl3_25 | ~spl3_13 | ~spl3_21),
% 1.55/0.57    inference(avatar_split_clause,[],[f259,f247,f174,f274])).
% 1.55/0.57  fof(f174,plain,(
% 1.55/0.57    spl3_13 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.55/0.57  fof(f259,plain,(
% 1.55/0.57    m1_subset_1(k5_xboole_0(sK1,sK1),k1_zfmisc_1(sK1)) | (~spl3_13 | ~spl3_21)),
% 1.55/0.57    inference(backward_demodulation,[],[f187,f258])).
% 1.55/0.57  fof(f187,plain,(
% 1.55/0.57    m1_subset_1(k4_xboole_0(sK1,sK1),k1_zfmisc_1(sK1)) | ~spl3_13),
% 1.55/0.57    inference(forward_demodulation,[],[f185,f184])).
% 1.55/0.57  fof(f184,plain,(
% 1.55/0.57    k4_xboole_0(sK1,sK1) = k3_subset_1(sK1,sK1) | ~spl3_13),
% 1.55/0.57    inference(resolution,[],[f176,f56])).
% 1.55/0.57  fof(f56,plain,(
% 1.55/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f33])).
% 1.55/0.57  fof(f33,plain,(
% 1.55/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.57    inference(ennf_transformation,[],[f22])).
% 1.55/0.57  fof(f22,axiom,(
% 1.55/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.55/0.57  fof(f176,plain,(
% 1.55/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl3_13),
% 1.55/0.57    inference(avatar_component_clause,[],[f174])).
% 1.55/0.57  fof(f185,plain,(
% 1.55/0.57    m1_subset_1(k3_subset_1(sK1,sK1),k1_zfmisc_1(sK1)) | ~spl3_13),
% 1.55/0.57    inference(resolution,[],[f176,f55])).
% 1.55/0.57  fof(f55,plain,(
% 1.55/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f32])).
% 1.55/0.57  fof(f32,plain,(
% 1.55/0.57    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.57    inference(ennf_transformation,[],[f23])).
% 1.55/0.57  fof(f23,axiom,(
% 1.55/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.55/0.57  fof(f272,plain,(
% 1.55/0.57    ~spl3_24 | spl3_10 | ~spl3_16),
% 1.55/0.57    inference(avatar_split_clause,[],[f214,f196,f148,f269])).
% 1.55/0.57  fof(f148,plain,(
% 1.55/0.57    spl3_10 <=> sK0 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.55/0.57  fof(f214,plain,(
% 1.55/0.57    sK0 != k2_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | (spl3_10 | ~spl3_16)),
% 1.55/0.57    inference(backward_demodulation,[],[f150,f207])).
% 1.55/0.57  fof(f150,plain,(
% 1.55/0.57    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | spl3_10),
% 1.55/0.57    inference(avatar_component_clause,[],[f148])).
% 1.55/0.57  fof(f250,plain,(
% 1.55/0.57    spl3_21 | ~spl3_9),
% 1.55/0.57    inference(avatar_split_clause,[],[f153,f141,f247])).
% 1.55/0.57  fof(f141,plain,(
% 1.55/0.57    spl3_9 <=> r1_tarski(sK1,sK1)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.55/0.57  fof(f153,plain,(
% 1.55/0.57    sK1 = k3_xboole_0(sK1,sK1) | ~spl3_9),
% 1.55/0.57    inference(resolution,[],[f143,f54])).
% 1.55/0.57  fof(f143,plain,(
% 1.55/0.57    r1_tarski(sK1,sK1) | ~spl3_9),
% 1.55/0.57    inference(avatar_component_clause,[],[f141])).
% 1.55/0.57  fof(f199,plain,(
% 1.55/0.57    spl3_16 | ~spl3_7),
% 1.55/0.57    inference(avatar_split_clause,[],[f127,f121,f196])).
% 1.55/0.57  fof(f121,plain,(
% 1.55/0.57    spl3_7 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.55/0.57  fof(f127,plain,(
% 1.55/0.57    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_7),
% 1.55/0.57    inference(superposition,[],[f123,f44])).
% 1.55/0.57  fof(f123,plain,(
% 1.55/0.57    sK1 = k3_xboole_0(sK1,sK0) | ~spl3_7),
% 1.55/0.57    inference(avatar_component_clause,[],[f121])).
% 1.55/0.57  fof(f177,plain,(
% 1.55/0.57    spl3_13 | ~spl3_11),
% 1.55/0.57    inference(avatar_split_clause,[],[f166,f155,f174])).
% 1.55/0.57  fof(f155,plain,(
% 1.55/0.57    spl3_11 <=> r2_hidden(sK1,k1_zfmisc_1(sK1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.55/0.57  fof(f166,plain,(
% 1.55/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl3_11),
% 1.55/0.57    inference(subsumption_resolution,[],[f165,f38])).
% 1.55/0.57  fof(f165,plain,(
% 1.55/0.57    v1_xboole_0(k1_zfmisc_1(sK1)) | m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl3_11),
% 1.55/0.57    inference(resolution,[],[f157,f52])).
% 1.55/0.57  fof(f52,plain,(
% 1.55/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f30])).
% 1.55/0.57  fof(f157,plain,(
% 1.55/0.57    r2_hidden(sK1,k1_zfmisc_1(sK1)) | ~spl3_11),
% 1.55/0.57    inference(avatar_component_clause,[],[f155])).
% 1.55/0.57  fof(f158,plain,(
% 1.55/0.57    spl3_11 | ~spl3_9),
% 1.55/0.57    inference(avatar_split_clause,[],[f152,f141,f155])).
% 1.55/0.57  fof(f152,plain,(
% 1.55/0.57    r2_hidden(sK1,k1_zfmisc_1(sK1)) | ~spl3_9),
% 1.55/0.57    inference(resolution,[],[f143,f71])).
% 1.55/0.57  fof(f71,plain,(
% 1.55/0.57    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 1.55/0.57    inference(equality_resolution,[],[f59])).
% 1.55/0.57  fof(f59,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.55/0.57    inference(cnf_transformation,[],[f18])).
% 1.55/0.57  fof(f151,plain,(
% 1.55/0.57    ~spl3_10 | ~spl3_1 | spl3_2 | ~spl3_4),
% 1.55/0.57    inference(avatar_split_clause,[],[f126,f98,f86,f74,f148])).
% 1.55/0.57  fof(f74,plain,(
% 1.55/0.57    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.55/0.57  fof(f86,plain,(
% 1.55/0.57    spl3_2 <=> sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.55/0.57  fof(f98,plain,(
% 1.55/0.57    spl3_4 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.55/0.57  fof(f126,plain,(
% 1.55/0.57    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | (~spl3_1 | spl3_2 | ~spl3_4)),
% 1.55/0.57    inference(subsumption_resolution,[],[f125,f100])).
% 1.55/0.57  fof(f100,plain,(
% 1.55/0.57    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_4),
% 1.55/0.57    inference(avatar_component_clause,[],[f98])).
% 1.55/0.57  fof(f125,plain,(
% 1.55/0.57    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl3_1 | spl3_2)),
% 1.55/0.57    inference(superposition,[],[f88,f78])).
% 1.55/0.57  fof(f78,plain,(
% 1.55/0.57    ( ! [X0] : (k4_subset_1(sK0,sK1,X0) = k2_xboole_0(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | ~spl3_1),
% 1.55/0.57    inference(resolution,[],[f76,f65])).
% 1.55/0.57  fof(f65,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f35])).
% 1.55/0.57  fof(f35,plain,(
% 1.55/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.57    inference(flattening,[],[f34])).
% 1.55/0.57  fof(f34,plain,(
% 1.55/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.55/0.57    inference(ennf_transformation,[],[f25])).
% 1.55/0.57  fof(f25,axiom,(
% 1.55/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.55/0.57  fof(f76,plain,(
% 1.55/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 1.55/0.57    inference(avatar_component_clause,[],[f74])).
% 1.55/0.57  fof(f88,plain,(
% 1.55/0.57    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) | spl3_2),
% 1.55/0.57    inference(avatar_component_clause,[],[f86])).
% 1.55/0.57  fof(f144,plain,(
% 1.55/0.57    spl3_9 | ~spl3_7),
% 1.55/0.57    inference(avatar_split_clause,[],[f132,f121,f141])).
% 1.55/0.57  fof(f132,plain,(
% 1.55/0.57    r1_tarski(sK1,sK1) | ~spl3_7),
% 1.55/0.57    inference(superposition,[],[f43,f123])).
% 1.55/0.57  fof(f43,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f5])).
% 1.55/0.57  fof(f5,axiom,(
% 1.55/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.55/0.57  fof(f124,plain,(
% 1.55/0.57    spl3_7 | ~spl3_5),
% 1.55/0.57    inference(avatar_split_clause,[],[f119,f103,f121])).
% 1.55/0.57  fof(f103,plain,(
% 1.55/0.57    spl3_5 <=> r1_tarski(sK1,sK0)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.55/0.57  fof(f119,plain,(
% 1.55/0.57    sK1 = k3_xboole_0(sK1,sK0) | ~spl3_5),
% 1.55/0.57    inference(resolution,[],[f105,f54])).
% 1.55/0.57  fof(f105,plain,(
% 1.55/0.57    r1_tarski(sK1,sK0) | ~spl3_5),
% 1.55/0.57    inference(avatar_component_clause,[],[f103])).
% 1.55/0.57  fof(f106,plain,(
% 1.55/0.57    spl3_5 | ~spl3_3),
% 1.55/0.57    inference(avatar_split_clause,[],[f95,f91,f103])).
% 1.55/0.57  fof(f91,plain,(
% 1.55/0.57    spl3_3 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.55/0.57  fof(f95,plain,(
% 1.55/0.57    r1_tarski(sK1,sK0) | ~spl3_3),
% 1.55/0.57    inference(resolution,[],[f93,f70])).
% 1.55/0.57  fof(f93,plain,(
% 1.55/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_3),
% 1.55/0.57    inference(avatar_component_clause,[],[f91])).
% 1.55/0.57  fof(f101,plain,(
% 1.55/0.57    spl3_4 | ~spl3_1),
% 1.55/0.57    inference(avatar_split_clause,[],[f83,f74,f98])).
% 1.55/0.57  fof(f83,plain,(
% 1.55/0.57    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_1),
% 1.55/0.57    inference(forward_demodulation,[],[f80,f79])).
% 1.55/0.57  fof(f79,plain,(
% 1.55/0.57    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_1),
% 1.55/0.57    inference(resolution,[],[f76,f56])).
% 1.55/0.57  fof(f80,plain,(
% 1.55/0.57    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_1),
% 1.55/0.57    inference(resolution,[],[f76,f55])).
% 1.55/0.57  fof(f94,plain,(
% 1.55/0.57    spl3_3 | ~spl3_1),
% 1.55/0.57    inference(avatar_split_clause,[],[f84,f74,f91])).
% 1.55/0.57  fof(f84,plain,(
% 1.55/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 1.55/0.57    inference(subsumption_resolution,[],[f81,f38])).
% 1.55/0.57  fof(f81,plain,(
% 1.55/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_1),
% 1.55/0.57    inference(resolution,[],[f76,f53])).
% 1.55/0.57  fof(f89,plain,(
% 1.55/0.57    ~spl3_2 | ~spl3_1),
% 1.55/0.57    inference(avatar_split_clause,[],[f82,f74,f86])).
% 1.55/0.57  fof(f82,plain,(
% 1.55/0.57    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) | ~spl3_1),
% 1.55/0.57    inference(backward_demodulation,[],[f72,f79])).
% 1.55/0.57  fof(f72,plain,(
% 1.55/0.57    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.55/0.57    inference(forward_demodulation,[],[f37,f39])).
% 1.55/0.57  fof(f39,plain,(
% 1.55/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.55/0.57    inference(cnf_transformation,[],[f21])).
% 1.55/0.57  fof(f21,axiom,(
% 1.55/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.55/0.57  fof(f37,plain,(
% 1.55/0.57    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.55/0.57    inference(cnf_transformation,[],[f28])).
% 1.55/0.57  fof(f28,plain,(
% 1.55/0.57    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.57    inference(ennf_transformation,[],[f27])).
% 1.55/0.57  fof(f27,negated_conjecture,(
% 1.55/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.55/0.57    inference(negated_conjecture,[],[f26])).
% 1.55/0.57  fof(f26,conjecture,(
% 1.55/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 1.55/0.57  fof(f77,plain,(
% 1.55/0.57    spl3_1),
% 1.55/0.57    inference(avatar_split_clause,[],[f36,f74])).
% 1.55/0.57  fof(f36,plain,(
% 1.55/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.55/0.57    inference(cnf_transformation,[],[f28])).
% 1.55/0.57  % SZS output end Proof for theBenchmark
% 1.55/0.57  % (7582)------------------------------
% 1.55/0.57  % (7582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (7582)Termination reason: Refutation
% 1.55/0.57  
% 1.55/0.57  % (7582)Memory used [KB]: 11385
% 1.55/0.57  % (7582)Time elapsed: 0.174 s
% 1.55/0.57  % (7582)------------------------------
% 1.55/0.57  % (7582)------------------------------
% 1.55/0.58  % (7557)Success in time 0.217 s
%------------------------------------------------------------------------------
