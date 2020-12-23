%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 237 expanded)
%              Number of leaves         :   37 ( 100 expanded)
%              Depth                    :    9
%              Number of atoms          :  360 ( 638 expanded)
%              Number of equality atoms :   92 ( 158 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f828,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f92,f97,f103,f159,f166,f239,f250,f266,f306,f307,f434,f436,f459,f542,f560,f604,f765,f824,f825])).

fof(f825,plain,
    ( k1_xboole_0 != k3_subset_1(sK0,sK1)
    | sK1 != k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | k3_subset_1(sK0,k3_subset_1(sK0,sK1)) != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1)))
    | sK0 != k5_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1))))
    | sK1 != k5_xboole_0(k1_xboole_0,sK1)
    | sK0 = sK1 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f824,plain,
    ( spl3_67
    | ~ spl3_20
    | ~ spl3_46
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f819,f762,f601,f292,f821])).

fof(f821,plain,
    ( spl3_67
  <=> sK1 = k5_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f292,plain,
    ( spl3_20
  <=> sK1 = k5_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f601,plain,
    ( spl3_46
  <=> k1_xboole_0 = k3_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f762,plain,
    ( spl3_62
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f819,plain,
    ( sK1 = k5_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_20
    | ~ spl3_46
    | ~ spl3_62 ),
    inference(forward_demodulation,[],[f818,f49])).

fof(f49,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f818,plain,
    ( sK1 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k1_xboole_0))
    | ~ spl3_20
    | ~ spl3_46
    | ~ spl3_62 ),
    inference(forward_demodulation,[],[f817,f764])).

fof(f764,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f762])).

fof(f817,plain,
    ( sK1 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK1)))
    | ~ spl3_20
    | ~ spl3_46 ),
    inference(forward_demodulation,[],[f816,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f816,plain,
    ( sK1 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)))
    | ~ spl3_20
    | ~ spl3_46 ),
    inference(forward_demodulation,[],[f294,f603])).

fof(f603,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK1)
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f601])).

fof(f294,plain,
    ( sK1 = k5_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK1))))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f292])).

fof(f765,plain,
    ( spl3_62
    | ~ spl3_21
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f760,f601,f297,f762])).

fof(f297,plain,
    ( spl3_21
  <=> k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f760,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_21
    | ~ spl3_46 ),
    inference(forward_demodulation,[],[f299,f603])).

fof(f299,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f297])).

fof(f604,plain,
    ( spl3_46
    | ~ spl3_1
    | ~ spl3_16
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f599,f246,f236,f83,f601])).

fof(f83,plain,
    ( spl3_1
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f236,plain,
    ( spl3_16
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f246,plain,
    ( spl3_18
  <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f599,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_16
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f598,f238])).

fof(f238,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f236])).

fof(f598,plain,
    ( k1_xboole_0 = k3_subset_1(sK0,sK1)
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_1
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f596,f84])).

fof(f84,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f596,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k1_xboole_0 = k3_subset_1(sK0,sK1)
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_18 ),
    inference(superposition,[],[f77,f248])).

fof(f248,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f246])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f65,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f560,plain,
    ( spl3_41
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f548,f455,f550])).

fof(f550,plain,
    ( spl3_41
  <=> sK0 = k5_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f455,plain,
    ( spl3_35
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f548,plain,
    ( sK0 = k5_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1))))
    | ~ spl3_35 ),
    inference(resolution,[],[f457,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f457,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK0)
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f455])).

fof(f542,plain,
    ( spl3_11
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f541,f122,f163])).

fof(f163,plain,
    ( spl3_11
  <=> r2_hidden(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f122,plain,
    ( spl3_6
  <=> m1_subset_1(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f541,plain,
    ( r2_hidden(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0))
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f531,f45])).

fof(f45,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f531,plain,
    ( r2_hidden(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_6 ),
    inference(resolution,[],[f124,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f124,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f459,plain,
    ( spl3_35
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f450,f414,f455])).

fof(f414,plain,
    ( spl3_30
  <=> r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f450,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK0)
    | ~ spl3_30 ),
    inference(resolution,[],[f416,f80])).

fof(f80,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f416,plain,
    ( r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f414])).

fof(f436,plain,
    ( spl3_30
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f435,f236,f414])).

fof(f435,plain,
    ( r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f409,f45])).

fof(f409,plain,
    ( r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_16 ),
    inference(resolution,[],[f238,f56])).

fof(f434,plain,
    ( spl3_32
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f407,f236,f424])).

fof(f424,plain,
    ( spl3_32
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f407,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1)))
    | ~ spl3_16 ),
    inference(resolution,[],[f238,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f63,f55])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f307,plain,
    ( spl3_20
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f290,f83,f292])).

fof(f290,plain,
    ( sK1 = k5_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK1))))
    | ~ spl3_1 ),
    inference(resolution,[],[f84,f74])).

fof(f306,plain,
    ( spl3_21
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f289,f83,f297])).

fof(f289,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f84,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f266,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f256,f100,f122])).

fof(f100,plain,
    ( spl3_4
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f256,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f102,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f102,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f250,plain,
    ( spl3_18
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f223,f94,f246])).

fof(f94,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f223,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f96,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f96,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f239,plain,
    ( spl3_16
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f220,f94,f236])).

fof(f220,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f96,f62])).

fof(f166,plain,
    ( ~ spl3_11
    | spl3_10 ),
    inference(avatar_split_clause,[],[f160,f156,f163])).

fof(f156,plain,
    ( spl3_10
  <=> r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f160,plain,
    ( ~ r2_hidden(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0))
    | spl3_10 ),
    inference(unit_resulting_resolution,[],[f158,f80])).

fof(f158,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f156])).

fof(f159,plain,
    ( ~ spl3_10
    | spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f154,f87,f83,f156])).

fof(f87,plain,
    ( spl3_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f154,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f85,f88])).

fof(f88,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f85,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f103,plain,
    ( spl3_4
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f98,f94,f87,f100])).

fof(f98,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f96,f88])).

fof(f97,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f42,f94])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f92,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f91,f87,f83])).

fof(f91,plain,
    ( sK0 = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f43,f48])).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f43,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f90,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f81,f87,f83])).

fof(f81,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f44,f48])).

fof(f44,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:37:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (26699)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.47  % (26691)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.48  % (26699)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (26691)Refutation not found, incomplete strategy% (26691)------------------------------
% 0.21/0.48  % (26691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (26691)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (26691)Memory used [KB]: 10618
% 0.21/0.48  % (26691)Time elapsed: 0.076 s
% 0.21/0.48  % (26691)------------------------------
% 0.21/0.48  % (26691)------------------------------
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f828,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f90,f92,f97,f103,f159,f166,f239,f250,f266,f306,f307,f434,f436,f459,f542,f560,f604,f765,f824,f825])).
% 0.21/0.49  fof(f825,plain,(
% 0.21/0.49    k1_xboole_0 != k3_subset_1(sK0,sK1) | sK1 != k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | k3_subset_1(sK0,k3_subset_1(sK0,sK1)) != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1))) | sK0 != k5_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1)))) | sK1 != k5_xboole_0(k1_xboole_0,sK1) | sK0 = sK1),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f824,plain,(
% 0.21/0.49    spl3_67 | ~spl3_20 | ~spl3_46 | ~spl3_62),
% 0.21/0.49    inference(avatar_split_clause,[],[f819,f762,f601,f292,f821])).
% 0.21/0.49  fof(f821,plain,(
% 0.21/0.49    spl3_67 <=> sK1 = k5_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 0.21/0.49  fof(f292,plain,(
% 0.21/0.49    spl3_20 <=> sK1 = k5_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK1))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.49  fof(f601,plain,(
% 0.21/0.49    spl3_46 <=> k1_xboole_0 = k3_subset_1(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.21/0.49  fof(f762,plain,(
% 0.21/0.49    spl3_62 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 0.21/0.49  fof(f819,plain,(
% 0.21/0.49    sK1 = k5_xboole_0(k1_xboole_0,sK1) | (~spl3_20 | ~spl3_46 | ~spl3_62)),
% 0.21/0.49    inference(forward_demodulation,[],[f818,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.49  fof(f818,plain,(
% 0.21/0.49    sK1 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k1_xboole_0)) | (~spl3_20 | ~spl3_46 | ~spl3_62)),
% 0.21/0.49    inference(forward_demodulation,[],[f817,f764])).
% 0.21/0.49  fof(f764,plain,(
% 0.21/0.49    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) | ~spl3_62),
% 0.21/0.49    inference(avatar_component_clause,[],[f762])).
% 0.21/0.49  fof(f817,plain,(
% 0.21/0.49    sK1 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK1))) | (~spl3_20 | ~spl3_46)),
% 0.21/0.49    inference(forward_demodulation,[],[f816,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.49  fof(f816,plain,(
% 0.21/0.49    sK1 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))) | (~spl3_20 | ~spl3_46)),
% 0.21/0.49    inference(forward_demodulation,[],[f294,f603])).
% 0.21/0.49  fof(f603,plain,(
% 0.21/0.49    k1_xboole_0 = k3_subset_1(sK0,sK1) | ~spl3_46),
% 0.21/0.49    inference(avatar_component_clause,[],[f601])).
% 0.21/0.49  fof(f294,plain,(
% 0.21/0.49    sK1 = k5_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK1)))) | ~spl3_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f292])).
% 0.21/0.49  fof(f765,plain,(
% 0.21/0.49    spl3_62 | ~spl3_21 | ~spl3_46),
% 0.21/0.49    inference(avatar_split_clause,[],[f760,f601,f297,f762])).
% 0.21/0.49  fof(f297,plain,(
% 0.21/0.49    spl3_21 <=> k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.49  fof(f760,plain,(
% 0.21/0.49    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) | (~spl3_21 | ~spl3_46)),
% 0.21/0.49    inference(forward_demodulation,[],[f299,f603])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) | ~spl3_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f297])).
% 0.21/0.49  fof(f604,plain,(
% 0.21/0.49    spl3_46 | ~spl3_1 | ~spl3_16 | ~spl3_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f599,f246,f236,f83,f601])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl3_1 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    spl3_16 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    spl3_18 <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.49  fof(f599,plain,(
% 0.21/0.49    k1_xboole_0 = k3_subset_1(sK0,sK1) | (~spl3_1 | ~spl3_16 | ~spl3_18)),
% 0.21/0.49    inference(subsumption_resolution,[],[f598,f238])).
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f236])).
% 0.21/0.49  fof(f598,plain,(
% 0.21/0.49    k1_xboole_0 = k3_subset_1(sK0,sK1) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl3_1 | ~spl3_18)),
% 0.21/0.49    inference(subsumption_resolution,[],[f596,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f83])).
% 0.21/0.49  fof(f596,plain,(
% 0.21/0.49    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | k1_xboole_0 = k3_subset_1(sK0,sK1) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_18),
% 0.21/0.49    inference(superposition,[],[f77,f248])).
% 0.21/0.49  fof(f248,plain,(
% 0.21/0.49    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl3_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f246])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f65,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 0.21/0.49  fof(f560,plain,(
% 0.21/0.49    spl3_41 | ~spl3_35),
% 0.21/0.49    inference(avatar_split_clause,[],[f548,f455,f550])).
% 0.21/0.49  fof(f550,plain,(
% 0.21/0.49    spl3_41 <=> sK0 = k5_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.49  fof(f455,plain,(
% 0.21/0.49    spl3_35 <=> r1_tarski(k3_subset_1(sK0,sK1),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.49  fof(f548,plain,(
% 0.21/0.49    sK0 = k5_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1)))) | ~spl3_35),
% 0.21/0.49    inference(resolution,[],[f457,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f60,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f54,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.49  fof(f457,plain,(
% 0.21/0.49    r1_tarski(k3_subset_1(sK0,sK1),sK0) | ~spl3_35),
% 0.21/0.49    inference(avatar_component_clause,[],[f455])).
% 0.21/0.49  fof(f542,plain,(
% 0.21/0.49    spl3_11 | ~spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f541,f122,f163])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    spl3_11 <=> r2_hidden(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl3_6 <=> m1_subset_1(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f541,plain,(
% 0.21/0.49    r2_hidden(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0)) | ~spl3_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f531,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,axiom,(
% 0.21/0.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.49  fof(f531,plain,(
% 0.21/0.49    r2_hidden(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_6),
% 0.21/0.49    inference(resolution,[],[f124,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    m1_subset_1(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0)) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f122])).
% 0.21/0.49  fof(f459,plain,(
% 0.21/0.49    spl3_35 | ~spl3_30),
% 0.21/0.49    inference(avatar_split_clause,[],[f450,f414,f455])).
% 0.21/0.49  fof(f414,plain,(
% 0.21/0.49    spl3_30 <=> r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.49  fof(f450,plain,(
% 0.21/0.49    r1_tarski(k3_subset_1(sK0,sK1),sK0) | ~spl3_30),
% 0.21/0.49    inference(resolution,[],[f416,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.49    inference(rectify,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.49  fof(f416,plain,(
% 0.21/0.49    r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f414])).
% 0.21/0.49  fof(f436,plain,(
% 0.21/0.49    spl3_30 | ~spl3_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f435,f236,f414])).
% 0.21/0.49  fof(f435,plain,(
% 0.21/0.49    r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_16),
% 0.21/0.49    inference(subsumption_resolution,[],[f409,f45])).
% 0.21/0.49  fof(f409,plain,(
% 0.21/0.49    r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_16),
% 0.21/0.49    inference(resolution,[],[f238,f56])).
% 0.21/0.49  fof(f434,plain,(
% 0.21/0.49    spl3_32 | ~spl3_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f407,f236,f424])).
% 0.21/0.49  fof(f424,plain,(
% 0.21/0.49    spl3_32 <=> k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.49  fof(f407,plain,(
% 0.21/0.49    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1))) | ~spl3_16),
% 0.21/0.49    inference(resolution,[],[f238,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f63,f55])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    spl3_20 | ~spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f290,f83,f292])).
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    sK1 = k5_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK1)))) | ~spl3_1),
% 0.21/0.49    inference(resolution,[],[f84,f74])).
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    spl3_21 | ~spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f289,f83,f297])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) | ~spl3_1),
% 0.21/0.49    inference(resolution,[],[f84,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    spl3_6 | ~spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f256,f100,f122])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl3_4 <=> m1_subset_1(sK0,k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    m1_subset_1(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f102,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f100])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    spl3_18 | ~spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f223,f94,f246])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl3_3),
% 0.21/0.49    inference(resolution,[],[f96,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f94])).
% 0.21/0.49  fof(f239,plain,(
% 0.21/0.49    spl3_16 | ~spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f220,f94,f236])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f96,f62])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    ~spl3_11 | spl3_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f160,f156,f163])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    spl3_10 <=> r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ~r2_hidden(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0)) | spl3_10),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f158,f80])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | spl3_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f156])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ~spl3_10 | spl3_1 | ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f154,f87,f83,f156])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl3_2 <=> sK0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | (spl3_1 | ~spl3_2)),
% 0.21/0.49    inference(forward_demodulation,[],[f85,f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    sK0 = sK1 | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f87])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f83])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    spl3_4 | ~spl3_2 | ~spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f98,f94,f87,f100])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | (~spl3_2 | ~spl3_3)),
% 0.21/0.49    inference(forward_demodulation,[],[f96,f88])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f42,f94])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(flattening,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.21/0.49    inference(negated_conjecture,[],[f20])).
% 0.21/0.49  fof(f20,conjecture,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl3_1 | spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f91,f87,f83])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    sK0 = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.49    inference(forward_demodulation,[],[f43,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f81,f87,f83])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.49    inference(forward_demodulation,[],[f44,f48])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (26699)------------------------------
% 0.21/0.49  % (26699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (26699)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (26699)Memory used [KB]: 6652
% 0.21/0.49  % (26699)Time elapsed: 0.077 s
% 0.21/0.49  % (26699)------------------------------
% 0.21/0.49  % (26699)------------------------------
% 0.21/0.49  % (26673)Success in time 0.135 s
%------------------------------------------------------------------------------
