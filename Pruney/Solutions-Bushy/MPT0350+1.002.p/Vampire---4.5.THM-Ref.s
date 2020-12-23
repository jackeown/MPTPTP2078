%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0350+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 230 expanded)
%              Number of leaves         :   30 (  97 expanded)
%              Depth                    :   11
%              Number of atoms          :  328 ( 651 expanded)
%              Number of equality atoms :   77 ( 141 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f302,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f62,f93,f96,f123,f138,f164,f192,f193,f200,f202,f211,f229,f233,f278,f301])).

fof(f301,plain,(
    spl3_26 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | spl3_26 ),
    inference(trivial_inequality_removal,[],[f296])).

fof(f296,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_26 ),
    inference(superposition,[],[f277,f63])).

fof(f63,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f35,f33])).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f277,plain,
    ( k1_xboole_0 != k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl3_26 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl3_26
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f278,plain,
    ( ~ spl3_26
    | spl3_5
    | ~ spl3_11
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f274,f231,f227,f140,f91,f276])).

fof(f91,plain,
    ( spl3_5
  <=> sK0 = k2_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f140,plain,
    ( spl3_11
  <=> sK0 = k3_subset_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f227,plain,
    ( spl3_18
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f231,plain,
    ( spl3_19
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f274,plain,
    ( k1_xboole_0 != k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl3_5
    | ~ spl3_11
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f273,f228])).

fof(f228,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f227])).

fof(f273,plain,
    ( sK0 != k2_xboole_0(k1_xboole_0,sK0)
    | spl3_5
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f270,f141])).

fof(f141,plain,
    ( sK0 = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f140])).

fof(f270,plain,
    ( sK0 != k2_xboole_0(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | spl3_5
    | ~ spl3_19 ),
    inference(superposition,[],[f92,f232])).

fof(f232,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f231])).

fof(f92,plain,
    ( sK0 != k2_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f233,plain,
    ( spl3_19
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f225,f150,f136,f231])).

fof(f136,plain,
    ( spl3_10
  <=> m1_subset_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f150,plain,
    ( spl3_14
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f225,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(resolution,[],[f215,f137])).

fof(f137,plain,
    ( m1_subset_1(sK1,k1_xboole_0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f215,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_xboole_0)
        | k1_xboole_0 = X5 )
    | ~ spl3_14 ),
    inference(resolution,[],[f195,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f195,plain,
    ( ! [X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_xboole_0) )
    | ~ spl3_14 ),
    inference(resolution,[],[f151,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f151,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f229,plain,
    ( spl3_18
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f224,f157,f150,f227])).

fof(f157,plain,
    ( spl3_16
  <=> m1_subset_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f224,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(resolution,[],[f215,f158])).

fof(f158,plain,
    ( m1_subset_1(sK0,k1_xboole_0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f157])).

fof(f211,plain,
    ( spl3_16
    | ~ spl3_12
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f210,f140,f118,f143,f157])).

fof(f143,plain,
    ( spl3_12
  <=> m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f118,plain,
    ( spl3_8
  <=> k1_xboole_0 = k1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f210,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | m1_subset_1(sK0,k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f209,f119])).

fof(f119,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f209,plain,
    ( m1_subset_1(sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f207,f119])).

fof(f207,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl3_11 ),
    inference(superposition,[],[f41,f141])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f202,plain,
    ( spl3_11
    | ~ spl3_12
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f174,f118,f143,f140])).

fof(f174,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | sK0 = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl3_8 ),
    inference(superposition,[],[f72,f119])).

fof(f72,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k1_xboole_0) = X0 ) ),
    inference(superposition,[],[f42,f32])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f200,plain,
    ( spl3_12
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f198,f150,f143])).

fof(f198,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl3_14 ),
    inference(resolution,[],[f194,f151])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | m1_subset_1(k1_xboole_0,X0) )
    | ~ spl3_14 ),
    inference(resolution,[],[f151,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f193,plain,
    ( spl3_13
    | spl3_14
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f175,f118,f150,f147])).

fof(f147,plain,
    ( spl3_13
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_xboole_0)
        | sK0 = k2_xboole_0(X3,k4_xboole_0(sK0,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f175,plain,
    ( ! [X3] :
        ( v1_xboole_0(k1_xboole_0)
        | ~ m1_subset_1(X3,k1_xboole_0)
        | sK0 = k2_xboole_0(X3,k4_xboole_0(sK0,X3)) )
    | ~ spl3_8 ),
    inference(superposition,[],[f76,f119])).

fof(f76,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(k1_zfmisc_1(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k2_xboole_0(X2,k4_xboole_0(X3,X2)) = X3 ) ),
    inference(resolution,[],[f71,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(resolution,[],[f40,f49])).

fof(f49,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f27,plain,(
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

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f192,plain,
    ( spl3_9
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f189,f147,f136,f121])).

fof(f121,plain,
    ( spl3_9
  <=> sK0 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f189,plain,
    ( sK0 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(resolution,[],[f148,f137])).

fof(f148,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_xboole_0)
        | sK0 = k2_xboole_0(X3,k4_xboole_0(sK0,X3)) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f147])).

fof(f164,plain,
    ( ~ spl3_2
    | spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f162,f121,f91,f55])).

fof(f55,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f162,plain,
    ( sK0 = k2_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_9 ),
    inference(superposition,[],[f122,f42])).

fof(f122,plain,
    ( sK0 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f138,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f124,f118,f55,f136])).

fof(f124,plain,
    ( m1_subset_1(sK1,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(superposition,[],[f56,f119])).

fof(f56,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f123,plain,
    ( spl3_8
    | spl3_9
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f114,f55,f121,f118])).

fof(f114,plain,
    ( sK0 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | k1_xboole_0 = k1_zfmisc_1(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f84,f56])).

fof(f84,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | k2_xboole_0(X6,k4_xboole_0(X7,X6)) = X7
      | k1_xboole_0 = k1_zfmisc_1(X7) ) ),
    inference(resolution,[],[f76,f34])).

fof(f96,plain,
    ( ~ spl3_2
    | spl3_4 ),
    inference(avatar_split_clause,[],[f94,f88,f55])).

fof(f88,plain,
    ( spl3_4
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f94,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_4 ),
    inference(resolution,[],[f89,f41])).

fof(f89,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f93,plain,
    ( ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | spl3_3 ),
    inference(avatar_split_clause,[],[f85,f60,f91,f88,f55])).

fof(f60,plain,
    ( spl3_3
  <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f85,plain,
    ( sK0 != k2_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_3 ),
    inference(superposition,[],[f61,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f61,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f62,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f58,f51,f60])).

fof(f51,plain,
    ( spl3_1
  <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f58,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl3_1 ),
    inference(forward_demodulation,[],[f52,f31])).

fof(f31,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f52,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f57,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f29,f55])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f53,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f30,f51])).

fof(f30,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------
