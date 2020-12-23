%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 214 expanded)
%              Number of leaves         :   29 (  82 expanded)
%              Depth                    :    9
%              Number of atoms          :  332 ( 576 expanded)
%              Number of equality atoms :   71 ( 136 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f276,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f98,f103,f108,f113,f140,f148,f166,f183,f210,f223,f225,f232,f245,f275])).

% (13313)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f275,plain,
    ( ~ spl11_8
    | ~ spl11_10
    | ~ spl11_17 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_17 ),
    inference(unit_resulting_resolution,[],[f193,f41,f270])).

fof(f270,plain,
    ( ! [X5] :
        ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,X5)
        | r2_hidden(sK0,X5) )
    | ~ spl11_17 ),
    inference(superposition,[],[f70,f244])).

fof(f244,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl11_17
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f193,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl11_8
    | ~ spl11_10 ),
    inference(backward_demodulation,[],[f143,f165])).

fof(f165,plain,
    ( k1_xboole_0 = sK2
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl11_10
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f143,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl11_8
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f245,plain,
    ( spl11_17
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f235,f229,f163,f142,f242])).

fof(f229,plain,
    ( spl11_16
  <=> sP9(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f235,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_16 ),
    inference(resolution,[],[f233,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f233,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl11_8
    | ~ spl11_10
    | ~ spl11_16 ),
    inference(resolution,[],[f231,f199])).

fof(f199,plain,
    ( ! [X0,X1] :
        ( ~ sP9(k1_xboole_0,X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl11_8
    | ~ spl11_10 ),
    inference(resolution,[],[f193,f86])).

fof(f86,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | ~ sP9(X2,X1) ) ),
    inference(general_splitting,[],[f61,f85_D])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) != X1
      | sP9(X2,X1) ) ),
    inference(cnf_transformation,[],[f85_D])).

fof(f85_D,plain,(
    ! [X1,X2] :
      ( ! [X0] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | k1_relset_1(X1,X0,X2) != X1 )
    <=> ~ sP9(X2,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) != X1
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f231,plain,
    ( sP9(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f229])).

fof(f232,plain,
    ( spl11_16
    | ~ spl11_6
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f227,f163,f133,f229])).

fof(f133,plain,
    ( spl11_6
  <=> sP9(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f227,plain,
    ( sP9(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl11_6
    | ~ spl11_10 ),
    inference(forward_demodulation,[],[f135,f165])).

fof(f135,plain,
    ( sP9(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f225,plain,
    ( spl11_2
    | ~ spl11_14
    | spl11_15 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl11_2
    | ~ spl11_14
    | spl11_15 ),
    inference(unit_resulting_resolution,[],[f97,f209,f40,f222,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f222,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | spl11_15 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl11_15
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f209,plain,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl11_14
  <=> v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f97,plain,
    ( k1_xboole_0 != sK1
    | spl11_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl11_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f223,plain,
    ( ~ spl11_15
    | spl11_7
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f218,f163,f137,f220])).

fof(f137,plain,
    ( spl11_7
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f218,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | spl11_7
    | ~ spl11_10 ),
    inference(forward_demodulation,[],[f139,f165])).

fof(f139,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | spl11_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f210,plain,
    ( spl11_14
    | ~ spl11_4
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f188,f163,f105,f207])).

fof(f105,plain,
    ( spl11_4
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f188,plain,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl11_4
    | ~ spl11_10 ),
    inference(backward_demodulation,[],[f107,f165])).

fof(f107,plain,
    ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f183,plain,
    ( ~ spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_9 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_9 ),
    inference(unit_resulting_resolution,[],[f92,f97,f102,f147,f107,f112,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f112,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl11_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f147,plain,
    ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl11_9
  <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f102,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl11_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f92,plain,
    ( v1_funct_1(sK2)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl11_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f166,plain,
    ( spl11_10
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f150,f142,f163])).

fof(f150,plain,
    ( k1_xboole_0 = sK2
    | ~ spl11_8 ),
    inference(resolution,[],[f143,f44])).

fof(f148,plain,
    ( spl11_8
    | spl11_9
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f131,f110,f145,f142])).

fof(f131,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl11_5 ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl11_5 ),
    inference(superposition,[],[f125,f123])).

fof(f123,plain,
    ( ! [X2] :
        ( sK0 = k1_mcart_1(X2)
        | ~ r2_hidden(X2,sK2) )
    | ~ spl11_5 ),
    inference(resolution,[],[f121,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f62,f67])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f121,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl11_5 ),
    inference(resolution,[],[f112,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f125,plain,
    ( ! [X4] :
        ( r2_hidden(k1_mcart_1(X4),k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X4,sK2) )
    | ~ spl11_5 ),
    inference(resolution,[],[f121,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f140,plain,
    ( spl11_6
    | ~ spl11_7
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f118,f110,f137,f133])).

fof(f118,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | sP9(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl11_5 ),
    inference(resolution,[],[f112,f85])).

fof(f113,plain,(
    spl11_5 ),
    inference(avatar_split_clause,[],[f68,f110])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f36,f67])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f108,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f69,f105])).

fof(f69,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f35,f67])).

fof(f35,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f103,plain,(
    ~ spl11_3 ),
    inference(avatar_split_clause,[],[f38,f100])).

fof(f38,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f98,plain,(
    ~ spl11_2 ),
    inference(avatar_split_clause,[],[f37,f95])).

fof(f37,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f93,plain,(
    spl11_1 ),
    inference(avatar_split_clause,[],[f34,f90])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (13322)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (13314)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (13306)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (13304)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (13322)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f276,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f93,f98,f103,f108,f113,f140,f148,f166,f183,f210,f223,f225,f232,f245,f275])).
% 0.21/0.52  % (13313)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  fof(f275,plain,(
% 0.21/0.52    ~spl11_8 | ~spl11_10 | ~spl11_17),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f271])).
% 0.21/0.52  fof(f271,plain,(
% 0.21/0.52    $false | (~spl11_8 | ~spl11_10 | ~spl11_17)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f193,f41,f270])).
% 0.21/0.52  fof(f270,plain,(
% 0.21/0.52    ( ! [X5] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,X5) | r2_hidden(sK0,X5)) ) | ~spl11_17),
% 0.21/0.52    inference(superposition,[],[f70,f244])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl11_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f242])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    spl11_17 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f48,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f42,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f45,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl11_8 | ~spl11_10)),
% 0.21/0.52    inference(backward_demodulation,[],[f143,f165])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl11_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f163])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    spl11_10 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl11_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f142])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    spl11_8 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    spl11_17 | ~spl11_8 | ~spl11_10 | ~spl11_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f235,f229,f163,f142,f242])).
% 0.21/0.52  fof(f229,plain,(
% 0.21/0.52    spl11_16 <=> sP9(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).
% 0.21/0.52  fof(f235,plain,(
% 0.21/0.52    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | (~spl11_8 | ~spl11_10 | ~spl11_16)),
% 0.21/0.52    inference(resolution,[],[f233,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.21/0.52  fof(f233,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) ) | (~spl11_8 | ~spl11_10 | ~spl11_16)),
% 0.21/0.52    inference(resolution,[],[f231,f199])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sP9(k1_xboole_0,X1) | ~r2_hidden(X0,X1)) ) | (~spl11_8 | ~spl11_10)),
% 0.21/0.52    inference(resolution,[],[f193,f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ( ! [X2,X3,X1] : (r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) | ~r2_hidden(X3,X1) | ~sP9(X2,X1)) )),
% 0.21/0.52    inference(general_splitting,[],[f61,f85_D])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1 | sP9(X2,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f85_D])).
% 0.21/0.52  fof(f85_D,plain,(
% 0.21/0.52    ( ! [X1,X2] : (( ! [X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1) ) <=> ~sP9(X2,X1)) )),
% 0.21/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1 | ~r2_hidden(X3,X1) | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    sP9(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl11_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f229])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    spl11_16 | ~spl11_6 | ~spl11_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f227,f163,f133,f229])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    spl11_6 <=> sP9(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 0.21/0.52  fof(f227,plain,(
% 0.21/0.52    sP9(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl11_6 | ~spl11_10)),
% 0.21/0.52    inference(forward_demodulation,[],[f135,f165])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    sP9(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl11_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f133])).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    spl11_2 | ~spl11_14 | spl11_15),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f224])).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    $false | (spl11_2 | ~spl11_14 | spl11_15)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f97,f209,f40,f222,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f222,plain,(
% 0.21/0.52    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | spl11_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f220])).
% 0.21/0.52  fof(f220,plain,(
% 0.21/0.52    spl11_15 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl11_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f207])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    spl11_14 <=> v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    k1_xboole_0 != sK1 | spl11_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f95])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    spl11_2 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    ~spl11_15 | spl11_7 | ~spl11_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f218,f163,f137,f220])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    spl11_7 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | (spl11_7 | ~spl11_10)),
% 0.21/0.52    inference(forward_demodulation,[],[f139,f165])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | spl11_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f137])).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    spl11_14 | ~spl11_4 | ~spl11_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f188,f163,f105,f207])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    spl11_4 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | (~spl11_4 | ~spl11_10)),
% 0.21/0.52    inference(backward_demodulation,[],[f107,f165])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl11_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f105])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    ~spl11_1 | spl11_2 | spl11_3 | ~spl11_4 | ~spl11_5 | ~spl11_9),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f174])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    $false | (~spl11_1 | spl11_2 | spl11_3 | ~spl11_4 | ~spl11_5 | ~spl11_9)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f92,f97,f102,f147,f107,f112,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.52    inference(flattening,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl11_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f110])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    spl11_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl11_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f145])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    spl11_9 <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl11_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    spl11_3 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    v1_funct_1(sK2) | ~spl11_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    spl11_1 <=> v1_funct_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    spl11_10 | ~spl11_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f150,f142,f163])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl11_8),
% 0.21/0.52    inference(resolution,[],[f143,f44])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    spl11_8 | spl11_9 | ~spl11_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f131,f110,f145,f142])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK2)) ) | ~spl11_5),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f130])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK2)) ) | ~spl11_5),
% 0.21/0.52    inference(superposition,[],[f125,f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    ( ! [X2] : (sK0 = k1_mcart_1(X2) | ~r2_hidden(X2,sK2)) ) | ~spl11_5),
% 0.21/0.52    inference(resolution,[],[f121,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.21/0.52    inference(definition_unfolding,[],[f62,f67])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    ( ! [X2] : (r2_hidden(X2,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~r2_hidden(X2,sK2)) ) | ~spl11_5),
% 0.21/0.52    inference(resolution,[],[f112,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ( ! [X4] : (r2_hidden(k1_mcart_1(X4),k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X4,sK2)) ) | ~spl11_5),
% 0.21/0.52    inference(resolution,[],[f121,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    spl11_6 | ~spl11_7 | ~spl11_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f118,f110,f137,f133])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | sP9(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl11_5),
% 0.21/0.52    inference(resolution,[],[f112,f85])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    spl11_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f68,f110])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.52    inference(definition_unfolding,[],[f36,f67])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.52    inference(negated_conjecture,[],[f17])).
% 0.21/0.52  fof(f17,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    spl11_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f69,f105])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.52    inference(definition_unfolding,[],[f35,f67])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ~spl11_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f38,f100])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ~spl11_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f37,f95])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    spl11_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f34,f90])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    v1_funct_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (13322)------------------------------
% 0.21/0.52  % (13322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13322)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (13322)Memory used [KB]: 10874
% 0.21/0.52  % (13322)Time elapsed: 0.065 s
% 0.21/0.52  % (13322)------------------------------
% 0.21/0.52  % (13322)------------------------------
% 0.21/0.53  % (13299)Success in time 0.167 s
%------------------------------------------------------------------------------
