%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:04 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 200 expanded)
%              Number of leaves         :   29 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :  326 ( 525 expanded)
%              Number of equality atoms :   62 ( 119 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f283,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f100,f105,f111,f125,f149,f160,f180,f193,f244,f267,f269,f276,f282])).

fof(f282,plain,
    ( ~ spl12_10
    | ~ spl12_12
    | ~ spl12_22 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_22 ),
    inference(unit_resulting_resolution,[],[f48,f73,f277,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f277,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_22 ),
    inference(resolution,[],[f275,f212])).

fof(f212,plain,
    ( ! [X2,X1] :
        ( ~ sP10(k1_xboole_0,X2)
        | ~ r2_hidden(X1,X2) )
    | ~ spl12_10
    | ~ spl12_12 ),
    inference(resolution,[],[f205,f88])).

fof(f88,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | ~ sP10(X2,X1) ) ),
    inference(general_splitting,[],[f64,f87_D])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) != X1
      | sP10(X2,X1) ) ),
    inference(cnf_transformation,[],[f87_D])).

fof(f87_D,plain,(
    ! [X1,X2] :
      ( ! [X0] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | k1_relset_1(X1,X0,X2) != X1 )
    <=> ~ sP10(X2,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) != X1
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f205,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl12_10
    | ~ spl12_12 ),
    inference(backward_demodulation,[],[f155,f179])).

fof(f179,plain,
    ( k1_xboole_0 = sK2
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl12_12
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f155,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl12_10
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f275,plain,
    ( sP10(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl12_22 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl12_22
  <=> sP10(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f73,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f42,f70])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f276,plain,
    ( spl12_22
    | ~ spl12_8
    | ~ spl12_12 ),
    inference(avatar_split_clause,[],[f271,f177,f142,f273])).

fof(f142,plain,
    ( spl12_8
  <=> sP10(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f271,plain,
    ( sP10(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl12_8
    | ~ spl12_12 ),
    inference(forward_demodulation,[],[f144,f179])).

fof(f144,plain,
    ( sP10(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f142])).

fof(f269,plain,
    ( spl12_2
    | ~ spl12_18
    | spl12_21 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | spl12_2
    | ~ spl12_18
    | spl12_21 ),
    inference(unit_resulting_resolution,[],[f99,f243,f44,f266,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f16])).

% (24313)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f16,axiom,(
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

fof(f266,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | spl12_21 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl12_21
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_21])])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f243,plain,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl12_18
  <=> v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f99,plain,
    ( k1_xboole_0 != sK1
    | spl12_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl12_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f267,plain,
    ( ~ spl12_21
    | spl12_9
    | ~ spl12_12 ),
    inference(avatar_split_clause,[],[f252,f177,f146,f264])).

fof(f146,plain,
    ( spl12_9
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f252,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | spl12_9
    | ~ spl12_12 ),
    inference(forward_demodulation,[],[f148,f179])).

fof(f148,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | spl12_9 ),
    inference(avatar_component_clause,[],[f146])).

fof(f244,plain,
    ( spl12_18
    | ~ spl12_4
    | ~ spl12_12 ),
    inference(avatar_split_clause,[],[f199,f177,f108,f241])).

fof(f108,plain,
    ( spl12_4
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f199,plain,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl12_4
    | ~ spl12_12 ),
    inference(backward_demodulation,[],[f110,f179])).

fof(f110,plain,
    ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f193,plain,
    ( ~ spl12_1
    | spl12_2
    | spl12_3
    | ~ spl12_4
    | ~ spl12_7
    | ~ spl12_11 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl12_1
    | spl12_2
    | spl12_3
    | ~ spl12_4
    | ~ spl12_7
    | ~ spl12_11 ),
    inference(unit_resulting_resolution,[],[f94,f99,f104,f159,f110,f124,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f124,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl12_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f159,plain,
    ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl12_11
  <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f104,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl12_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl12_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f94,plain,
    ( v1_funct_1(sK2)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl12_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f180,plain,
    ( spl12_12
    | ~ spl12_10 ),
    inference(avatar_split_clause,[],[f163,f154,f177])).

fof(f163,plain,
    ( k1_xboole_0 = sK2
    | ~ spl12_10 ),
    inference(resolution,[],[f155,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f160,plain,
    ( spl12_10
    | spl12_11
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f152,f122,f157,f154])).

fof(f152,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl12_7 ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl12_7 ),
    inference(superposition,[],[f137,f135])).

fof(f135,plain,
    ( ! [X2] :
        ( sK0 = k1_mcart_1(X2)
        | ~ r2_hidden(X2,sK2) )
    | ~ spl12_7 ),
    inference(resolution,[],[f133,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f65,f70])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f133,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl12_7 ),
    inference(resolution,[],[f124,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f137,plain,
    ( ! [X4] :
        ( r2_hidden(k1_mcart_1(X4),k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X4,sK2) )
    | ~ spl12_7 ),
    inference(resolution,[],[f133,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f149,plain,
    ( spl12_8
    | ~ spl12_9
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f130,f122,f146,f142])).

fof(f130,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | sP10(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl12_7 ),
    inference(resolution,[],[f124,f87])).

fof(f125,plain,(
    spl12_7 ),
    inference(avatar_split_clause,[],[f71,f122])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f39,f70])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f111,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f72,f108])).

fof(f72,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f38,f70])).

fof(f38,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f105,plain,(
    ~ spl12_3 ),
    inference(avatar_split_clause,[],[f41,f102])).

fof(f41,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f100,plain,(
    ~ spl12_2 ),
    inference(avatar_split_clause,[],[f40,f97])).

fof(f40,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f95,plain,(
    spl12_1 ),
    inference(avatar_split_clause,[],[f37,f92])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:56:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (24307)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.47  % (24299)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (24296)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (24294)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (24293)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (24295)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (24312)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.54  % (24297)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.54  % (24318)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.54  % (24303)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.32/0.54  % (24314)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.55  % (24306)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.55  % (24310)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.55  % (24301)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.32/0.55  % (24319)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.55  % (24321)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.32/0.55  % (24309)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.55  % (24320)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.55  % (24309)Refutation not found, incomplete strategy% (24309)------------------------------
% 1.32/0.55  % (24309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (24309)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (24309)Memory used [KB]: 10618
% 1.32/0.55  % (24309)Time elapsed: 0.135 s
% 1.32/0.55  % (24309)------------------------------
% 1.32/0.55  % (24309)------------------------------
% 1.32/0.55  % (24311)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.32/0.56  % (24292)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.56  % (24304)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.56  % (24305)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.56/0.56  % (24317)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.56/0.56  % (24302)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.56/0.56  % (24316)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.56/0.56  % (24314)Refutation found. Thanks to Tanya!
% 1.56/0.56  % SZS status Theorem for theBenchmark
% 1.56/0.56  % SZS output start Proof for theBenchmark
% 1.56/0.56  fof(f283,plain,(
% 1.56/0.56    $false),
% 1.56/0.56    inference(avatar_sat_refutation,[],[f95,f100,f105,f111,f125,f149,f160,f180,f193,f244,f267,f269,f276,f282])).
% 1.56/0.56  fof(f282,plain,(
% 1.56/0.56    ~spl12_10 | ~spl12_12 | ~spl12_22),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f278])).
% 1.56/0.56  fof(f278,plain,(
% 1.56/0.56    $false | (~spl12_10 | ~spl12_12 | ~spl12_22)),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f48,f73,f277,f50])).
% 1.56/0.56  fof(f50,plain,(
% 1.56/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f25])).
% 1.56/0.56  fof(f25,plain,(
% 1.56/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.56/0.56    inference(flattening,[],[f24])).
% 1.56/0.56  fof(f24,plain,(
% 1.56/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.56/0.56    inference(ennf_transformation,[],[f9])).
% 1.56/0.56  fof(f9,axiom,(
% 1.56/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.56/0.56  fof(f277,plain,(
% 1.56/0.56    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) ) | (~spl12_10 | ~spl12_12 | ~spl12_22)),
% 1.56/0.56    inference(resolution,[],[f275,f212])).
% 1.56/0.56  fof(f212,plain,(
% 1.56/0.56    ( ! [X2,X1] : (~sP10(k1_xboole_0,X2) | ~r2_hidden(X1,X2)) ) | (~spl12_10 | ~spl12_12)),
% 1.56/0.56    inference(resolution,[],[f205,f88])).
% 1.56/0.56  fof(f88,plain,(
% 1.56/0.56    ( ! [X2,X3,X1] : (r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2) | ~r2_hidden(X3,X1) | ~sP10(X2,X1)) )),
% 1.56/0.56    inference(general_splitting,[],[f64,f87_D])).
% 1.56/0.56  fof(f87,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1 | sP10(X2,X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f87_D])).
% 1.56/0.56  fof(f87_D,plain,(
% 1.56/0.56    ( ! [X1,X2] : (( ! [X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1) ) <=> ~sP10(X2,X1)) )),
% 1.56/0.56    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).
% 1.56/0.56  fof(f64,plain,(
% 1.56/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1 | ~r2_hidden(X3,X1) | r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f31])).
% 1.56/0.56  fof(f31,plain,(
% 1.56/0.56    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.56/0.56    inference(ennf_transformation,[],[f12])).
% 1.56/0.56  fof(f12,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 1.56/0.56  fof(f205,plain,(
% 1.56/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl12_10 | ~spl12_12)),
% 1.56/0.56    inference(backward_demodulation,[],[f155,f179])).
% 1.56/0.56  fof(f179,plain,(
% 1.56/0.56    k1_xboole_0 = sK2 | ~spl12_12),
% 1.56/0.56    inference(avatar_component_clause,[],[f177])).
% 1.56/0.56  fof(f177,plain,(
% 1.56/0.56    spl12_12 <=> k1_xboole_0 = sK2),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).
% 1.56/0.56  fof(f155,plain,(
% 1.56/0.56    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl12_10),
% 1.56/0.56    inference(avatar_component_clause,[],[f154])).
% 1.56/0.56  fof(f154,plain,(
% 1.56/0.56    spl12_10 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 1.56/0.56  fof(f275,plain,(
% 1.56/0.56    sP10(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl12_22),
% 1.56/0.56    inference(avatar_component_clause,[],[f273])).
% 1.56/0.56  fof(f273,plain,(
% 1.56/0.56    spl12_22 <=> sP10(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).
% 1.56/0.56  fof(f73,plain,(
% 1.56/0.56    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 1.56/0.56    inference(definition_unfolding,[],[f42,f70])).
% 1.56/0.56  fof(f70,plain,(
% 1.56/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.56/0.56    inference(definition_unfolding,[],[f45,f69])).
% 1.56/0.56  fof(f69,plain,(
% 1.56/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.56/0.56    inference(definition_unfolding,[],[f49,f53])).
% 1.56/0.56  fof(f53,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f4])).
% 1.56/0.56  fof(f4,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.56/0.56  fof(f49,plain,(
% 1.56/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f3])).
% 1.56/0.56  fof(f3,axiom,(
% 1.56/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.56/0.56  fof(f45,plain,(
% 1.56/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f2])).
% 1.56/0.56  fof(f2,axiom,(
% 1.56/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.56/0.56  fof(f42,plain,(
% 1.56/0.56    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f5])).
% 1.56/0.56  fof(f5,axiom,(
% 1.56/0.56    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.56/0.56  fof(f48,plain,(
% 1.56/0.56    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f6])).
% 1.56/0.56  fof(f6,axiom,(
% 1.56/0.56    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 1.56/0.56  fof(f276,plain,(
% 1.56/0.56    spl12_22 | ~spl12_8 | ~spl12_12),
% 1.56/0.56    inference(avatar_split_clause,[],[f271,f177,f142,f273])).
% 1.56/0.56  fof(f142,plain,(
% 1.56/0.56    spl12_8 <=> sP10(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 1.56/0.56  fof(f271,plain,(
% 1.56/0.56    sP10(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl12_8 | ~spl12_12)),
% 1.56/0.56    inference(forward_demodulation,[],[f144,f179])).
% 1.56/0.56  fof(f144,plain,(
% 1.56/0.56    sP10(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl12_8),
% 1.56/0.56    inference(avatar_component_clause,[],[f142])).
% 1.56/0.56  fof(f269,plain,(
% 1.56/0.56    spl12_2 | ~spl12_18 | spl12_21),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f268])).
% 1.56/0.56  fof(f268,plain,(
% 1.56/0.56    $false | (spl12_2 | ~spl12_18 | spl12_21)),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f99,f243,f44,f266,f61])).
% 1.56/0.56  fof(f61,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f30])).
% 1.56/0.56  fof(f30,plain,(
% 1.56/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.56    inference(flattening,[],[f29])).
% 1.56/0.56  fof(f29,plain,(
% 1.56/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.56    inference(ennf_transformation,[],[f16])).
% 1.56/0.56  % (24313)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.56/0.56  fof(f16,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.56/0.56  fof(f266,plain,(
% 1.56/0.56    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | spl12_21),
% 1.56/0.56    inference(avatar_component_clause,[],[f264])).
% 1.56/0.56  fof(f264,plain,(
% 1.56/0.56    spl12_21 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_21])])).
% 1.56/0.56  fof(f44,plain,(
% 1.56/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f8])).
% 1.56/0.56  fof(f8,axiom,(
% 1.56/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.56/0.56  fof(f243,plain,(
% 1.56/0.56    v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl12_18),
% 1.56/0.56    inference(avatar_component_clause,[],[f241])).
% 1.56/0.56  fof(f241,plain,(
% 1.56/0.56    spl12_18 <=> v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).
% 1.56/0.56  fof(f99,plain,(
% 1.56/0.56    k1_xboole_0 != sK1 | spl12_2),
% 1.56/0.56    inference(avatar_component_clause,[],[f97])).
% 1.56/0.56  fof(f97,plain,(
% 1.56/0.56    spl12_2 <=> k1_xboole_0 = sK1),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.56/0.56  fof(f267,plain,(
% 1.56/0.56    ~spl12_21 | spl12_9 | ~spl12_12),
% 1.56/0.56    inference(avatar_split_clause,[],[f252,f177,f146,f264])).
% 1.56/0.56  fof(f146,plain,(
% 1.56/0.56    spl12_9 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 1.56/0.56  fof(f252,plain,(
% 1.56/0.56    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | (spl12_9 | ~spl12_12)),
% 1.56/0.56    inference(forward_demodulation,[],[f148,f179])).
% 1.56/0.56  fof(f148,plain,(
% 1.56/0.56    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | spl12_9),
% 1.56/0.56    inference(avatar_component_clause,[],[f146])).
% 1.56/0.56  fof(f244,plain,(
% 1.56/0.56    spl12_18 | ~spl12_4 | ~spl12_12),
% 1.56/0.56    inference(avatar_split_clause,[],[f199,f177,f108,f241])).
% 1.56/0.56  fof(f108,plain,(
% 1.56/0.56    spl12_4 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 1.56/0.56  fof(f199,plain,(
% 1.56/0.56    v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | (~spl12_4 | ~spl12_12)),
% 1.56/0.56    inference(backward_demodulation,[],[f110,f179])).
% 1.56/0.56  fof(f110,plain,(
% 1.56/0.56    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl12_4),
% 1.56/0.56    inference(avatar_component_clause,[],[f108])).
% 1.56/0.56  fof(f193,plain,(
% 1.56/0.56    ~spl12_1 | spl12_2 | spl12_3 | ~spl12_4 | ~spl12_7 | ~spl12_11),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f184])).
% 1.56/0.56  fof(f184,plain,(
% 1.56/0.56    $false | (~spl12_1 | spl12_2 | spl12_3 | ~spl12_4 | ~spl12_7 | ~spl12_11)),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f94,f99,f104,f159,f110,f124,f68])).
% 1.56/0.56  fof(f68,plain,(
% 1.56/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f36])).
% 1.56/0.56  fof(f36,plain,(
% 1.56/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.56/0.56    inference(flattening,[],[f35])).
% 1.56/0.56  fof(f35,plain,(
% 1.56/0.56    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.56/0.56    inference(ennf_transformation,[],[f17])).
% 1.56/0.56  fof(f17,axiom,(
% 1.56/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 1.56/0.56  fof(f124,plain,(
% 1.56/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl12_7),
% 1.56/0.56    inference(avatar_component_clause,[],[f122])).
% 1.56/0.56  fof(f122,plain,(
% 1.56/0.56    spl12_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 1.56/0.56  fof(f159,plain,(
% 1.56/0.56    r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl12_11),
% 1.56/0.56    inference(avatar_component_clause,[],[f157])).
% 1.56/0.56  fof(f157,plain,(
% 1.56/0.56    spl12_11 <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 1.56/0.56  fof(f104,plain,(
% 1.56/0.56    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl12_3),
% 1.56/0.56    inference(avatar_component_clause,[],[f102])).
% 1.56/0.56  fof(f102,plain,(
% 1.56/0.56    spl12_3 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 1.56/0.56  fof(f94,plain,(
% 1.56/0.56    v1_funct_1(sK2) | ~spl12_1),
% 1.56/0.56    inference(avatar_component_clause,[],[f92])).
% 1.56/0.56  fof(f92,plain,(
% 1.56/0.56    spl12_1 <=> v1_funct_1(sK2)),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.56/0.56  fof(f180,plain,(
% 1.56/0.56    spl12_12 | ~spl12_10),
% 1.56/0.56    inference(avatar_split_clause,[],[f163,f154,f177])).
% 1.56/0.56  fof(f163,plain,(
% 1.56/0.56    k1_xboole_0 = sK2 | ~spl12_10),
% 1.56/0.56    inference(resolution,[],[f155,f47])).
% 1.56/0.56  fof(f47,plain,(
% 1.56/0.56    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.56/0.56    inference(cnf_transformation,[],[f23])).
% 1.56/0.56  fof(f23,plain,(
% 1.56/0.56    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.56/0.56    inference(flattening,[],[f22])).
% 1.56/0.56  fof(f22,plain,(
% 1.56/0.56    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.56/0.56    inference(ennf_transformation,[],[f15])).
% 1.56/0.56  fof(f15,axiom,(
% 1.56/0.56    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).
% 1.56/0.56  fof(f160,plain,(
% 1.56/0.56    spl12_10 | spl12_11 | ~spl12_7),
% 1.56/0.56    inference(avatar_split_clause,[],[f152,f122,f157,f154])).
% 1.56/0.56  fof(f152,plain,(
% 1.56/0.56    ( ! [X0] : (r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK2)) ) | ~spl12_7),
% 1.56/0.56    inference(duplicate_literal_removal,[],[f151])).
% 1.56/0.56  fof(f151,plain,(
% 1.56/0.56    ( ! [X0] : (r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK2)) ) | ~spl12_7),
% 1.56/0.56    inference(superposition,[],[f137,f135])).
% 1.56/0.56  fof(f135,plain,(
% 1.56/0.56    ( ! [X2] : (sK0 = k1_mcart_1(X2) | ~r2_hidden(X2,sK2)) ) | ~spl12_7),
% 1.56/0.56    inference(resolution,[],[f133,f75])).
% 1.56/0.56  fof(f75,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 1.56/0.56    inference(definition_unfolding,[],[f65,f70])).
% 1.56/0.56  fof(f65,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | k1_mcart_1(X0) = X1) )),
% 1.56/0.56    inference(cnf_transformation,[],[f32])).
% 1.56/0.56  fof(f32,plain,(
% 1.56/0.56    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 1.56/0.56    inference(ennf_transformation,[],[f14])).
% 1.56/0.56  fof(f14,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 1.56/0.56  fof(f133,plain,(
% 1.56/0.56    ( ! [X2] : (r2_hidden(X2,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~r2_hidden(X2,sK2)) ) | ~spl12_7),
% 1.56/0.56    inference(resolution,[],[f124,f51])).
% 1.56/0.56  fof(f51,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f26])).
% 1.56/0.56  fof(f26,plain,(
% 1.56/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.56/0.56    inference(ennf_transformation,[],[f7])).
% 1.56/0.56  fof(f7,axiom,(
% 1.56/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.56/0.56  fof(f137,plain,(
% 1.56/0.56    ( ! [X4] : (r2_hidden(k1_mcart_1(X4),k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X4,sK2)) ) | ~spl12_7),
% 1.56/0.56    inference(resolution,[],[f133,f54])).
% 1.56/0.56  fof(f54,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f28])).
% 1.56/0.56  fof(f28,plain,(
% 1.56/0.56    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.56/0.56    inference(ennf_transformation,[],[f13])).
% 1.56/0.56  fof(f13,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.56/0.56  fof(f149,plain,(
% 1.56/0.56    spl12_8 | ~spl12_9 | ~spl12_7),
% 1.56/0.56    inference(avatar_split_clause,[],[f130,f122,f146,f142])).
% 1.56/0.56  fof(f130,plain,(
% 1.56/0.56    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | sP10(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl12_7),
% 1.56/0.56    inference(resolution,[],[f124,f87])).
% 1.56/0.56  fof(f125,plain,(
% 1.56/0.56    spl12_7),
% 1.56/0.56    inference(avatar_split_clause,[],[f71,f122])).
% 1.56/0.56  fof(f71,plain,(
% 1.56/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.56/0.56    inference(definition_unfolding,[],[f39,f70])).
% 1.56/0.56  fof(f39,plain,(
% 1.56/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.56/0.56    inference(cnf_transformation,[],[f21])).
% 1.56/0.56  fof(f21,plain,(
% 1.56/0.56    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.56/0.56    inference(flattening,[],[f20])).
% 1.56/0.56  fof(f20,plain,(
% 1.56/0.56    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.56/0.56    inference(ennf_transformation,[],[f19])).
% 1.56/0.56  fof(f19,negated_conjecture,(
% 1.56/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.56/0.56    inference(negated_conjecture,[],[f18])).
% 1.56/0.56  fof(f18,conjecture,(
% 1.56/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 1.56/0.56  fof(f111,plain,(
% 1.56/0.56    spl12_4),
% 1.56/0.56    inference(avatar_split_clause,[],[f72,f108])).
% 1.56/0.56  fof(f72,plain,(
% 1.56/0.56    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.56/0.56    inference(definition_unfolding,[],[f38,f70])).
% 1.56/0.56  fof(f38,plain,(
% 1.56/0.56    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.56/0.56    inference(cnf_transformation,[],[f21])).
% 1.56/0.56  fof(f105,plain,(
% 1.56/0.56    ~spl12_3),
% 1.56/0.56    inference(avatar_split_clause,[],[f41,f102])).
% 1.56/0.56  fof(f41,plain,(
% 1.56/0.56    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 1.56/0.56    inference(cnf_transformation,[],[f21])).
% 1.56/0.56  fof(f100,plain,(
% 1.56/0.56    ~spl12_2),
% 1.56/0.56    inference(avatar_split_clause,[],[f40,f97])).
% 1.56/0.56  fof(f40,plain,(
% 1.56/0.56    k1_xboole_0 != sK1),
% 1.56/0.56    inference(cnf_transformation,[],[f21])).
% 1.56/0.56  fof(f95,plain,(
% 1.56/0.56    spl12_1),
% 1.56/0.56    inference(avatar_split_clause,[],[f37,f92])).
% 1.56/0.56  fof(f37,plain,(
% 1.56/0.56    v1_funct_1(sK2)),
% 1.56/0.56    inference(cnf_transformation,[],[f21])).
% 1.56/0.56  % SZS output end Proof for theBenchmark
% 1.56/0.56  % (24314)------------------------------
% 1.56/0.56  % (24314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (24314)Termination reason: Refutation
% 1.56/0.56  
% 1.56/0.56  % (24314)Memory used [KB]: 10874
% 1.56/0.56  % (24314)Time elapsed: 0.100 s
% 1.56/0.56  % (24314)------------------------------
% 1.56/0.56  % (24314)------------------------------
% 1.56/0.56  % (24291)Success in time 0.199 s
%------------------------------------------------------------------------------
