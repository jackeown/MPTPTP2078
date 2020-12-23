%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 196 expanded)
%              Number of leaves         :   29 (  74 expanded)
%              Depth                    :    9
%              Number of atoms          :  312 ( 508 expanded)
%              Number of equality atoms :   63 ( 117 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f277,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f99,f105,f119,f143,f154,f174,f187,f238,f261,f263,f270,f276])).

fof(f276,plain,
    ( ~ spl9_10
    | ~ spl9_12
    | ~ spl9_22 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_22 ),
    inference(unit_resulting_resolution,[],[f47,f73,f271,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f271,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_22 ),
    inference(resolution,[],[f269,f206])).

fof(f206,plain,
    ( ! [X2,X1] :
        ( ~ sP7(k1_xboole_0,X2)
        | ~ r2_hidden(X1,X2) )
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(resolution,[],[f199,f82])).

fof(f82,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | ~ sP7(X2,X1) ) ),
    inference(general_splitting,[],[f64,f81_D])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) != X1
      | sP7(X2,X1) ) ),
    inference(cnf_transformation,[],[f81_D])).

fof(f81_D,plain,(
    ! [X1,X2] :
      ( ! [X0] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | k1_relset_1(X1,X0,X2) != X1 )
    <=> ~ sP7(X2,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) != X1
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f199,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(backward_demodulation,[],[f149,f173])).

fof(f173,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl9_12
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f149,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl9_10
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f269,plain,
    ( sP7(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl9_22
  <=> sP7(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f73,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f69])).

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

fof(f48,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f270,plain,
    ( spl9_22
    | ~ spl9_8
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f265,f171,f136,f267])).

fof(f136,plain,
    ( spl9_8
  <=> sP7(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f265,plain,
    ( sP7(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl9_8
    | ~ spl9_12 ),
    inference(forward_demodulation,[],[f138,f173])).

fof(f138,plain,
    ( sP7(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f136])).

fof(f263,plain,
    ( spl9_2
    | ~ spl9_18
    | spl9_21 ),
    inference(avatar_contradiction_clause,[],[f262])).

% (18569)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f262,plain,
    ( $false
    | spl9_2
    | ~ spl9_18
    | spl9_21 ),
    inference(unit_resulting_resolution,[],[f93,f237,f42,f260,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f260,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | spl9_21 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl9_21
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f237,plain,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl9_18
  <=> v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f93,plain,
    ( k1_xboole_0 != sK1
    | spl9_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl9_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f261,plain,
    ( ~ spl9_21
    | spl9_9
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f246,f171,f140,f258])).

fof(f140,plain,
    ( spl9_9
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f246,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)
    | spl9_9
    | ~ spl9_12 ),
    inference(forward_demodulation,[],[f142,f173])).

fof(f142,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | spl9_9 ),
    inference(avatar_component_clause,[],[f140])).

fof(f238,plain,
    ( spl9_18
    | ~ spl9_4
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f193,f171,f102,f235])).

fof(f102,plain,
    ( spl9_4
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f193,plain,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl9_4
    | ~ spl9_12 ),
    inference(backward_demodulation,[],[f104,f173])).

fof(f104,plain,
    ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f187,plain,
    ( ~ spl9_1
    | spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_11 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl9_1
    | spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f88,f93,f98,f153,f104,f118,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f118,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl9_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f153,plain,
    ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl9_11
  <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f98,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl9_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f88,plain,
    ( v1_funct_1(sK2)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl9_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f174,plain,
    ( spl9_12
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f157,f148,f171])).

fof(f157,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_10 ),
    inference(resolution,[],[f149,f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f154,plain,
    ( spl9_10
    | spl9_11
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f146,f116,f151,f148])).

fof(f146,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl9_7 ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl9_7 ),
    inference(superposition,[],[f130,f128])).

fof(f128,plain,
    ( ! [X0] :
        ( k1_mcart_1(X0) = sK0
        | ~ r2_hidden(X0,sK2) )
    | ~ spl9_7 ),
    inference(resolution,[],[f127,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f65,f70])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f69])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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

fof(f127,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl9_7 ),
    inference(resolution,[],[f118,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f130,plain,
    ( ! [X2] :
        ( r2_hidden(k1_mcart_1(X2),k2_enumset1(sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl9_7 ),
    inference(resolution,[],[f127,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f143,plain,
    ( spl9_8
    | ~ spl9_9
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f124,f116,f140,f136])).

fof(f124,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | sP7(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl9_7 ),
    inference(resolution,[],[f118,f81])).

fof(f119,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f71,f116])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f38,f70])).

fof(f38,plain,(
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

fof(f105,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f72,f102])).

fof(f72,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f37,f70])).

fof(f37,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f99,plain,(
    ~ spl9_3 ),
    inference(avatar_split_clause,[],[f40,f96])).

fof(f40,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f94,plain,(
    ~ spl9_2 ),
    inference(avatar_split_clause,[],[f39,f91])).

fof(f39,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f89,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f36,f86])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:54:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (18578)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (18570)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (18561)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (18562)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (18566)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (18577)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (18578)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f277,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f89,f94,f99,f105,f119,f143,f154,f174,f187,f238,f261,f263,f270,f276])).
% 0.21/0.53  fof(f276,plain,(
% 0.21/0.53    ~spl9_10 | ~spl9_12 | ~spl9_22),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f272])).
% 0.21/0.53  fof(f272,plain,(
% 0.21/0.53    $false | (~spl9_10 | ~spl9_12 | ~spl9_22)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f47,f73,f271,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.53  fof(f271,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) ) | (~spl9_10 | ~spl9_12 | ~spl9_22)),
% 0.21/0.53    inference(resolution,[],[f269,f206])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~sP7(k1_xboole_0,X2) | ~r2_hidden(X1,X2)) ) | (~spl9_10 | ~spl9_12)),
% 0.21/0.53    inference(resolution,[],[f199,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X2,X3,X1] : (r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2) | ~r2_hidden(X3,X1) | ~sP7(X2,X1)) )),
% 0.21/0.53    inference(general_splitting,[],[f64,f81_D])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1 | sP7(X2,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f81_D])).
% 0.21/0.53  fof(f81_D,plain,(
% 0.21/0.53    ( ! [X1,X2] : (( ! [X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1) ) <=> ~sP7(X2,X1)) )),
% 0.21/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1 | ~r2_hidden(X3,X1) | r2_hidden(k4_tarski(X3,sK6(X2,X3)),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl9_10 | ~spl9_12)),
% 0.21/0.53    inference(backward_demodulation,[],[f149,f173])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    k1_xboole_0 = sK2 | ~spl9_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f171])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    spl9_12 <=> k1_xboole_0 = sK2),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl9_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f148])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    spl9_10 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.21/0.53  fof(f269,plain,(
% 0.21/0.53    sP7(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl9_22),
% 0.21/0.53    inference(avatar_component_clause,[],[f267])).
% 0.21/0.53  fof(f267,plain,(
% 0.21/0.53    spl9_22 <=> sP7(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f48,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f49,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    spl9_22 | ~spl9_8 | ~spl9_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f265,f171,f136,f267])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    spl9_8 <=> sP7(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    sP7(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl9_8 | ~spl9_12)),
% 0.21/0.53    inference(forward_demodulation,[],[f138,f173])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    sP7(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl9_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f136])).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    spl9_2 | ~spl9_18 | spl9_21),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f262])).
% 0.21/0.53  % (18569)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  fof(f262,plain,(
% 0.21/0.53    $false | (spl9_2 | ~spl9_18 | spl9_21)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f93,f237,f42,f260,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(flattening,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.53  fof(f260,plain,(
% 0.21/0.53    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | spl9_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f258])).
% 0.21/0.53  fof(f258,plain,(
% 0.21/0.53    spl9_21 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl9_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f235])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    spl9_18 <=> v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | spl9_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f91])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    spl9_2 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.53  fof(f261,plain,(
% 0.21/0.53    ~spl9_21 | spl9_9 | ~spl9_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f246,f171,f140,f258])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    spl9_9 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.21/0.53  fof(f246,plain,(
% 0.21/0.53    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,k1_xboole_0) | (spl9_9 | ~spl9_12)),
% 0.21/0.53    inference(forward_demodulation,[],[f142,f173])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | spl9_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f140])).
% 0.21/0.53  fof(f238,plain,(
% 0.21/0.53    spl9_18 | ~spl9_4 | ~spl9_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f193,f171,f102,f235])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    spl9_4 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    v1_funct_2(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | (~spl9_4 | ~spl9_12)),
% 0.21/0.53    inference(backward_demodulation,[],[f104,f173])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl9_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f102])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    ~spl9_1 | spl9_2 | spl9_3 | ~spl9_4 | ~spl9_7 | ~spl9_11),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f178])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    $false | (~spl9_1 | spl9_2 | spl9_3 | ~spl9_4 | ~spl9_7 | ~spl9_11)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f88,f93,f98,f153,f104,f118,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.54    inference(flattening,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl9_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f116])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    spl9_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl9_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f151])).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    spl9_11 <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl9_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f96])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    spl9_3 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    v1_funct_1(sK2) | ~spl9_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    spl9_1 <=> v1_funct_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    spl9_12 | ~spl9_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f157,f148,f171])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | ~spl9_10),
% 0.21/0.54    inference(resolution,[],[f149,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    spl9_10 | spl9_11 | ~spl9_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f146,f116,f151,f148])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK2)) ) | ~spl9_7),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f145])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK2)) ) | ~spl9_7),
% 0.21/0.54    inference(superposition,[],[f130,f128])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    ( ! [X0] : (k1_mcart_1(X0) = sK0 | ~r2_hidden(X0,sK2)) ) | ~spl9_7),
% 0.21/0.54    inference(resolution,[],[f127,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.21/0.54    inference(definition_unfolding,[],[f65,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f43,f69])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    ( ! [X2] : (r2_hidden(X2,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~r2_hidden(X2,sK2)) ) | ~spl9_7),
% 0.21/0.54    inference(resolution,[],[f118,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    ( ! [X2] : (r2_hidden(k1_mcart_1(X2),k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X2,sK2)) ) | ~spl9_7),
% 0.21/0.54    inference(resolution,[],[f127,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    spl9_8 | ~spl9_9 | ~spl9_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f124,f116,f140,f136])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | sP7(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl9_7),
% 0.21/0.54    inference(resolution,[],[f118,f81])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    spl9_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f71,f116])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.21/0.54    inference(definition_unfolding,[],[f38,f70])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.54    inference(negated_conjecture,[],[f18])).
% 0.21/0.54  fof(f18,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    spl9_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f72,f102])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.54    inference(definition_unfolding,[],[f37,f70])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    ~spl9_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f40,f96])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ~spl9_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f39,f91])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    k1_xboole_0 != sK1),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    spl9_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f36,f86])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    v1_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (18578)------------------------------
% 0.21/0.54  % (18578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18578)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (18578)Memory used [KB]: 10874
% 0.21/0.54  % (18578)Time elapsed: 0.070 s
% 0.21/0.54  % (18578)------------------------------
% 0.21/0.54  % (18578)------------------------------
% 0.21/0.54  % (18554)Success in time 0.173 s
%------------------------------------------------------------------------------
