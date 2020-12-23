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
% DateTime   : Thu Dec  3 12:43:49 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 422 expanded)
%              Number of leaves         :   37 ( 159 expanded)
%              Depth                    :   12
%              Number of atoms          :  297 ( 659 expanded)
%              Number of equality atoms :   95 ( 328 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1348,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f99,f115,f140,f214,f220,f269,f272,f294,f556,f562,f596,f849,f1232,f1292,f1321,f1341])).

fof(f1341,plain,
    ( spl5_14
    | ~ spl5_2
    | ~ spl5_24
    | ~ spl5_49 ),
    inference(avatar_split_clause,[],[f1340,f1318,f593,f96,f217])).

fof(f217,plain,
    ( spl5_14
  <=> sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f96,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f593,plain,
    ( spl5_24
  <=> sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f1318,plain,
    ( spl5_49
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f1340,plain,
    ( sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_24
    | ~ spl5_49 ),
    inference(forward_demodulation,[],[f1339,f595])).

fof(f595,plain,
    ( sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f593])).

fof(f1339,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl5_2
    | ~ spl5_49 ),
    inference(forward_demodulation,[],[f1338,f71])).

fof(f71,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f37,f39,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1338,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,sK0))
    | ~ spl5_2
    | ~ spl5_49 ),
    inference(forward_demodulation,[],[f1333,f73])).

fof(f73,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f43,f69,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1333,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl5_2
    | ~ spl5_49 ),
    inference(resolution,[],[f1320,f426])).

fof(f426,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK1,X0) = k3_tarski(k1_enumset1(sK1,sK1,X0)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f76,f98])).

fof(f98,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f62,f69])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f1320,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f1318])).

fof(f1321,plain,
    ( spl5_49
    | spl5_3
    | ~ spl5_47 ),
    inference(avatar_split_clause,[],[f1316,f1289,f108,f1318])).

fof(f108,plain,
    ( spl5_3
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1289,plain,
    ( spl5_47
  <=> r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f1316,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_47 ),
    inference(resolution,[],[f1291,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f1291,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f1289])).

fof(f1292,plain,
    ( spl5_47
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f1277,f1229,f1289])).

fof(f1229,plain,
    ( spl5_44
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f1277,plain,
    ( r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_44 ),
    inference(resolution,[],[f1231,f86])).

fof(f86,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f1231,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f1229])).

fof(f1232,plain,
    ( spl5_44
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f1227,f846,f1229])).

fof(f846,plain,
    ( spl5_34
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f1227,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl5_34 ),
    inference(forward_demodulation,[],[f1215,f367])).

fof(f367,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f360,f36])).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f360,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f70,f273])).

fof(f273,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f72,f174])).

fof(f174,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[],[f75,f34])).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f49,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f38,f42,f42])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1215,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0),sK0)
    | ~ spl5_34 ),
    inference(superposition,[],[f1191,f848])).

fof(f848,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f846])).

fof(f1191,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(duplicate_literal_removal,[],[f1167])).

fof(f1167,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
      | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ) ),
    inference(resolution,[],[f188,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1)
      | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ) ),
    inference(resolution,[],[f88,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f67,f42])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f849,plain,
    ( spl5_34
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f844,f544,f846])).

fof(f544,plain,
    ( spl5_20
  <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f844,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f813,f429])).

fof(f429,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f249,f412])).

fof(f412,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f273,f367])).

fof(f249,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f70,f175])).

fof(f175,plain,(
    ! [X1] : k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(resolution,[],[f75,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f813,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl5_20 ),
    inference(superposition,[],[f275,f546])).

fof(f546,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f544])).

fof(f275,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f70,f72])).

fof(f596,plain,
    ( spl5_24
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f591,f559,f593])).

fof(f559,plain,
    ( spl5_22
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f591,plain,
    ( sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f582,f510])).

fof(f510,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(forward_demodulation,[],[f391,f367])).

fof(f391,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f371,f70])).

fof(f371,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[],[f74,f36])).

fof(f74,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f44,f69,f42])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f582,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,k1_xboole_0))
    | ~ spl5_22 ),
    inference(superposition,[],[f73,f561])).

fof(f561,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f559])).

fof(f562,plain,
    ( spl5_22
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f557,f178,f559])).

fof(f178,plain,
    ( spl5_11
  <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f557,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f536,f429])).

fof(f536,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1)
    | ~ spl5_11 ),
    inference(superposition,[],[f70,f180])).

fof(f180,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f178])).

fof(f556,plain,
    ( spl5_20
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f535,f178,f544])).

fof(f535,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_11 ),
    inference(superposition,[],[f72,f180])).

fof(f294,plain,
    ( spl5_11
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f291,f119,f178])).

fof(f119,plain,
    ( spl5_5
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f291,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl5_5 ),
    inference(resolution,[],[f121,f75])).

fof(f121,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f272,plain,
    ( spl5_5
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f116,f112,f119])).

fof(f112,plain,
    ( spl5_4
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f116,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f114,f85])).

fof(f85,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f114,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f269,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | ~ spl5_3 ),
    inference(resolution,[],[f110,f33])).

fof(f33,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f110,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f220,plain,
    ( ~ spl5_14
    | spl5_6
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f215,f211,f137,f217])).

fof(f137,plain,
    ( spl5_6
  <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f211,plain,
    ( spl5_13
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f215,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))
    | spl5_6
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f139,f213])).

fof(f213,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f211])).

fof(f139,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f137])).

fof(f214,plain,
    ( spl5_13
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f207,f96,f211])).

fof(f207,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f50,f98])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f140,plain,
    ( ~ spl5_6
    | spl5_1 ),
    inference(avatar_split_clause,[],[f135,f91,f137])).

fof(f91,plain,
    ( spl5_1
  <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f135,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl5_1 ),
    inference(forward_demodulation,[],[f93,f35])).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f93,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f115,plain,
    ( spl5_3
    | spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f106,f96,f112,f108])).

fof(f106,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f48,f98])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f99,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f31,f96])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f94,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f32,f91])).

fof(f32,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n005.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:48:17 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.22/0.51  % (5563)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (5543)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (5546)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (5547)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (5542)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (5541)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (5557)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (5563)Refutation not found, incomplete strategy% (5563)------------------------------
% 0.22/0.54  % (5563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5563)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (5563)Memory used [KB]: 10746
% 0.22/0.54  % (5563)Time elapsed: 0.113 s
% 0.22/0.54  % (5563)------------------------------
% 0.22/0.54  % (5563)------------------------------
% 0.22/0.54  % (5555)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (5561)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (5550)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (5544)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (5545)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (5552)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (5551)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (5552)Refutation not found, incomplete strategy% (5552)------------------------------
% 0.22/0.54  % (5552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5552)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (5552)Memory used [KB]: 10618
% 0.22/0.54  % (5552)Time elapsed: 0.124 s
% 0.22/0.54  % (5552)------------------------------
% 0.22/0.54  % (5552)------------------------------
% 0.22/0.54  % (5568)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (5551)Refutation not found, incomplete strategy% (5551)------------------------------
% 0.22/0.55  % (5551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5551)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (5551)Memory used [KB]: 10618
% 0.22/0.55  % (5551)Time elapsed: 0.123 s
% 0.22/0.55  % (5551)------------------------------
% 0.22/0.55  % (5551)------------------------------
% 0.22/0.55  % (5549)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (5569)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (5567)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (5560)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (5562)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (5554)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (5553)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (5570)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.53/0.56  % (5558)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.53/0.56  % (5566)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.53/0.56  % (5565)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.53/0.56  % (5559)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.53/0.56  % (5558)Refutation not found, incomplete strategy% (5558)------------------------------
% 1.53/0.56  % (5558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (5558)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (5558)Memory used [KB]: 10618
% 1.53/0.57  % (5558)Time elapsed: 0.148 s
% 1.53/0.57  % (5558)------------------------------
% 1.53/0.57  % (5558)------------------------------
% 1.53/0.57  % (5556)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.67/0.58  % (5548)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.67/0.58  % (5564)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.67/0.62  % (5557)Refutation found. Thanks to Tanya!
% 1.67/0.62  % SZS status Theorem for theBenchmark
% 1.67/0.62  % SZS output start Proof for theBenchmark
% 1.67/0.62  fof(f1348,plain,(
% 1.67/0.62    $false),
% 1.67/0.62    inference(avatar_sat_refutation,[],[f94,f99,f115,f140,f214,f220,f269,f272,f294,f556,f562,f596,f849,f1232,f1292,f1321,f1341])).
% 1.67/0.62  fof(f1341,plain,(
% 1.67/0.62    spl5_14 | ~spl5_2 | ~spl5_24 | ~spl5_49),
% 1.67/0.62    inference(avatar_split_clause,[],[f1340,f1318,f593,f96,f217])).
% 1.67/0.62  fof(f217,plain,(
% 1.67/0.62    spl5_14 <=> sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.67/0.62  fof(f96,plain,(
% 1.67/0.62    spl5_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.67/0.62  fof(f593,plain,(
% 1.67/0.62    spl5_24 <=> sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.67/0.62  fof(f1318,plain,(
% 1.67/0.62    spl5_49 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 1.67/0.62  fof(f1340,plain,(
% 1.67/0.62    sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) | (~spl5_2 | ~spl5_24 | ~spl5_49)),
% 1.67/0.62    inference(forward_demodulation,[],[f1339,f595])).
% 1.67/0.62  fof(f595,plain,(
% 1.67/0.62    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl5_24),
% 1.67/0.62    inference(avatar_component_clause,[],[f593])).
% 1.67/0.62  fof(f1339,plain,(
% 1.67/0.62    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | (~spl5_2 | ~spl5_49)),
% 1.67/0.62    inference(forward_demodulation,[],[f1338,f71])).
% 1.67/0.62  fof(f71,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.67/0.62    inference(definition_unfolding,[],[f37,f39,f39])).
% 1.67/0.62  fof(f39,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f14])).
% 1.67/0.62  fof(f14,axiom,(
% 1.67/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.67/0.62  fof(f37,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f13])).
% 1.67/0.62  fof(f13,axiom,(
% 1.67/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.67/0.62  fof(f1338,plain,(
% 1.67/0.62    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,sK0)) | (~spl5_2 | ~spl5_49)),
% 1.67/0.62    inference(forward_demodulation,[],[f1333,f73])).
% 1.67/0.62  fof(f73,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0)))) )),
% 1.67/0.62    inference(definition_unfolding,[],[f43,f69,f69])).
% 1.67/0.62  fof(f69,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.67/0.62    inference(definition_unfolding,[],[f40,f39])).
% 1.67/0.62  fof(f40,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.67/0.62    inference(cnf_transformation,[],[f16])).
% 1.67/0.62  fof(f16,axiom,(
% 1.67/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.67/0.62  fof(f43,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f8])).
% 1.67/0.62  fof(f8,axiom,(
% 1.67/0.62    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.67/0.62  fof(f1333,plain,(
% 1.67/0.62    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK0,sK1))) | (~spl5_2 | ~spl5_49)),
% 1.67/0.62    inference(resolution,[],[f1320,f426])).
% 1.67/0.62  fof(f426,plain,(
% 1.67/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X0) = k3_tarski(k1_enumset1(sK1,sK1,X0))) ) | ~spl5_2),
% 1.67/0.62    inference(resolution,[],[f76,f98])).
% 1.67/0.62  fof(f98,plain,(
% 1.67/0.62    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_2),
% 1.67/0.62    inference(avatar_component_clause,[],[f96])).
% 1.67/0.62  fof(f76,plain,(
% 1.67/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))) )),
% 1.67/0.62    inference(definition_unfolding,[],[f62,f69])).
% 1.67/0.62  fof(f62,plain,(
% 1.67/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f30])).
% 1.67/0.62  fof(f30,plain,(
% 1.67/0.62    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.67/0.62    inference(flattening,[],[f29])).
% 1.67/0.62  fof(f29,plain,(
% 1.67/0.62    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.67/0.62    inference(ennf_transformation,[],[f21])).
% 1.67/0.62  fof(f21,axiom,(
% 1.67/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.67/0.62  fof(f1320,plain,(
% 1.67/0.62    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl5_49),
% 1.67/0.62    inference(avatar_component_clause,[],[f1318])).
% 1.67/0.62  fof(f1321,plain,(
% 1.67/0.62    spl5_49 | spl5_3 | ~spl5_47),
% 1.67/0.62    inference(avatar_split_clause,[],[f1316,f1289,f108,f1318])).
% 1.67/0.62  fof(f108,plain,(
% 1.67/0.62    spl5_3 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.67/0.62  fof(f1289,plain,(
% 1.67/0.62    spl5_47 <=> r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 1.67/0.62  fof(f1316,plain,(
% 1.67/0.62    v1_xboole_0(k1_zfmisc_1(sK0)) | m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl5_47),
% 1.67/0.62    inference(resolution,[],[f1291,f47])).
% 1.67/0.62  fof(f47,plain,(
% 1.67/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f25])).
% 1.67/0.62  fof(f25,plain,(
% 1.67/0.62    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.67/0.62    inference(ennf_transformation,[],[f17])).
% 1.67/0.62  fof(f17,axiom,(
% 1.67/0.62    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.67/0.62  fof(f1291,plain,(
% 1.67/0.62    r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl5_47),
% 1.67/0.62    inference(avatar_component_clause,[],[f1289])).
% 1.67/0.62  fof(f1292,plain,(
% 1.67/0.62    spl5_47 | ~spl5_44),
% 1.67/0.62    inference(avatar_split_clause,[],[f1277,f1229,f1289])).
% 1.67/0.62  fof(f1229,plain,(
% 1.67/0.62    spl5_44 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK0)),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 1.67/0.62  fof(f1277,plain,(
% 1.67/0.62    r2_hidden(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl5_44),
% 1.67/0.62    inference(resolution,[],[f1231,f86])).
% 1.67/0.62  fof(f86,plain,(
% 1.67/0.62    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 1.67/0.62    inference(equality_resolution,[],[f57])).
% 1.67/0.62  fof(f57,plain,(
% 1.67/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.67/0.62    inference(cnf_transformation,[],[f15])).
% 1.67/0.62  fof(f15,axiom,(
% 1.67/0.62    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.67/0.62  fof(f1231,plain,(
% 1.67/0.62    r1_tarski(k4_xboole_0(sK0,sK1),sK0) | ~spl5_44),
% 1.67/0.62    inference(avatar_component_clause,[],[f1229])).
% 1.67/0.62  fof(f1232,plain,(
% 1.67/0.62    spl5_44 | ~spl5_34),
% 1.67/0.62    inference(avatar_split_clause,[],[f1227,f846,f1229])).
% 1.67/0.62  fof(f846,plain,(
% 1.67/0.62    spl5_34 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 1.67/0.62  fof(f1227,plain,(
% 1.67/0.62    r1_tarski(k4_xboole_0(sK0,sK1),sK0) | ~spl5_34),
% 1.67/0.62    inference(forward_demodulation,[],[f1215,f367])).
% 1.67/0.62  fof(f367,plain,(
% 1.67/0.62    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.67/0.62    inference(forward_demodulation,[],[f360,f36])).
% 1.67/0.62  fof(f36,plain,(
% 1.67/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.67/0.62    inference(cnf_transformation,[],[f10])).
% 1.67/0.62  fof(f10,axiom,(
% 1.67/0.62    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.67/0.62  fof(f360,plain,(
% 1.67/0.62    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)) )),
% 1.67/0.62    inference(superposition,[],[f70,f273])).
% 1.67/0.62  fof(f273,plain,(
% 1.67/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.67/0.62    inference(superposition,[],[f72,f174])).
% 1.67/0.62  fof(f174,plain,(
% 1.67/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.67/0.62    inference(resolution,[],[f75,f34])).
% 1.67/0.62  fof(f34,plain,(
% 1.67/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f7])).
% 1.67/0.62  fof(f7,axiom,(
% 1.67/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.67/0.62  fof(f75,plain,(
% 1.67/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.67/0.62    inference(definition_unfolding,[],[f49,f42])).
% 1.67/0.62  fof(f42,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.67/0.62    inference(cnf_transformation,[],[f9])).
% 1.67/0.62  fof(f9,axiom,(
% 1.67/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.67/0.62  fof(f49,plain,(
% 1.67/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.67/0.62    inference(cnf_transformation,[],[f26])).
% 1.67/0.62  fof(f26,plain,(
% 1.67/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.67/0.62    inference(ennf_transformation,[],[f6])).
% 1.67/0.62  fof(f6,axiom,(
% 1.67/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.67/0.62  fof(f72,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.67/0.62    inference(definition_unfolding,[],[f38,f42,f42])).
% 1.67/0.62  fof(f38,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f1])).
% 1.67/0.62  fof(f1,axiom,(
% 1.67/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.67/0.62  fof(f70,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.67/0.62    inference(definition_unfolding,[],[f41,f42])).
% 1.67/0.62  fof(f41,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.67/0.62    inference(cnf_transformation,[],[f5])).
% 1.67/0.62  fof(f5,axiom,(
% 1.67/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.67/0.62  fof(f1215,plain,(
% 1.67/0.62    r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0),sK0) | ~spl5_34),
% 1.67/0.62    inference(superposition,[],[f1191,f848])).
% 1.67/0.62  fof(f848,plain,(
% 1.67/0.62    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) | ~spl5_34),
% 1.67/0.62    inference(avatar_component_clause,[],[f846])).
% 1.67/0.62  fof(f1191,plain,(
% 1.67/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) )),
% 1.67/0.62    inference(duplicate_literal_removal,[],[f1167])).
% 1.67/0.62  fof(f1167,plain,(
% 1.67/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)) )),
% 1.67/0.62    inference(resolution,[],[f188,f56])).
% 1.67/0.62  fof(f56,plain,(
% 1.67/0.62    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f28])).
% 1.67/0.62  fof(f28,plain,(
% 1.67/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.67/0.62    inference(ennf_transformation,[],[f2])).
% 1.67/0.62  fof(f2,axiom,(
% 1.67/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.67/0.62  fof(f188,plain,(
% 1.67/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK2(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.67/0.62    inference(resolution,[],[f88,f55])).
% 1.67/0.62  fof(f55,plain,(
% 1.67/0.62    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f28])).
% 1.67/0.62  fof(f88,plain,(
% 1.67/0.62    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X3,X1)) )),
% 1.67/0.62    inference(equality_resolution,[],[f78])).
% 1.67/0.62  fof(f78,plain,(
% 1.67/0.62    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 1.67/0.62    inference(definition_unfolding,[],[f67,f42])).
% 1.67/0.62  fof(f67,plain,(
% 1.67/0.62    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.67/0.62    inference(cnf_transformation,[],[f3])).
% 1.67/0.62  fof(f3,axiom,(
% 1.67/0.62    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.67/0.62  fof(f849,plain,(
% 1.67/0.62    spl5_34 | ~spl5_20),
% 1.67/0.62    inference(avatar_split_clause,[],[f844,f544,f846])).
% 1.67/0.62  fof(f544,plain,(
% 1.67/0.62    spl5_20 <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.67/0.62  fof(f844,plain,(
% 1.67/0.62    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) | ~spl5_20),
% 1.67/0.62    inference(forward_demodulation,[],[f813,f429])).
% 1.67/0.62  fof(f429,plain,(
% 1.67/0.62    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 1.67/0.62    inference(backward_demodulation,[],[f249,f412])).
% 1.67/0.62  fof(f412,plain,(
% 1.67/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.67/0.62    inference(backward_demodulation,[],[f273,f367])).
% 1.67/0.62  fof(f249,plain,(
% 1.67/0.62    ( ! [X1] : (k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)) )),
% 1.67/0.62    inference(superposition,[],[f70,f175])).
% 1.67/0.62  fof(f175,plain,(
% 1.67/0.62    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1) )),
% 1.67/0.62    inference(resolution,[],[f75,f83])).
% 1.67/0.62  fof(f83,plain,(
% 1.67/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.67/0.62    inference(equality_resolution,[],[f52])).
% 1.67/0.62  fof(f52,plain,(
% 1.67/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.67/0.62    inference(cnf_transformation,[],[f4])).
% 1.67/0.62  fof(f4,axiom,(
% 1.67/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.67/0.62  fof(f813,plain,(
% 1.67/0.62    k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | ~spl5_20),
% 1.67/0.62    inference(superposition,[],[f275,f546])).
% 1.67/0.62  fof(f546,plain,(
% 1.67/0.62    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_20),
% 1.67/0.62    inference(avatar_component_clause,[],[f544])).
% 1.67/0.62  fof(f275,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.67/0.62    inference(superposition,[],[f70,f72])).
% 1.67/0.62  fof(f596,plain,(
% 1.67/0.62    spl5_24 | ~spl5_22),
% 1.67/0.62    inference(avatar_split_clause,[],[f591,f559,f593])).
% 1.67/0.62  fof(f559,plain,(
% 1.67/0.62    spl5_22 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.67/0.62  fof(f591,plain,(
% 1.67/0.62    sK0 = k3_tarski(k1_enumset1(sK0,sK0,sK1)) | ~spl5_22),
% 1.67/0.62    inference(forward_demodulation,[],[f582,f510])).
% 1.67/0.62  fof(f510,plain,(
% 1.67/0.62    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 1.67/0.62    inference(forward_demodulation,[],[f391,f367])).
% 1.67/0.62  fof(f391,plain,(
% 1.67/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_tarski(k1_enumset1(X0,X0,k1_xboole_0))) )),
% 1.67/0.62    inference(forward_demodulation,[],[f371,f70])).
% 1.67/0.62  fof(f371,plain,(
% 1.67/0.62    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)))) )),
% 1.67/0.62    inference(superposition,[],[f74,f36])).
% 1.67/0.62  fof(f74,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.67/0.62    inference(definition_unfolding,[],[f44,f69,f42])).
% 1.67/0.62  fof(f44,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.67/0.62    inference(cnf_transformation,[],[f12])).
% 1.67/0.62  fof(f12,axiom,(
% 1.67/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.67/0.62  fof(f582,plain,(
% 1.67/0.62    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,k1_xboole_0)) | ~spl5_22),
% 1.67/0.62    inference(superposition,[],[f73,f561])).
% 1.67/0.62  fof(f561,plain,(
% 1.67/0.62    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl5_22),
% 1.67/0.62    inference(avatar_component_clause,[],[f559])).
% 1.67/0.62  fof(f562,plain,(
% 1.67/0.62    spl5_22 | ~spl5_11),
% 1.67/0.62    inference(avatar_split_clause,[],[f557,f178,f559])).
% 1.67/0.62  fof(f178,plain,(
% 1.67/0.62    spl5_11 <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.67/0.62  fof(f557,plain,(
% 1.67/0.62    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl5_11),
% 1.67/0.62    inference(forward_demodulation,[],[f536,f429])).
% 1.67/0.62  fof(f536,plain,(
% 1.67/0.62    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1) | ~spl5_11),
% 1.67/0.62    inference(superposition,[],[f70,f180])).
% 1.67/0.62  fof(f180,plain,(
% 1.67/0.62    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | ~spl5_11),
% 1.67/0.62    inference(avatar_component_clause,[],[f178])).
% 1.67/0.62  fof(f556,plain,(
% 1.67/0.62    spl5_20 | ~spl5_11),
% 1.67/0.62    inference(avatar_split_clause,[],[f535,f178,f544])).
% 1.67/0.62  fof(f535,plain,(
% 1.67/0.62    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_11),
% 1.67/0.62    inference(superposition,[],[f72,f180])).
% 1.67/0.62  fof(f294,plain,(
% 1.67/0.62    spl5_11 | ~spl5_5),
% 1.67/0.62    inference(avatar_split_clause,[],[f291,f119,f178])).
% 1.67/0.62  fof(f119,plain,(
% 1.67/0.62    spl5_5 <=> r1_tarski(sK1,sK0)),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.67/0.62  fof(f291,plain,(
% 1.67/0.62    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | ~spl5_5),
% 1.67/0.62    inference(resolution,[],[f121,f75])).
% 1.67/0.62  fof(f121,plain,(
% 1.67/0.62    r1_tarski(sK1,sK0) | ~spl5_5),
% 1.67/0.62    inference(avatar_component_clause,[],[f119])).
% 1.67/0.62  fof(f272,plain,(
% 1.67/0.62    spl5_5 | ~spl5_4),
% 1.67/0.62    inference(avatar_split_clause,[],[f116,f112,f119])).
% 1.67/0.62  fof(f112,plain,(
% 1.67/0.62    spl5_4 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.67/0.62  fof(f116,plain,(
% 1.67/0.62    r1_tarski(sK1,sK0) | ~spl5_4),
% 1.67/0.62    inference(resolution,[],[f114,f85])).
% 1.67/0.62  fof(f85,plain,(
% 1.67/0.62    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.67/0.62    inference(equality_resolution,[],[f58])).
% 1.67/0.62  fof(f58,plain,(
% 1.67/0.62    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.67/0.62    inference(cnf_transformation,[],[f15])).
% 1.67/0.62  fof(f114,plain,(
% 1.67/0.62    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl5_4),
% 1.67/0.62    inference(avatar_component_clause,[],[f112])).
% 1.67/0.62  fof(f269,plain,(
% 1.67/0.62    ~spl5_3),
% 1.67/0.62    inference(avatar_contradiction_clause,[],[f267])).
% 1.67/0.62  fof(f267,plain,(
% 1.67/0.62    $false | ~spl5_3),
% 1.67/0.62    inference(resolution,[],[f110,f33])).
% 1.67/0.62  fof(f33,plain,(
% 1.67/0.62    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.67/0.62    inference(cnf_transformation,[],[f20])).
% 1.67/0.62  fof(f20,axiom,(
% 1.67/0.62    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.67/0.62  fof(f110,plain,(
% 1.67/0.62    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_3),
% 1.67/0.62    inference(avatar_component_clause,[],[f108])).
% 1.67/0.62  fof(f220,plain,(
% 1.67/0.62    ~spl5_14 | spl5_6 | ~spl5_13),
% 1.67/0.62    inference(avatar_split_clause,[],[f215,f211,f137,f217])).
% 1.67/0.62  fof(f137,plain,(
% 1.67/0.62    spl5_6 <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.67/0.62  fof(f211,plain,(
% 1.67/0.62    spl5_13 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.67/0.62  fof(f215,plain,(
% 1.67/0.62    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) | (spl5_6 | ~spl5_13)),
% 1.67/0.62    inference(backward_demodulation,[],[f139,f213])).
% 1.67/0.62  fof(f213,plain,(
% 1.67/0.62    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl5_13),
% 1.67/0.62    inference(avatar_component_clause,[],[f211])).
% 1.67/0.62  fof(f139,plain,(
% 1.67/0.62    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl5_6),
% 1.67/0.62    inference(avatar_component_clause,[],[f137])).
% 1.67/0.62  fof(f214,plain,(
% 1.67/0.62    spl5_13 | ~spl5_2),
% 1.67/0.62    inference(avatar_split_clause,[],[f207,f96,f211])).
% 1.67/0.62  fof(f207,plain,(
% 1.67/0.62    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl5_2),
% 1.67/0.62    inference(resolution,[],[f50,f98])).
% 1.67/0.62  fof(f50,plain,(
% 1.67/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f27])).
% 1.67/0.62  fof(f27,plain,(
% 1.67/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.67/0.62    inference(ennf_transformation,[],[f19])).
% 1.67/0.62  fof(f19,axiom,(
% 1.67/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.67/0.62  fof(f140,plain,(
% 1.67/0.62    ~spl5_6 | spl5_1),
% 1.67/0.62    inference(avatar_split_clause,[],[f135,f91,f137])).
% 1.67/0.62  fof(f91,plain,(
% 1.67/0.62    spl5_1 <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.67/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.67/0.62  fof(f135,plain,(
% 1.67/0.62    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl5_1),
% 1.67/0.62    inference(forward_demodulation,[],[f93,f35])).
% 1.67/0.62  fof(f35,plain,(
% 1.67/0.62    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.67/0.62    inference(cnf_transformation,[],[f18])).
% 1.67/0.62  fof(f18,axiom,(
% 1.67/0.62    ! [X0] : k2_subset_1(X0) = X0),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.67/0.62  fof(f93,plain,(
% 1.67/0.62    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl5_1),
% 1.67/0.62    inference(avatar_component_clause,[],[f91])).
% 1.67/0.62  fof(f115,plain,(
% 1.67/0.62    spl5_3 | spl5_4 | ~spl5_2),
% 1.67/0.62    inference(avatar_split_clause,[],[f106,f96,f112,f108])).
% 1.67/0.62  fof(f106,plain,(
% 1.67/0.62    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_2),
% 1.67/0.62    inference(resolution,[],[f48,f98])).
% 1.67/0.62  fof(f48,plain,(
% 1.67/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.67/0.62    inference(cnf_transformation,[],[f25])).
% 1.67/0.62  fof(f99,plain,(
% 1.67/0.62    spl5_2),
% 1.67/0.62    inference(avatar_split_clause,[],[f31,f96])).
% 1.67/0.62  fof(f31,plain,(
% 1.67/0.62    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.67/0.62    inference(cnf_transformation,[],[f24])).
% 1.67/0.62  fof(f24,plain,(
% 1.67/0.62    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.67/0.62    inference(ennf_transformation,[],[f23])).
% 1.67/0.62  fof(f23,negated_conjecture,(
% 1.67/0.62    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.67/0.62    inference(negated_conjecture,[],[f22])).
% 1.67/0.62  fof(f22,conjecture,(
% 1.67/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.67/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 1.67/0.62  fof(f94,plain,(
% 1.67/0.62    ~spl5_1),
% 1.67/0.62    inference(avatar_split_clause,[],[f32,f91])).
% 1.67/0.62  fof(f32,plain,(
% 1.67/0.62    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.67/0.62    inference(cnf_transformation,[],[f24])).
% 1.67/0.62  % SZS output end Proof for theBenchmark
% 1.67/0.62  % (5557)------------------------------
% 1.67/0.62  % (5557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.62  % (5557)Termination reason: Refutation
% 1.67/0.62  
% 1.67/0.62  % (5557)Memory used [KB]: 11641
% 1.67/0.62  % (5557)Time elapsed: 0.203 s
% 1.67/0.62  % (5557)------------------------------
% 1.67/0.62  % (5557)------------------------------
% 2.03/0.64  % (5540)Success in time 0.27 s
%------------------------------------------------------------------------------
