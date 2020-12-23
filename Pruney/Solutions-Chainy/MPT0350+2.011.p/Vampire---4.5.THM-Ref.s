%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 213 expanded)
%              Number of leaves         :   31 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  294 ( 487 expanded)
%              Number of equality atoms :   85 ( 162 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f328,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f76,f104,f106,f118,f128,f142,f182,f225,f230,f249,f296,f327])).

fof(f327,plain,
    ( ~ spl3_2
    | ~ spl3_17
    | spl3_20
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_17
    | spl3_20
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f325,f248])).

fof(f248,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl3_20
  <=> sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f325,plain,
    ( sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_17
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f318,f295])).

fof(f295,plain,
    ( sK0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK0,sK1)))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl3_25
  <=> sK0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f318,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK0,sK1))) = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_17 ),
    inference(resolution,[],[f208,f229])).

fof(f229,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl3_17
  <=> r1_tarski(k5_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k4_subset_1(sK0,sK1,X0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,X0)) )
    | ~ spl3_2 ),
    inference(resolution,[],[f166,f64])).

fof(f64,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f166,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK1,X0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,X0)) )
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f161,f34])).

fof(f34,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f161,plain,
    ( ! [X0] :
        ( k4_subset_1(sK0,sK1,X0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,X0))
        | ~ r2_hidden(X0,k1_zfmisc_1(sK0))
        | v1_xboole_0(k1_zfmisc_1(sK0)) )
    | ~ spl3_2 ),
    inference(resolution,[],[f81,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f81,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK1,X0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,X0)) )
    | ~ spl3_2 ),
    inference(resolution,[],[f75,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f55,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f75,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f296,plain,
    ( spl3_25
    | ~ spl3_9
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f291,f222,f176,f139,f293])).

fof(f139,plain,
    ( spl3_9
  <=> sK0 = k3_tarski(k2_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f176,plain,
    ( spl3_12
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f222,plain,
    ( spl3_16
  <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f291,plain,
    ( sK0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK0,sK1)))
    | ~ spl3_9
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f290,f178])).

% (13443)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f178,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f176])).

% (13472)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f290,plain,
    ( sK0 = k3_tarski(k2_enumset1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)))
    | ~ spl3_9
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f289,f224])).

fof(f224,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f222])).

fof(f289,plain,
    ( sK0 = k3_tarski(k2_enumset1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1)))
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f288,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f37,f56,f56])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f288,plain,
    ( sK0 = k3_tarski(k2_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f141,f178])).

fof(f141,plain,
    ( sK0 = k3_tarski(k2_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f249,plain,
    ( ~ spl3_20
    | spl3_1
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f243,f222,f68,f246])).

fof(f68,plain,
    ( spl3_1
  <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f243,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))
    | spl3_1
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f70,f224])).

fof(f70,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f230,plain,
    ( spl3_17
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f217,f176,f227])).

fof(f217,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK0)
    | ~ spl3_12 ),
    inference(superposition,[],[f58,f178])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f225,plain,
    ( spl3_16
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f214,f176,f94,f222])).

fof(f94,plain,
    ( spl3_4
  <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f214,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f96,f178])).

fof(f96,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f182,plain,
    ( spl3_12
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f170,f124,f176])).

fof(f124,plain,
    ( spl3_7
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f170,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_7 ),
    inference(superposition,[],[f38,f126])).

fof(f126,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f142,plain,
    ( spl3_9
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f137,f94,f139])).

fof(f137,plain,
    ( sK0 = k3_tarski(k2_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f131,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f39,f57])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f131,plain,
    ( k3_tarski(k2_enumset1(sK0,sK0,sK0,k3_xboole_0(sK0,sK1))) = k3_tarski(k2_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))))
    | ~ spl3_4 ),
    inference(superposition,[],[f61,f96])).

fof(f61,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f57,f57])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f128,plain,
    ( spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f122,f114,f124])).

fof(f114,plain,
    ( spl3_6
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f122,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f116,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f116,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f114])).

fof(f118,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f109,f89,f114])).

fof(f89,plain,
    ( spl3_3
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f109,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f91,f65])).

fof(f65,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f91,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f106,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f105,f73,f89])).

fof(f105,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f84,f34])).

fof(f84,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f75,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f104,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f83,f73,f94])).

fof(f83,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f75,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f42])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f76,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f32,f73])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f71,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f66,f68])).

fof(f66,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f33,f35])).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f33,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n013.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:34:24 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (13444)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (13449)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (13445)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (13448)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (13458)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (13466)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (13458)Refutation not found, incomplete strategy% (13458)------------------------------
% 0.21/0.53  % (13458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13458)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13458)Memory used [KB]: 6140
% 0.21/0.53  % (13458)Time elapsed: 0.003 s
% 0.21/0.53  % (13458)------------------------------
% 0.21/0.53  % (13458)------------------------------
% 0.21/0.53  % (13451)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (13454)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (13465)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (13452)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (13468)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (13450)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (13452)Refutation not found, incomplete strategy% (13452)------------------------------
% 0.21/0.53  % (13452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13452)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13452)Memory used [KB]: 10618
% 0.21/0.53  % (13452)Time elapsed: 0.126 s
% 0.21/0.53  % (13452)------------------------------
% 0.21/0.53  % (13452)------------------------------
% 0.21/0.54  % (13447)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (13467)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (13457)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (13469)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (13471)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (13461)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (13465)Refutation not found, incomplete strategy% (13465)------------------------------
% 0.21/0.54  % (13465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13465)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13465)Memory used [KB]: 10746
% 0.21/0.54  % (13465)Time elapsed: 0.129 s
% 0.21/0.54  % (13465)------------------------------
% 0.21/0.54  % (13465)------------------------------
% 0.21/0.54  % (13446)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (13460)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (13460)Refutation not found, incomplete strategy% (13460)------------------------------
% 0.21/0.54  % (13460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13460)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13460)Memory used [KB]: 10618
% 0.21/0.54  % (13460)Time elapsed: 0.121 s
% 0.21/0.54  % (13460)------------------------------
% 0.21/0.54  % (13460)------------------------------
% 0.21/0.54  % (13463)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (13468)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f328,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f71,f76,f104,f106,f118,f128,f142,f182,f225,f230,f249,f296,f327])).
% 0.21/0.55  fof(f327,plain,(
% 0.21/0.55    ~spl3_2 | ~spl3_17 | spl3_20 | ~spl3_25),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f326])).
% 0.21/0.55  fof(f326,plain,(
% 0.21/0.55    $false | (~spl3_2 | ~spl3_17 | spl3_20 | ~spl3_25)),
% 0.21/0.55    inference(subsumption_resolution,[],[f325,f248])).
% 0.21/0.55  fof(f248,plain,(
% 0.21/0.55    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) | spl3_20),
% 0.21/0.55    inference(avatar_component_clause,[],[f246])).
% 0.21/0.55  fof(f246,plain,(
% 0.21/0.55    spl3_20 <=> sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.55  fof(f325,plain,(
% 0.21/0.55    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) | (~spl3_2 | ~spl3_17 | ~spl3_25)),
% 0.21/0.55    inference(forward_demodulation,[],[f318,f295])).
% 0.21/0.55  fof(f295,plain,(
% 0.21/0.55    sK0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK0,sK1))) | ~spl3_25),
% 0.21/0.55    inference(avatar_component_clause,[],[f293])).
% 0.21/0.55  fof(f293,plain,(
% 0.21/0.55    spl3_25 <=> sK0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK0,sK1)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.55  fof(f318,plain,(
% 0.21/0.55    k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK0,sK1))) = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) | (~spl3_2 | ~spl3_17)),
% 0.21/0.55    inference(resolution,[],[f208,f229])).
% 0.21/0.55  fof(f229,plain,(
% 0.21/0.55    r1_tarski(k5_xboole_0(sK0,sK1),sK0) | ~spl3_17),
% 0.21/0.55    inference(avatar_component_clause,[],[f227])).
% 0.21/0.55  fof(f227,plain,(
% 0.21/0.55    spl3_17 <=> r1_tarski(k5_xboole_0(sK0,sK1),sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.55  fof(f208,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,sK0) | k4_subset_1(sK0,sK1,X0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,X0))) ) | ~spl3_2),
% 0.21/0.55    inference(resolution,[],[f166,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.55    inference(rectify,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,X0))) ) | ~spl3_2),
% 0.21/0.55    inference(subsumption_resolution,[],[f161,f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,axiom,(
% 0.21/0.55    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.55  fof(f161,plain,(
% 0.21/0.55    ( ! [X0] : (k4_subset_1(sK0,sK1,X0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,X0)) | ~r2_hidden(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))) ) | ~spl3_2),
% 0.21/0.55    inference(resolution,[],[f81,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,X0))) ) | ~spl3_2),
% 0.21/0.55    inference(resolution,[],[f75,f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f55,f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f41,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f40,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(flattening,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.55    inference(ennf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f73])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.55  fof(f296,plain,(
% 0.21/0.55    spl3_25 | ~spl3_9 | ~spl3_12 | ~spl3_16),
% 0.21/0.55    inference(avatar_split_clause,[],[f291,f222,f176,f139,f293])).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    spl3_9 <=> sK0 = k3_tarski(k2_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.55  fof(f176,plain,(
% 0.21/0.55    spl3_12 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.55  fof(f222,plain,(
% 0.21/0.55    spl3_16 <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.55  fof(f291,plain,(
% 0.21/0.55    sK0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK0,sK1))) | (~spl3_9 | ~spl3_12 | ~spl3_16)),
% 0.21/0.55    inference(forward_demodulation,[],[f290,f178])).
% 0.21/0.55  % (13443)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  fof(f178,plain,(
% 0.21/0.55    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_12),
% 0.21/0.55    inference(avatar_component_clause,[],[f176])).
% 0.21/0.55  % (13472)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  fof(f290,plain,(
% 0.21/0.55    sK0 = k3_tarski(k2_enumset1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))) | (~spl3_9 | ~spl3_12 | ~spl3_16)),
% 0.21/0.55    inference(forward_demodulation,[],[f289,f224])).
% 0.21/0.55  fof(f224,plain,(
% 0.21/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | ~spl3_16),
% 0.21/0.55    inference(avatar_component_clause,[],[f222])).
% 0.21/0.55  fof(f289,plain,(
% 0.21/0.55    sK0 = k3_tarski(k2_enumset1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k3_subset_1(sK0,sK1))) | (~spl3_9 | ~spl3_12)),
% 0.21/0.55    inference(forward_demodulation,[],[f288,f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f37,f56,f56])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.55  fof(f288,plain,(
% 0.21/0.55    sK0 = k3_tarski(k2_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_xboole_0(sK0,sK1))) | (~spl3_9 | ~spl3_12)),
% 0.21/0.55    inference(forward_demodulation,[],[f141,f178])).
% 0.21/0.55  fof(f141,plain,(
% 0.21/0.55    sK0 = k3_tarski(k2_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)))) | ~spl3_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f139])).
% 0.21/0.55  fof(f249,plain,(
% 0.21/0.55    ~spl3_20 | spl3_1 | ~spl3_16),
% 0.21/0.55    inference(avatar_split_clause,[],[f243,f222,f68,f246])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    spl3_1 <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.55  fof(f243,plain,(
% 0.21/0.55    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) | (spl3_1 | ~spl3_16)),
% 0.21/0.55    inference(backward_demodulation,[],[f70,f224])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl3_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f68])).
% 0.21/0.55  fof(f230,plain,(
% 0.21/0.55    spl3_17 | ~spl3_12),
% 0.21/0.55    inference(avatar_split_clause,[],[f217,f176,f227])).
% 0.21/0.55  fof(f217,plain,(
% 0.21/0.55    r1_tarski(k5_xboole_0(sK0,sK1),sK0) | ~spl3_12),
% 0.21/0.55    inference(superposition,[],[f58,f178])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f36,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.55  fof(f225,plain,(
% 0.21/0.55    spl3_16 | ~spl3_4 | ~spl3_12),
% 0.21/0.55    inference(avatar_split_clause,[],[f214,f176,f94,f222])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    spl3_4 <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.55  fof(f214,plain,(
% 0.21/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | (~spl3_4 | ~spl3_12)),
% 0.21/0.55    inference(backward_demodulation,[],[f96,f178])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f94])).
% 0.21/0.55  fof(f182,plain,(
% 0.21/0.55    spl3_12 | ~spl3_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f170,f124,f176])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    spl3_7 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.55  fof(f170,plain,(
% 0.21/0.55    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_7),
% 0.21/0.55    inference(superposition,[],[f38,f126])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    sK1 = k3_xboole_0(sK1,sK0) | ~spl3_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f124])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.55  fof(f142,plain,(
% 0.21/0.55    spl3_9 | ~spl3_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f137,f94,f139])).
% 0.21/0.55  fof(f137,plain,(
% 0.21/0.55    sK0 = k3_tarski(k2_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)))) | ~spl3_4),
% 0.21/0.55    inference(forward_demodulation,[],[f131,f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 0.21/0.55    inference(definition_unfolding,[],[f39,f57])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    k3_tarski(k2_enumset1(sK0,sK0,sK0,k3_xboole_0(sK0,sK1))) = k3_tarski(k2_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)))) | ~spl3_4),
% 0.21/0.55    inference(superposition,[],[f61,f96])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f43,f57,f57])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 0.21/0.55  fof(f128,plain,(
% 0.21/0.55    spl3_7 | ~spl3_6),
% 0.21/0.55    inference(avatar_split_clause,[],[f122,f114,f124])).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    spl3_6 <=> r1_tarski(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    sK1 = k3_xboole_0(sK1,sK0) | ~spl3_6),
% 0.21/0.55    inference(resolution,[],[f116,f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    r1_tarski(sK1,sK0) | ~spl3_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f114])).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    spl3_6 | ~spl3_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f109,f89,f114])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    spl3_3 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    r1_tarski(sK1,sK0) | ~spl3_3),
% 0.21/0.55    inference(resolution,[],[f91,f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(equality_resolution,[],[f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f31])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f89])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    spl3_3 | ~spl3_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f105,f73,f89])).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.21/0.55    inference(subsumption_resolution,[],[f84,f34])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.21/0.55    inference(resolution,[],[f75,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    spl3_4 | ~spl3_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f83,f73,f94])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_2),
% 0.21/0.55    inference(resolution,[],[f75,f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f49,f42])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    spl3_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f32,f73])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.21/0.55    inference(negated_conjecture,[],[f17])).
% 0.21/0.55  fof(f17,conjecture,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ~spl3_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f66,f68])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.55    inference(forward_demodulation,[],[f33,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (13468)------------------------------
% 0.21/0.55  % (13468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (13468)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (13468)Memory used [KB]: 6396
% 0.21/0.55  % (13468)Time elapsed: 0.132 s
% 0.21/0.55  % (13468)------------------------------
% 0.21/0.55  % (13468)------------------------------
% 0.21/0.55  % (13443)Refutation not found, incomplete strategy% (13443)------------------------------
% 0.21/0.55  % (13443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (13443)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (13443)Memory used [KB]: 1663
% 0.21/0.55  % (13443)Time elapsed: 0.137 s
% 0.21/0.55  % (13443)------------------------------
% 0.21/0.55  % (13443)------------------------------
% 1.44/0.55  % (13442)Success in time 0.181 s
%------------------------------------------------------------------------------
