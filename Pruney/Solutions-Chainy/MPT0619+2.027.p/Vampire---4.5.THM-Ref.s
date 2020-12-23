%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 225 expanded)
%              Number of leaves         :   28 (  87 expanded)
%              Depth                    :   12
%              Number of atoms          :  428 ( 658 expanded)
%              Number of equality atoms :  236 ( 374 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f110,f114,f118,f128,f138,f143,f151,f158,f186,f198,f213,f219])).

fof(f219,plain,
    ( spl4_1
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f217,f211,f104])).

fof(f104,plain,
    ( spl4_1
  <=> k2_relat_1(sK1) = k4_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f211,plain,
    ( spl4_19
  <=> ! [X1] :
        ( k1_funct_1(sK1,sK0) != X1
        | k2_relat_1(sK1) = k4_enumset1(X1,X1,X1,X1,X1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f217,plain,
    ( k2_relat_1(sK1) = k4_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
    | ~ spl4_19 ),
    inference(equality_resolution,[],[f212])).

fof(f212,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,sK0) != X1
        | k2_relat_1(sK1) = k4_enumset1(X1,X1,X1,X1,X1,X1) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f211])).

fof(f213,plain,
    ( spl4_15
    | spl4_19
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f201,f195,f211,f184])).

fof(f184,plain,
    ( spl4_15
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f195,plain,
    ( spl4_16
  <=> ! [X2] :
        ( k2_relat_1(sK1) = k4_enumset1(X2,X2,X2,X2,X2,X2)
        | k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f201,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,sK0) != X1
        | k1_xboole_0 = k2_relat_1(sK1)
        | k2_relat_1(sK1) = k4_enumset1(X1,X1,X1,X1,X1,X1) )
    | ~ spl4_16 ),
    inference(duplicate_literal_removal,[],[f200])).

fof(f200,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,sK0) != X1
        | k1_xboole_0 = k2_relat_1(sK1)
        | k2_relat_1(sK1) = k4_enumset1(X1,X1,X1,X1,X1,X1)
        | k2_relat_1(sK1) = k4_enumset1(X1,X1,X1,X1,X1,X1) )
    | ~ spl4_16 ),
    inference(superposition,[],[f77,f196])).

fof(f196,plain,
    ( ! [X2] :
        ( k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X2)
        | k2_relat_1(sK1) = k4_enumset1(X2,X2,X2,X2,X2,X2) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f195])).

fof(f77,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f49,f73])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f198,plain,
    ( spl4_16
    | spl4_15
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f193,f155,f141,f184,f195])).

fof(f141,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( k1_funct_1(sK1,X0) = X1
        | ~ r2_hidden(X1,k11_relat_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f155,plain,
    ( spl4_9
  <=> k2_relat_1(sK1) = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f193,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k2_relat_1(sK1)
        | k2_relat_1(sK1) = k4_enumset1(X2,X2,X2,X2,X2,X2)
        | k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X2) )
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(resolution,[],[f78,f168])).

fof(f168,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(sK1))
        | k1_funct_1(sK1,sK0) = X2 )
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(superposition,[],[f142,f156])).

fof(f156,plain,
    ( k2_relat_1(sK1) = k11_relat_1(sK1,sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f155])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k11_relat_1(sK1,X0))
        | k1_funct_1(sK1,X0) = X1 )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f141])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f48,f73])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f186,plain,
    ( ~ spl4_4
    | ~ spl4_5
    | ~ spl4_15
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f170,f155,f184,f126,f116])).

fof(f116,plain,
    ( spl4_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f126,plain,
    ( spl4_5
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f170,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl4_9 ),
    inference(superposition,[],[f46,f156])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f158,plain,
    ( ~ spl4_4
    | spl4_9
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f153,f149,f155,f116])).

fof(f149,plain,
    ( spl4_8
  <=> k11_relat_1(sK1,sK0) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f153,plain,
    ( k2_relat_1(sK1) = k11_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl4_8 ),
    inference(superposition,[],[f43,f150])).

fof(f150,plain,
    ( k11_relat_1(sK1,sK0) = k9_relat_1(sK1,k1_relat_1(sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f149])).

fof(f43,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f151,plain,
    ( spl4_8
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f147,f116,f108,f149])).

fof(f108,plain,
    ( spl4_2
  <=> k1_relat_1(sK1) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f147,plain,
    ( k11_relat_1(sK1,sK0) = k9_relat_1(sK1,k1_relat_1(sK1))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f146,f109])).

fof(f109,plain,
    ( k1_relat_1(sK1) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f146,plain,
    ( ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k4_enumset1(X0,X0,X0,X0,X0,X0))
    | ~ spl4_4 ),
    inference(resolution,[],[f76,f117])).

fof(f117,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k4_enumset1(X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f44,f73])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f143,plain,
    ( ~ spl4_4
    | spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f139,f136,f141,f116])).

fof(f136,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK1,X0) = X1
        | ~ r2_hidden(X1,k11_relat_1(sK1,X0))
        | ~ v1_relat_1(sK1) )
    | ~ spl4_6 ),
    inference(resolution,[],[f137,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f137,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = X1 )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f138,plain,
    ( ~ spl4_4
    | spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f133,f112,f136,f116])).

fof(f112,plain,
    ( spl4_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = X1
        | ~ v1_relat_1(sK1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f54,f113])).

fof(f113,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f128,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f124,f108,f126])).

fof(f124,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl4_2 ),
    inference(superposition,[],[f93,f109])).

fof(f93,plain,(
    ! [X2,X0,X7,X3,X1] : r2_hidden(X7,k4_enumset1(X0,X0,X1,X2,X3,X7)) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | k4_enumset1(X0,X0,X1,X2,X3,X7) != X5 ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f63,f57])).

fof(f63,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ( ( ( sK3(X0,X1,X2,X3,X4,X5) != X4
              & sK3(X0,X1,X2,X3,X4,X5) != X3
              & sK3(X0,X1,X2,X3,X4,X5) != X2
              & sK3(X0,X1,X2,X3,X4,X5) != X1
              & sK3(X0,X1,X2,X3,X4,X5) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK3(X0,X1,X2,X3,X4,X5) = X4
            | sK3(X0,X1,X2,X3,X4,X5) = X3
            | sK3(X0,X1,X2,X3,X4,X5) = X2
            | sK3(X0,X1,X2,X3,X4,X5) = X1
            | sK3(X0,X1,X2,X3,X4,X5) = X0
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4,X5) != X4
            & sK3(X0,X1,X2,X3,X4,X5) != X3
            & sK3(X0,X1,X2,X3,X4,X5) != X2
            & sK3(X0,X1,X2,X3,X4,X5) != X1
            & sK3(X0,X1,X2,X3,X4,X5) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK3(X0,X1,X2,X3,X4,X5) = X4
          | sK3(X0,X1,X2,X3,X4,X5) = X3
          | sK3(X0,X1,X2,X3,X4,X5) = X2
          | sK3(X0,X1,X2,X3,X4,X5) = X1
          | sK3(X0,X1,X2,X3,X4,X5) = X0
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(f118,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f38,f116])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    & k1_tarski(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
      & k1_tarski(sK0) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f114,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f39,f112])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f110,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f75,f108])).

fof(f75,plain,(
    k1_relat_1(sK1) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f40,f73])).

fof(f40,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f106,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f74,f104])).

fof(f74,plain,(
    k2_relat_1(sK1) != k4_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f41,f73])).

fof(f41,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (1476)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (1476)Refutation not found, incomplete strategy% (1476)------------------------------
% 0.20/0.50  % (1476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1476)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1476)Memory used [KB]: 10618
% 0.20/0.50  % (1476)Time elapsed: 0.076 s
% 0.20/0.50  % (1476)------------------------------
% 0.20/0.50  % (1476)------------------------------
% 0.20/0.50  % (1484)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.51  % (1484)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f220,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f106,f110,f114,f118,f128,f138,f143,f151,f158,f186,f198,f213,f219])).
% 0.20/0.51  fof(f219,plain,(
% 0.20/0.51    spl4_1 | ~spl4_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f217,f211,f104])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    spl4_1 <=> k2_relat_1(sK1) = k4_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.51  fof(f211,plain,(
% 0.20/0.51    spl4_19 <=> ! [X1] : (k1_funct_1(sK1,sK0) != X1 | k2_relat_1(sK1) = k4_enumset1(X1,X1,X1,X1,X1,X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.51  fof(f217,plain,(
% 0.20/0.51    k2_relat_1(sK1) = k4_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | ~spl4_19),
% 0.20/0.51    inference(equality_resolution,[],[f212])).
% 0.20/0.51  fof(f212,plain,(
% 0.20/0.51    ( ! [X1] : (k1_funct_1(sK1,sK0) != X1 | k2_relat_1(sK1) = k4_enumset1(X1,X1,X1,X1,X1,X1)) ) | ~spl4_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f211])).
% 0.20/0.51  fof(f213,plain,(
% 0.20/0.51    spl4_15 | spl4_19 | ~spl4_16),
% 0.20/0.51    inference(avatar_split_clause,[],[f201,f195,f211,f184])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    spl4_15 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.51  fof(f195,plain,(
% 0.20/0.51    spl4_16 <=> ! [X2] : (k2_relat_1(sK1) = k4_enumset1(X2,X2,X2,X2,X2,X2) | k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.51  fof(f201,plain,(
% 0.20/0.51    ( ! [X1] : (k1_funct_1(sK1,sK0) != X1 | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k4_enumset1(X1,X1,X1,X1,X1,X1)) ) | ~spl4_16),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f200])).
% 0.20/0.51  fof(f200,plain,(
% 0.20/0.51    ( ! [X1] : (k1_funct_1(sK1,sK0) != X1 | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k4_enumset1(X1,X1,X1,X1,X1,X1) | k2_relat_1(sK1) = k4_enumset1(X1,X1,X1,X1,X1,X1)) ) | ~spl4_16),
% 0.20/0.51    inference(superposition,[],[f77,f196])).
% 0.20/0.51  fof(f196,plain,(
% 0.20/0.51    ( ! [X2] : (k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X2) | k2_relat_1(sK1) = k4_enumset1(X2,X2,X2,X2,X2,X2)) ) | ~spl4_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f195])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f49,f73])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f42,f72])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f45,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f50,f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f56,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    spl4_16 | spl4_15 | ~spl4_7 | ~spl4_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f193,f155,f141,f184,f195])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    spl4_7 <=> ! [X1,X0] : (k1_funct_1(sK1,X0) = X1 | ~r2_hidden(X1,k11_relat_1(sK1,X0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.51  fof(f155,plain,(
% 0.20/0.51    spl4_9 <=> k2_relat_1(sK1) = k11_relat_1(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.51  fof(f193,plain,(
% 0.20/0.51    ( ! [X2] : (k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k4_enumset1(X2,X2,X2,X2,X2,X2) | k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),X2)) ) | (~spl4_7 | ~spl4_9)),
% 0.20/0.51    inference(resolution,[],[f78,f168])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK1)) | k1_funct_1(sK1,sK0) = X2) ) | (~spl4_7 | ~spl4_9)),
% 0.20/0.51    inference(superposition,[],[f142,f156])).
% 0.20/0.51  fof(f156,plain,(
% 0.20/0.51    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) | ~spl4_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f155])).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X1,k11_relat_1(sK1,X0)) | k1_funct_1(sK1,X0) = X1) ) | ~spl4_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f141])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f48,f73])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    ~spl4_4 | ~spl4_5 | ~spl4_15 | ~spl4_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f170,f155,f184,f126,f116])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    spl4_4 <=> v1_relat_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    spl4_5 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    k1_xboole_0 != k2_relat_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl4_9),
% 0.20/0.51    inference(superposition,[],[f46,f156])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.20/0.51  fof(f158,plain,(
% 0.20/0.51    ~spl4_4 | spl4_9 | ~spl4_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f153,f149,f155,f116])).
% 0.20/0.51  fof(f149,plain,(
% 0.20/0.51    spl4_8 <=> k11_relat_1(sK1,sK0) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | ~spl4_8),
% 0.20/0.51    inference(superposition,[],[f43,f150])).
% 0.20/0.51  fof(f150,plain,(
% 0.20/0.51    k11_relat_1(sK1,sK0) = k9_relat_1(sK1,k1_relat_1(sK1)) | ~spl4_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f149])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    spl4_8 | ~spl4_2 | ~spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f147,f116,f108,f149])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    spl4_2 <=> k1_relat_1(sK1) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    k11_relat_1(sK1,sK0) = k9_relat_1(sK1,k1_relat_1(sK1)) | (~spl4_2 | ~spl4_4)),
% 0.20/0.51    inference(superposition,[],[f146,f109])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    k1_relat_1(sK1) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) | ~spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f108])).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k4_enumset1(X0,X0,X0,X0,X0,X0))) ) | ~spl4_4),
% 0.20/0.51    inference(resolution,[],[f76,f117])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    v1_relat_1(sK1) | ~spl4_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f116])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k4_enumset1(X1,X1,X1,X1,X1,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f44,f73])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.20/0.51  fof(f143,plain,(
% 0.20/0.51    ~spl4_4 | spl4_7 | ~spl4_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f139,f136,f141,f116])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    spl4_6 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_funct_1(sK1,X0) = X1 | ~r2_hidden(X1,k11_relat_1(sK1,X0)) | ~v1_relat_1(sK1)) ) | ~spl4_6),
% 0.20/0.51    inference(resolution,[],[f137,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(nnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1) ) | ~spl4_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f136])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    ~spl4_4 | spl4_6 | ~spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f133,f112,f136,f116])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    spl4_3 <=> v1_funct_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1 | ~v1_relat_1(sK1)) ) | ~spl4_3),
% 0.20/0.51    inference(resolution,[],[f54,f113])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    v1_funct_1(sK1) | ~spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f112])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(nnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    spl4_5 | ~spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f124,f108,f126])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl4_2),
% 0.20/0.51    inference(superposition,[],[f93,f109])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    ( ! [X2,X0,X7,X3,X1] : (r2_hidden(X7,k4_enumset1(X0,X0,X1,X2,X3,X7))) )),
% 0.20/0.51    inference(equality_resolution,[],[f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    ( ! [X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | k4_enumset1(X0,X0,X1,X2,X3,X7) != X5) )),
% 0.20/0.51    inference(equality_resolution,[],[f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X4 != X7 | k4_enumset1(X0,X0,X1,X2,X3,X4) != X5) )),
% 0.20/0.51    inference(definition_unfolding,[],[f63,f57])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X4 != X7 | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 0.20/0.51    inference(cnf_transformation,[],[f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | (((sK3(X0,X1,X2,X3,X4,X5) != X4 & sK3(X0,X1,X2,X3,X4,X5) != X3 & sK3(X0,X1,X2,X3,X4,X5) != X2 & sK3(X0,X1,X2,X3,X4,X5) != X1 & sK3(X0,X1,X2,X3,X4,X5) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)) & (sK3(X0,X1,X2,X3,X4,X5) = X4 | sK3(X0,X1,X2,X3,X4,X5) = X3 | sK3(X0,X1,X2,X3,X4,X5) = X2 | sK3(X0,X1,X2,X3,X4,X5) = X1 | sK3(X0,X1,X2,X3,X4,X5) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5))) => (((sK3(X0,X1,X2,X3,X4,X5) != X4 & sK3(X0,X1,X2,X3,X4,X5) != X3 & sK3(X0,X1,X2,X3,X4,X5) != X2 & sK3(X0,X1,X2,X3,X4,X5) != X1 & sK3(X0,X1,X2,X3,X4,X5) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)) & (sK3(X0,X1,X2,X3,X4,X5) = X4 | sK3(X0,X1,X2,X3,X4,X5) = X3 | sK3(X0,X1,X2,X3,X4,X5) = X2 | sK3(X0,X1,X2,X3,X4,X5) = X1 | sK3(X0,X1,X2,X3,X4,X5) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.20/0.51    inference(rectify,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.20/0.51    inference(flattening,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.20/0.51    inference(nnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f38,f116])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    v1_relat_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.51    inference(negated_conjecture,[],[f13])).
% 0.20/0.51  fof(f13,conjecture,(
% 0.20/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f39,f112])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    v1_funct_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f75,f108])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    k1_relat_1(sK1) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.51    inference(definition_unfolding,[],[f40,f73])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ~spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f74,f104])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    k2_relat_1(sK1) != k4_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.20/0.51    inference(definition_unfolding,[],[f41,f73])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (1484)------------------------------
% 0.20/0.51  % (1484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1484)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (1484)Memory used [KB]: 10874
% 0.20/0.51  % (1484)Time elapsed: 0.096 s
% 0.20/0.51  % (1484)------------------------------
% 0.20/0.51  % (1484)------------------------------
% 0.20/0.52  % (1464)Success in time 0.155 s
%------------------------------------------------------------------------------
