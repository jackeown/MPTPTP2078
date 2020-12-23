%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 492 expanded)
%              Number of leaves         :   23 ( 165 expanded)
%              Depth                    :   13
%              Number of atoms          :  246 ( 895 expanded)
%              Number of equality atoms :   78 ( 604 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f467,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f111,f135,f228,f241,f312,f338,f451,f466])).

fof(f466,plain,
    ( spl7_2
    | spl7_4 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | spl7_2
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f89,f434,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f434,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl7_2
    | spl7_4 ),
    inference(forward_demodulation,[],[f433,f159])).

fof(f159,plain,
    ( k1_xboole_0 = sK1
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f110,f154,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f36,f69,f69])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f65,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f154,plain,(
    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f83,f70])).

fof(f70,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f35,f69,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f67])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f35,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f51,f68])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f110,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl7_4
  <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f433,plain,
    ( ~ r1_xboole_0(sK1,sK1)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f101,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f101,plain,
    ( k1_xboole_0 != sK1
    | spl7_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f89,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f451,plain,
    ( spl7_4
    | ~ spl7_6
    | spl7_7 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | spl7_4
    | ~ spl7_6
    | spl7_7 ),
    inference(unit_resulting_resolution,[],[f226,f421])).

fof(f421,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl7_4
    | spl7_7 ),
    inference(backward_demodulation,[],[f311,f159])).

fof(f311,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl7_7
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f226,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl7_6
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f338,plain,
    ( spl7_3
    | ~ spl7_4
    | spl7_7 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | spl7_3
    | ~ spl7_4
    | spl7_7 ),
    inference(unit_resulting_resolution,[],[f311,f330])).

fof(f330,plain,
    ( r1_tarski(sK1,sK2)
    | spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f325,f109])).

fof(f109,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f325,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK2)
    | spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f315,f315,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f54,f67])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f315,plain,
    ( r2_hidden(sK0,sK2)
    | spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f292,f256])).

fof(f256,plain,
    ( ! [X0] :
        ( r1_xboole_0(sK1,X0)
        | r2_hidden(sK0,X0) )
    | ~ spl7_4 ),
    inference(superposition,[],[f78,f109])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f69])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f292,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f286,f58])).

fof(f286,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl7_3
    | ~ spl7_4 ),
    inference(superposition,[],[f116,f242])).

fof(f242,plain,
    ( sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f70,f109])).

fof(f116,plain,
    ( ! [X0] : ~ r1_xboole_0(sK2,k3_tarski(k2_enumset1(X0,X0,X0,sK2)))
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f112,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f112,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f106,f39])).

fof(f106,plain,
    ( k1_xboole_0 != sK2
    | spl7_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f312,plain,
    ( ~ spl7_7
    | spl7_5
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f247,f108,f132,f309])).

fof(f132,plain,
    ( spl7_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f247,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK1,sK2)
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f153,f109])).

fof(f153,plain,
    ( sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ r1_tarski(sK1,sK2) ),
    inference(superposition,[],[f70,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f68])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f241,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f41,f229,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f43,f69])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f229,plain,
    ( r2_hidden(sK3(k1_xboole_0,sK2),k1_xboole_0)
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f227,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f227,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f225])).

fof(f41,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f228,plain,
    ( spl7_1
    | ~ spl7_6
    | spl7_4 ),
    inference(avatar_split_clause,[],[f164,f108,f225,f95])).

fof(f95,plain,
    ( spl7_1
  <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f164,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | spl7_4 ),
    inference(backward_demodulation,[],[f153,f159])).

fof(f135,plain,
    ( ~ spl7_5
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f93,f108,f132])).

fof(f93,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f71])).

fof(f71,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK2 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f34,f69,f69])).

fof(f34,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f111,plain,
    ( ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f73,f108,f104])).

fof(f73,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f32,f69])).

fof(f32,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f102,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f72,f99,f95])).

fof(f72,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f33,f69])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (5143)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (5138)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (5159)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (5151)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (5150)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (5163)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (5160)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (5137)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (5141)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (5139)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (5136)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (5157)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (5156)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (5152)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (5145)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (5155)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (5141)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f467,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f102,f111,f135,f228,f241,f312,f338,f451,f466])).
% 0.20/0.52  fof(f466,plain,(
% 0.20/0.52    spl7_2 | spl7_4),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f455])).
% 0.20/0.52  fof(f455,plain,(
% 0.20/0.52    $false | (spl7_2 | spl7_4)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f89,f434,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.52  fof(f434,plain,(
% 0.20/0.52    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (spl7_2 | spl7_4)),
% 0.20/0.52    inference(forward_demodulation,[],[f433,f159])).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | spl7_4),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f110,f154,f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(definition_unfolding,[],[f36,f69,f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f45,f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f65,f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 0.20/0.52  fof(f154,plain,(
% 0.20/0.52    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.52    inference(superposition,[],[f83,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))),
% 0.20/0.52    inference(definition_unfolding,[],[f35,f69,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f50,f67])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,axiom,(
% 0.20/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.20/0.52    inference(negated_conjecture,[],[f22])).
% 0.20/0.52  fof(f22,conjecture,(
% 0.20/0.52    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f51,f68])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | spl7_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f108])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    spl7_4 <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.52  fof(f433,plain,(
% 0.20/0.52    ~r1_xboole_0(sK1,sK1) | spl7_2),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f101,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | spl7_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f99])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    spl7_2 <=> k1_xboole_0 = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.52    inference(equality_resolution,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f451,plain,(
% 0.20/0.52    spl7_4 | ~spl7_6 | spl7_7),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f446])).
% 0.20/0.52  fof(f446,plain,(
% 0.20/0.52    $false | (spl7_4 | ~spl7_6 | spl7_7)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f226,f421])).
% 0.20/0.52  fof(f421,plain,(
% 0.20/0.52    ~r1_tarski(k1_xboole_0,sK2) | (spl7_4 | spl7_7)),
% 0.20/0.52    inference(backward_demodulation,[],[f311,f159])).
% 0.20/0.52  fof(f311,plain,(
% 0.20/0.52    ~r1_tarski(sK1,sK2) | spl7_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f309])).
% 0.20/0.52  fof(f309,plain,(
% 0.20/0.52    spl7_7 <=> r1_tarski(sK1,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.52  fof(f226,plain,(
% 0.20/0.52    r1_tarski(k1_xboole_0,sK2) | ~spl7_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f225])).
% 0.20/0.52  fof(f225,plain,(
% 0.20/0.52    spl7_6 <=> r1_tarski(k1_xboole_0,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.52  fof(f338,plain,(
% 0.20/0.52    spl7_3 | ~spl7_4 | spl7_7),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f334])).
% 0.20/0.52  fof(f334,plain,(
% 0.20/0.52    $false | (spl7_3 | ~spl7_4 | spl7_7)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f311,f330])).
% 0.20/0.52  fof(f330,plain,(
% 0.20/0.52    r1_tarski(sK1,sK2) | (spl7_3 | ~spl7_4)),
% 0.20/0.52    inference(forward_demodulation,[],[f325,f109])).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl7_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f108])).
% 0.20/0.52  fof(f325,plain,(
% 0.20/0.52    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK2) | (spl7_3 | ~spl7_4)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f315,f315,f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f54,f67])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.20/0.52  fof(f315,plain,(
% 0.20/0.52    r2_hidden(sK0,sK2) | (spl7_3 | ~spl7_4)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f292,f256])).
% 0.20/0.52  fof(f256,plain,(
% 0.20/0.52    ( ! [X0] : (r1_xboole_0(sK1,X0) | r2_hidden(sK0,X0)) ) | ~spl7_4),
% 0.20/0.52    inference(superposition,[],[f78,f109])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f44,f69])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,axiom,(
% 0.20/0.52    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.20/0.52  fof(f292,plain,(
% 0.20/0.52    ~r1_xboole_0(sK1,sK2) | (spl7_3 | ~spl7_4)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f286,f58])).
% 0.20/0.52  fof(f286,plain,(
% 0.20/0.52    ~r1_xboole_0(sK2,sK1) | (spl7_3 | ~spl7_4)),
% 0.20/0.52    inference(superposition,[],[f116,f242])).
% 0.20/0.52  fof(f242,plain,(
% 0.20/0.52    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl7_4),
% 0.20/0.52    inference(backward_demodulation,[],[f70,f109])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_xboole_0(sK2,k3_tarski(k2_enumset1(X0,X0,X0,sK2)))) ) | spl7_3),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f112,f80])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f47,f68])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.20/0.52  fof(f112,plain,(
% 0.20/0.52    ~r1_xboole_0(sK2,sK2) | spl7_3),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f106,f39])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    k1_xboole_0 != sK2 | spl7_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f104])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    spl7_3 <=> k1_xboole_0 = sK2),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.52  fof(f312,plain,(
% 0.20/0.52    ~spl7_7 | spl7_5 | ~spl7_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f247,f108,f132,f309])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    spl7_5 <=> sK1 = sK2),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.52  fof(f247,plain,(
% 0.20/0.52    sK1 = sK2 | ~r1_tarski(sK1,sK2) | ~spl7_4),
% 0.20/0.52    inference(backward_demodulation,[],[f153,f109])).
% 0.20/0.52  fof(f153,plain,(
% 0.20/0.52    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | ~r1_tarski(sK1,sK2)),
% 0.20/0.52    inference(superposition,[],[f70,f82])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f49,f68])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.52  fof(f241,plain,(
% 0.20/0.52    spl7_6),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f234])).
% 0.20/0.52  fof(f234,plain,(
% 0.20/0.52    $false | spl7_6),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f41,f229,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f43,f69])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,axiom,(
% 0.20/0.52    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.20/0.52  fof(f229,plain,(
% 0.20/0.52    r2_hidden(sK3(k1_xboole_0,sK2),k1_xboole_0) | spl7_6),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f227,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  fof(f227,plain,(
% 0.20/0.52    ~r1_tarski(k1_xboole_0,sK2) | spl7_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f225])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.52  fof(f228,plain,(
% 0.20/0.52    spl7_1 | ~spl7_6 | spl7_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f164,f108,f225,f95])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    spl7_1 <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.52  fof(f164,plain,(
% 0.20/0.52    ~r1_tarski(k1_xboole_0,sK2) | sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | spl7_4),
% 0.20/0.52    inference(backward_demodulation,[],[f153,f159])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    ~spl7_5 | ~spl7_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f93,f108,f132])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != sK2),
% 0.20/0.52    inference(inner_rewriting,[],[f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | sK2 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.52    inference(definition_unfolding,[],[f34,f69,f69])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    ~spl7_3 | ~spl7_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f73,f108,f104])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 0.20/0.52    inference(definition_unfolding,[],[f32,f69])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    ~spl7_1 | ~spl7_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f72,f99,f95])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | sK2 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.52    inference(definition_unfolding,[],[f33,f69])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (5141)------------------------------
% 0.20/0.52  % (5141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5141)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (5141)Memory used [KB]: 6396
% 0.20/0.52  % (5141)Time elapsed: 0.122 s
% 0.20/0.52  % (5141)------------------------------
% 0.20/0.52  % (5141)------------------------------
% 0.20/0.52  % (5152)Refutation not found, incomplete strategy% (5152)------------------------------
% 0.20/0.52  % (5152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5152)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5152)Memory used [KB]: 6140
% 0.20/0.52  % (5152)Time elapsed: 0.004 s
% 0.20/0.52  % (5152)------------------------------
% 0.20/0.52  % (5152)------------------------------
% 0.20/0.53  % (5133)Success in time 0.17 s
%------------------------------------------------------------------------------
