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
% DateTime   : Thu Dec  3 12:54:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 187 expanded)
%              Number of leaves         :   21 (  75 expanded)
%              Depth                    :    8
%              Number of atoms          :  208 ( 376 expanded)
%              Number of equality atoms :   53 ( 123 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f91,f97,f112,f114,f121,f129,f143,f146])).

fof(f146,plain,(
    spl2_15 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl2_15 ),
    inference(resolution,[],[f142,f44])).

fof(f44,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_enumset1(X1,X1,X1)) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f33,f35])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f28])).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f142,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl2_15
  <=> r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f143,plain,
    ( ~ spl2_15
    | spl2_8
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f131,f125,f88,f140])).

fof(f88,plain,
    ( spl2_8
  <=> r1_tarski(k11_relat_1(sK1,sK0),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f125,plain,
    ( spl2_13
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f131,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | spl2_8
    | ~ spl2_13 ),
    inference(backward_demodulation,[],[f90,f127])).

fof(f127,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f125])).

fof(f90,plain,
    ( ~ r1_tarski(k11_relat_1(sK1,sK0),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f129,plain,
    ( spl2_13
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f123,f118,f56,f125])).

fof(f56,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f118,plain,
    ( spl2_12
  <=> k1_xboole_0 = k9_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f123,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(superposition,[],[f81,f120])).

fof(f120,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f81,plain,
    ( ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_enumset1(X0,X0,X0))
    | ~ spl2_3 ),
    inference(resolution,[],[f37,f58])).

fof(f58,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f26,f35])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f121,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f116,f105,f61,f56,f118])).

fof(f61,plain,
    ( spl2_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f105,plain,
    ( spl2_10
  <=> k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f116,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f115,f63])).

fof(f63,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f115,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(superposition,[],[f70,f107])).

fof(f107,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f70,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)
    | ~ spl2_3 ),
    inference(resolution,[],[f29,f58])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f114,plain,
    ( spl2_10
    | ~ spl2_9
    | spl2_11 ),
    inference(avatar_split_clause,[],[f113,f109,f95,f105])).

fof(f95,plain,
    ( spl2_9
  <=> ! [X0] :
        ( k11_relat_1(sK1,X0) = k1_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0))
        | k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(X0,X0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f109,plain,
    ( spl2_11
  <=> r1_tarski(k11_relat_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f113,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))
    | ~ spl2_9
    | spl2_11 ),
    inference(resolution,[],[f101,f111])).

fof(f111,plain,
    ( ~ r1_tarski(k11_relat_1(sK1,sK0),k11_relat_1(sK1,sK0))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f101,plain,
    ( ! [X3] :
        ( r1_tarski(k11_relat_1(sK1,X3),k11_relat_1(sK1,X3))
        | k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(X3,X3,X3)) )
    | ~ spl2_9 ),
    inference(superposition,[],[f43,f96])).

fof(f96,plain,
    ( ! [X0] :
        ( k11_relat_1(sK1,X0) = k1_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0))
        | k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(X0,X0,X0)) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f43,plain,(
    ! [X1] : r1_tarski(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) != X0
      | r1_tarski(X0,k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f34,f35,f35])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f112,plain,
    ( spl2_10
    | ~ spl2_11
    | spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f98,f95,f88,f109,f105])).

fof(f98,plain,
    ( ~ r1_tarski(k11_relat_1(sK1,sK0),k11_relat_1(sK1,sK0))
    | k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))
    | spl2_8
    | ~ spl2_9 ),
    inference(superposition,[],[f90,f96])).

fof(f97,plain,
    ( spl2_9
    | ~ spl2_3
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f92,f56,f51,f56,f95])).

fof(f51,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | k11_relat_1(sK1,X0) = k1_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0))
        | k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(X0,X0,X0)) )
    | ~ spl2_3 ),
    inference(resolution,[],[f39,f84])).

fof(f84,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_relat_1(sK1))
        | k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(X0,X0,X0)) )
    | ~ spl2_3 ),
    inference(resolution,[],[f71,f58])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k1_enumset1(X1,X1,X1))
      | r2_hidden(X1,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f27,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_enumset1(X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f35])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k11_relat_1(X1,X0) = k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) ) ),
    inference(definition_unfolding,[],[f31,f35])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(f91,plain,
    ( ~ spl2_8
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f86,f56,f46,f88])).

fof(f46,plain,
    ( spl2_1
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f86,plain,
    ( ~ r1_tarski(k11_relat_1(sK1,sK0),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | spl2_1
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f85,f81])).

fof(f85,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | spl2_1
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f48,f70])).

fof(f48,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f64,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f24,f61])).

fof(f24,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f59,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f20,f56])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

fof(f54,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f36,f46])).

fof(f36,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f22,f35,f35])).

fof(f22,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:57:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (17540)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.50  % (17522)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.50  % (17530)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.50  % (17532)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.50  % (17537)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.50  % (17537)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f91,f97,f112,f114,f121,f129,f143,f146])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    spl2_15),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f144])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    $false | spl2_15),
% 0.22/0.50    inference(resolution,[],[f142,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_enumset1(X1,X1,X1))) )),
% 0.22/0.50    inference(equality_resolution,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_enumset1(X1,X1,X1))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f33,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f25,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    ~r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | spl2_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f140])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    spl2_15 <=> r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    ~spl2_15 | spl2_8 | ~spl2_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f131,f125,f88,f140])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl2_8 <=> r1_tarski(k11_relat_1(sK1,sK0),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    spl2_13 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    ~r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | (spl2_8 | ~spl2_13)),
% 0.22/0.50    inference(backward_demodulation,[],[f90,f127])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl2_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f125])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    ~r1_tarski(k11_relat_1(sK1,sK0),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | spl2_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f88])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    spl2_13 | ~spl2_3 | ~spl2_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f123,f118,f56,f125])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    spl2_3 <=> v1_relat_1(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    spl2_12 <=> k1_xboole_0 = k9_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    k1_xboole_0 = k11_relat_1(sK1,sK0) | (~spl2_3 | ~spl2_12)),
% 0.22/0.50    inference(superposition,[],[f81,f120])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    k1_xboole_0 = k9_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)) | ~spl2_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f118])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_enumset1(X0,X0,X0))) ) | ~spl2_3),
% 0.22/0.50    inference(resolution,[],[f37,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    v1_relat_1(sK1) | ~spl2_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f56])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f26,f35])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    spl2_12 | ~spl2_3 | ~spl2_4 | ~spl2_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f116,f105,f61,f56,f118])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    spl2_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    spl2_10 <=> k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    k1_xboole_0 = k9_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)) | (~spl2_3 | ~spl2_4 | ~spl2_10)),
% 0.22/0.50    inference(forward_demodulation,[],[f115,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl2_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f61])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)) | (~spl2_3 | ~spl2_10)),
% 0.22/0.50    inference(superposition,[],[f70,f107])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)) | ~spl2_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f105])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) ) | ~spl2_3),
% 0.22/0.50    inference(resolution,[],[f29,f58])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    spl2_10 | ~spl2_9 | spl2_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f113,f109,f95,f105])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    spl2_9 <=> ! [X0] : (k11_relat_1(sK1,X0) = k1_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0)) | k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(X0,X0,X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    spl2_11 <=> r1_tarski(k11_relat_1(sK1,sK0),k11_relat_1(sK1,sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)) | (~spl2_9 | spl2_11)),
% 0.22/0.50    inference(resolution,[],[f101,f111])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    ~r1_tarski(k11_relat_1(sK1,sK0),k11_relat_1(sK1,sK0)) | spl2_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f109])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ( ! [X3] : (r1_tarski(k11_relat_1(sK1,X3),k11_relat_1(sK1,X3)) | k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(X3,X3,X3))) ) | ~spl2_9),
% 0.22/0.50    inference(superposition,[],[f43,f96])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ( ! [X0] : (k11_relat_1(sK1,X0) = k1_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0)) | k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(X0,X0,X0))) ) | ~spl2_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f95])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X1] : (r1_tarski(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))) )),
% 0.22/0.50    inference(equality_resolution,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) != X0 | r1_tarski(X0,k1_enumset1(X1,X1,X1))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f34,f35,f35])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    spl2_10 | ~spl2_11 | spl2_8 | ~spl2_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f98,f95,f88,f109,f105])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ~r1_tarski(k11_relat_1(sK1,sK0),k11_relat_1(sK1,sK0)) | k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)) | (spl2_8 | ~spl2_9)),
% 0.22/0.50    inference(superposition,[],[f90,f96])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    spl2_9 | ~spl2_3 | ~spl2_2 | ~spl2_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f92,f56,f51,f56,f95])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    spl2_2 <=> v1_funct_1(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k11_relat_1(sK1,X0) = k1_enumset1(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0),k1_funct_1(sK1,X0)) | k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(X0,X0,X0))) ) | ~spl2_3),
% 0.22/0.50    inference(resolution,[],[f39,f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,k1_enumset1(X0,X0,X0))) ) | ~spl2_3),
% 0.22/0.51    inference(resolution,[],[f71,f58])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_enumset1(X1,X1,X1)) | r2_hidden(X1,k1_relat_1(X0))) )),
% 0.22/0.51    inference(resolution,[],[f27,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(k1_enumset1(X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f30,f35])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k11_relat_1(X1,X0) = k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f31,f35])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    ~spl2_8 | spl2_1 | ~spl2_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f86,f56,f46,f88])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    spl2_1 <=> r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ~r1_tarski(k11_relat_1(sK1,sK0),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | (spl2_1 | ~spl2_3)),
% 0.22/0.51    inference(forward_demodulation,[],[f85,f81])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ~r1_tarski(k9_relat_1(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | (spl2_1 | ~spl2_3)),
% 0.22/0.51    inference(forward_demodulation,[],[f48,f70])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | spl2_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f46])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    spl2_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f24,f61])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    spl2_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f20,f56])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    v1_relat_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.51    inference(negated_conjecture,[],[f10])).
% 0.22/0.51  fof(f10,conjecture,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    spl2_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f21,f51])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    v1_funct_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ~spl2_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f36,f46])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 0.22/0.51    inference(definition_unfolding,[],[f22,f35,f35])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (17537)------------------------------
% 0.22/0.51  % (17537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17537)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (17537)Memory used [KB]: 10746
% 0.22/0.51  % (17537)Time elapsed: 0.093 s
% 0.22/0.51  % (17537)------------------------------
% 0.22/0.51  % (17537)------------------------------
% 0.22/0.51  % (17532)Refutation not found, incomplete strategy% (17532)------------------------------
% 0.22/0.51  % (17532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17532)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (17532)Memory used [KB]: 10618
% 0.22/0.51  % (17532)Time elapsed: 0.083 s
% 0.22/0.51  % (17532)------------------------------
% 0.22/0.51  % (17532)------------------------------
% 0.22/0.51  % (17519)Success in time 0.146 s
%------------------------------------------------------------------------------
