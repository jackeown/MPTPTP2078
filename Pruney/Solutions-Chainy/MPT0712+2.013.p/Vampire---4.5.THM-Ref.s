%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:44 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 148 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  253 ( 368 expanded)
%              Number of equality atoms :   42 (  73 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f920,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f81,f86,f96,f164,f173,f241,f919])).

fof(f919,plain,
    ( spl2_12
    | ~ spl2_1
    | ~ spl2_16
    | ~ spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f918,f83,f78,f232,f63,f157])).

fof(f157,plain,
    ( spl2_12
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f63,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f232,plain,
    ( spl2_16
  <=> r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f78,plain,
    ( spl2_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f83,plain,
    ( spl2_5
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f918,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl2_4
    | spl2_5 ),
    inference(forward_demodulation,[],[f887,f80])).

fof(f80,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f887,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK0,k1_relat_1(sK1))
    | spl2_5 ),
    inference(superposition,[],[f85,f860])).

fof(f860,plain,(
    ! [X8,X7] :
      ( k1_xboole_0 = k7_relat_1(X7,k2_enumset1(X8,X8,X8,X8))
      | ~ v1_relat_1(X7)
      | r2_hidden(X8,k1_relat_1(X7)) ) ),
    inference(duplicate_literal_removal,[],[f840])).

fof(f840,plain,(
    ! [X8,X7] :
      ( ~ v1_relat_1(X7)
      | k1_xboole_0 = k7_relat_1(X7,k2_enumset1(X8,X8,X8,X8))
      | r2_hidden(X8,k1_relat_1(X7))
      | ~ v1_relat_1(X7) ) ),
    inference(resolution,[],[f822,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f822,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))))
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(factoring,[],[f268])).

fof(f268,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_relat_1(k7_relat_1(X0,k2_enumset1(X1,X1,X1,X2))))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k2_enumset1(X1,X1,X1,X2))
      | r2_hidden(X1,k1_relat_1(k7_relat_1(X0,k2_enumset1(X1,X1,X1,X2)))) ) ),
    inference(resolution,[],[f260,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f260,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(k7_relat_1(X0,X1)))
      | k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f126,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f126,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1(X8,X9)),X10)
      | k1_xboole_0 = k7_relat_1(X8,X9)
      | ~ r1_xboole_0(X9,X10)
      | ~ v1_relat_1(X8) ) ),
    inference(global_subsumption,[],[f50,f120])).

fof(f120,plain,(
    ! [X10,X8,X9] :
      ( k1_xboole_0 = k7_relat_1(X8,X9)
      | ~ r1_tarski(k1_relat_1(k7_relat_1(X8,X9)),X10)
      | ~ v1_relat_1(k7_relat_1(X8,X9))
      | ~ r1_xboole_0(X9,X10)
      | ~ v1_relat_1(X8) ) ),
    inference(superposition,[],[f40,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f85,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f241,plain,(
    spl2_16 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | spl2_16 ),
    inference(unit_resulting_resolution,[],[f41,f234])).

fof(f234,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | spl2_16 ),
    inference(avatar_component_clause,[],[f232])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f173,plain,(
    spl2_13 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl2_13 ),
    inference(unit_resulting_resolution,[],[f60,f163])).

fof(f163,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl2_13
  <=> r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f164,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_12
    | ~ spl2_13
    | spl2_6 ),
    inference(avatar_split_clause,[],[f155,f93,f161,f157,f68,f63])).

fof(f68,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f93,plain,
    ( spl2_6
  <=> r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f155,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_6 ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_6 ),
    inference(superposition,[],[f95,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1)) = k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f42,f55,f55])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

fof(f95,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f96,plain,
    ( ~ spl2_1
    | ~ spl2_6
    | spl2_5 ),
    inference(avatar_split_clause,[],[f91,f83,f93,f63])).

fof(f91,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | ~ v1_relat_1(sK1)
    | spl2_5 ),
    inference(superposition,[],[f85,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f86,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f57,f83])).

fof(f57,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f36,f56,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f55])).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

fof(f81,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f45,f78])).

fof(f45,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f71,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f35,f68])).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f34,f63])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (8003)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.48  % (8028)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.48  % (8020)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.49  % (8011)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.50  % (8025)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (8017)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (8013)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (8024)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (8016)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.28/0.52  % (8016)Refutation not found, incomplete strategy% (8016)------------------------------
% 1.28/0.52  % (8016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (8016)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.52  
% 1.28/0.52  % (8016)Memory used [KB]: 1663
% 1.28/0.52  % (8016)Time elapsed: 0.062 s
% 1.28/0.52  % (8016)------------------------------
% 1.28/0.52  % (8016)------------------------------
% 1.28/0.52  % (8008)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.53  % (8006)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.28/0.53  % (8004)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.28/0.53  % (8002)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.28/0.53  % (8007)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.28/0.54  % (8015)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.45/0.54  % (8022)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.45/0.54  % (8021)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.45/0.54  % (8019)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.45/0.55  % (8030)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.45/0.55  % (8029)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.45/0.55  % (8027)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.45/0.55  % (8029)Refutation not found, incomplete strategy% (8029)------------------------------
% 1.45/0.55  % (8029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (8029)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (8029)Memory used [KB]: 6140
% 1.45/0.55  % (8029)Time elapsed: 0.136 s
% 1.45/0.55  % (8029)------------------------------
% 1.45/0.55  % (8029)------------------------------
% 1.45/0.55  % (8001)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.45/0.55  % (8031)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.45/0.55  % (8030)Refutation not found, incomplete strategy% (8030)------------------------------
% 1.45/0.55  % (8030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (8030)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (8030)Memory used [KB]: 10746
% 1.45/0.55  % (8030)Time elapsed: 0.137 s
% 1.45/0.55  % (8030)------------------------------
% 1.45/0.55  % (8030)------------------------------
% 1.45/0.55  % (8031)Refutation not found, incomplete strategy% (8031)------------------------------
% 1.45/0.55  % (8031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (8031)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (8031)Memory used [KB]: 1663
% 1.45/0.55  % (8031)Time elapsed: 0.136 s
% 1.45/0.55  % (8031)------------------------------
% 1.45/0.55  % (8031)------------------------------
% 1.45/0.55  % (8014)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.45/0.55  % (8023)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.45/0.55  % (8012)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.45/0.55  % (8010)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.45/0.55  % (8012)Refutation not found, incomplete strategy% (8012)------------------------------
% 1.45/0.55  % (8012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (8012)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (8012)Memory used [KB]: 10746
% 1.45/0.55  % (8012)Time elapsed: 0.148 s
% 1.45/0.55  % (8012)------------------------------
% 1.45/0.55  % (8012)------------------------------
% 1.45/0.56  % (8009)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.45/0.56  % (8018)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.45/0.57  % (8018)Refutation not found, incomplete strategy% (8018)------------------------------
% 1.45/0.57  % (8018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (8018)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (8018)Memory used [KB]: 10618
% 1.45/0.57  % (8018)Time elapsed: 0.156 s
% 1.45/0.57  % (8018)------------------------------
% 1.45/0.57  % (8018)------------------------------
% 1.45/0.57  % (8026)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.45/0.57  % (8026)Refutation not found, incomplete strategy% (8026)------------------------------
% 1.45/0.57  % (8026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (8026)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (8026)Memory used [KB]: 10618
% 1.45/0.57  % (8026)Time elapsed: 0.155 s
% 1.45/0.57  % (8026)------------------------------
% 1.45/0.57  % (8026)------------------------------
% 1.45/0.59  % (8025)Refutation found. Thanks to Tanya!
% 1.45/0.59  % SZS status Theorem for theBenchmark
% 1.45/0.59  % SZS output start Proof for theBenchmark
% 1.45/0.59  fof(f920,plain,(
% 1.45/0.59    $false),
% 1.45/0.59    inference(avatar_sat_refutation,[],[f66,f71,f81,f86,f96,f164,f173,f241,f919])).
% 1.45/0.59  fof(f919,plain,(
% 1.45/0.59    spl2_12 | ~spl2_1 | ~spl2_16 | ~spl2_4 | spl2_5),
% 1.45/0.59    inference(avatar_split_clause,[],[f918,f83,f78,f232,f63,f157])).
% 1.45/0.59  fof(f157,plain,(
% 1.45/0.59    spl2_12 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 1.45/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.45/0.59  fof(f63,plain,(
% 1.45/0.59    spl2_1 <=> v1_relat_1(sK1)),
% 1.45/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.45/0.59  fof(f232,plain,(
% 1.45/0.59    spl2_16 <=> r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 1.45/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.45/0.59  fof(f78,plain,(
% 1.45/0.59    spl2_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.45/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.45/0.59  fof(f83,plain,(
% 1.45/0.59    spl2_5 <=> r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 1.45/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.45/0.59  fof(f918,plain,(
% 1.45/0.59    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | ~v1_relat_1(sK1) | r2_hidden(sK0,k1_relat_1(sK1)) | (~spl2_4 | spl2_5)),
% 1.45/0.59    inference(forward_demodulation,[],[f887,f80])).
% 1.45/0.59  fof(f80,plain,(
% 1.45/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl2_4),
% 1.45/0.59    inference(avatar_component_clause,[],[f78])).
% 1.45/0.59  fof(f887,plain,(
% 1.45/0.59    ~r1_tarski(k2_relat_1(k1_xboole_0),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | ~v1_relat_1(sK1) | r2_hidden(sK0,k1_relat_1(sK1)) | spl2_5),
% 1.45/0.59    inference(superposition,[],[f85,f860])).
% 1.45/0.59  fof(f860,plain,(
% 1.45/0.59    ( ! [X8,X7] : (k1_xboole_0 = k7_relat_1(X7,k2_enumset1(X8,X8,X8,X8)) | ~v1_relat_1(X7) | r2_hidden(X8,k1_relat_1(X7))) )),
% 1.45/0.59    inference(duplicate_literal_removal,[],[f840])).
% 1.45/0.59  fof(f840,plain,(
% 1.45/0.59    ( ! [X8,X7] : (~v1_relat_1(X7) | k1_xboole_0 = k7_relat_1(X7,k2_enumset1(X8,X8,X8,X8)) | r2_hidden(X8,k1_relat_1(X7)) | ~v1_relat_1(X7)) )),
% 1.45/0.59    inference(resolution,[],[f822,f47])).
% 1.45/0.59  fof(f47,plain,(
% 1.45/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f33])).
% 1.45/0.59  fof(f33,plain,(
% 1.45/0.59    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 1.45/0.59    inference(flattening,[],[f32])).
% 1.45/0.59  fof(f32,plain,(
% 1.45/0.59    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 1.45/0.59    inference(nnf_transformation,[],[f23])).
% 1.45/0.59  fof(f23,plain,(
% 1.45/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 1.45/0.59    inference(ennf_transformation,[],[f11])).
% 1.45/0.59  fof(f11,axiom,(
% 1.45/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 1.45/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 1.45/0.60  fof(f822,plain,(
% 1.45/0.60    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0)))) | ~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))) )),
% 1.45/0.60    inference(factoring,[],[f268])).
% 1.45/0.60  fof(f268,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_relat_1(k7_relat_1(X0,k2_enumset1(X1,X1,X1,X2)))) | ~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k2_enumset1(X1,X1,X1,X2)) | r2_hidden(X1,k1_relat_1(k7_relat_1(X0,k2_enumset1(X1,X1,X1,X2))))) )),
% 1.45/0.60    inference(resolution,[],[f260,f59])).
% 1.45/0.60  fof(f59,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 1.45/0.60    inference(definition_unfolding,[],[f52,f55])).
% 1.45/0.60  fof(f55,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.45/0.60    inference(definition_unfolding,[],[f53,f54])).
% 1.45/0.60  fof(f54,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f5])).
% 1.45/0.60  fof(f5,axiom,(
% 1.45/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.45/0.60  fof(f53,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f4])).
% 1.45/0.60  fof(f4,axiom,(
% 1.45/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.45/0.60  fof(f52,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f27])).
% 1.45/0.60  fof(f27,plain,(
% 1.45/0.60    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 1.45/0.60    inference(ennf_transformation,[],[f6])).
% 1.45/0.60  fof(f6,axiom,(
% 1.45/0.60    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 1.45/0.60  fof(f260,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(k7_relat_1(X0,X1))) | k1_xboole_0 = k7_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.45/0.60    inference(resolution,[],[f126,f60])).
% 1.45/0.60  fof(f60,plain,(
% 1.45/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.45/0.60    inference(equality_resolution,[],[f38])).
% 1.45/0.60  fof(f38,plain,(
% 1.45/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.45/0.60    inference(cnf_transformation,[],[f31])).
% 1.45/0.60  fof(f31,plain,(
% 1.45/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.45/0.60    inference(flattening,[],[f30])).
% 1.45/0.60  fof(f30,plain,(
% 1.45/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.45/0.60    inference(nnf_transformation,[],[f1])).
% 1.45/0.60  fof(f1,axiom,(
% 1.45/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.45/0.60  fof(f126,plain,(
% 1.45/0.60    ( ! [X10,X8,X9] : (~r1_tarski(k1_relat_1(k7_relat_1(X8,X9)),X10) | k1_xboole_0 = k7_relat_1(X8,X9) | ~r1_xboole_0(X9,X10) | ~v1_relat_1(X8)) )),
% 1.45/0.60    inference(global_subsumption,[],[f50,f120])).
% 1.45/0.60  fof(f120,plain,(
% 1.45/0.60    ( ! [X10,X8,X9] : (k1_xboole_0 = k7_relat_1(X8,X9) | ~r1_tarski(k1_relat_1(k7_relat_1(X8,X9)),X10) | ~v1_relat_1(k7_relat_1(X8,X9)) | ~r1_xboole_0(X9,X10) | ~v1_relat_1(X8)) )),
% 1.45/0.60    inference(superposition,[],[f40,f49])).
% 1.45/0.60  fof(f49,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f25])).
% 1.45/0.60  fof(f25,plain,(
% 1.45/0.60    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 1.45/0.60    inference(flattening,[],[f24])).
% 1.45/0.60  fof(f24,plain,(
% 1.45/0.60    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.45/0.60    inference(ennf_transformation,[],[f9])).
% 1.45/0.60  fof(f9,axiom,(
% 1.45/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 1.45/0.60  fof(f40,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f19])).
% 1.45/0.60  fof(f19,plain,(
% 1.45/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.45/0.60    inference(flattening,[],[f18])).
% 1.45/0.60  fof(f18,plain,(
% 1.45/0.60    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.45/0.60    inference(ennf_transformation,[],[f12])).
% 1.45/0.60  fof(f12,axiom,(
% 1.45/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.45/0.60  fof(f50,plain,(
% 1.45/0.60    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f26])).
% 1.45/0.60  fof(f26,plain,(
% 1.45/0.60    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.45/0.60    inference(ennf_transformation,[],[f7])).
% 1.45/0.60  fof(f7,axiom,(
% 1.45/0.60    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.45/0.60  fof(f85,plain,(
% 1.45/0.60    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | spl2_5),
% 1.45/0.60    inference(avatar_component_clause,[],[f83])).
% 1.45/0.60  fof(f241,plain,(
% 1.45/0.60    spl2_16),
% 1.45/0.60    inference(avatar_contradiction_clause,[],[f236])).
% 1.45/0.60  fof(f236,plain,(
% 1.45/0.60    $false | spl2_16),
% 1.45/0.60    inference(unit_resulting_resolution,[],[f41,f234])).
% 1.45/0.60  fof(f234,plain,(
% 1.45/0.60    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | spl2_16),
% 1.45/0.60    inference(avatar_component_clause,[],[f232])).
% 1.45/0.60  fof(f41,plain,(
% 1.45/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f2])).
% 1.45/0.60  fof(f2,axiom,(
% 1.45/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.45/0.60  fof(f173,plain,(
% 1.45/0.60    spl2_13),
% 1.45/0.60    inference(avatar_contradiction_clause,[],[f169])).
% 1.45/0.60  fof(f169,plain,(
% 1.45/0.60    $false | spl2_13),
% 1.45/0.60    inference(unit_resulting_resolution,[],[f60,f163])).
% 1.45/0.60  fof(f163,plain,(
% 1.45/0.60    ~r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | spl2_13),
% 1.45/0.60    inference(avatar_component_clause,[],[f161])).
% 1.45/0.60  fof(f161,plain,(
% 1.45/0.60    spl2_13 <=> r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.45/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.45/0.60  fof(f164,plain,(
% 1.45/0.60    ~spl2_1 | ~spl2_2 | ~spl2_12 | ~spl2_13 | spl2_6),
% 1.45/0.60    inference(avatar_split_clause,[],[f155,f93,f161,f157,f68,f63])).
% 1.45/0.60  fof(f68,plain,(
% 1.45/0.60    spl2_2 <=> v1_funct_1(sK1)),
% 1.45/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.45/0.60  fof(f93,plain,(
% 1.45/0.60    spl2_6 <=> r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 1.45/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.45/0.60  fof(f155,plain,(
% 1.45/0.60    ~r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_6),
% 1.45/0.60    inference(duplicate_literal_removal,[],[f152])).
% 1.45/0.60  fof(f152,plain,(
% 1.45/0.60    ~r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_6),
% 1.45/0.60    inference(superposition,[],[f95,f58])).
% 1.45/0.60  fof(f58,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1)) = k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.45/0.60    inference(definition_unfolding,[],[f42,f55,f55])).
% 1.45/0.60  fof(f42,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f21])).
% 1.45/0.60  fof(f21,plain,(
% 1.45/0.60    ! [X0,X1,X2] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.45/0.60    inference(flattening,[],[f20])).
% 1.45/0.60  fof(f20,plain,(
% 1.45/0.60    ! [X0,X1,X2] : ((k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.45/0.60    inference(ennf_transformation,[],[f13])).
% 1.45/0.60  fof(f13,axiom,(
% 1.45/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).
% 1.45/0.60  fof(f95,plain,(
% 1.45/0.60    ~r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | spl2_6),
% 1.45/0.60    inference(avatar_component_clause,[],[f93])).
% 1.45/0.60  fof(f96,plain,(
% 1.45/0.60    ~spl2_1 | ~spl2_6 | spl2_5),
% 1.45/0.60    inference(avatar_split_clause,[],[f91,f83,f93,f63])).
% 1.45/0.60  fof(f91,plain,(
% 1.45/0.60    ~r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) | ~v1_relat_1(sK1) | spl2_5),
% 1.45/0.60    inference(superposition,[],[f85,f43])).
% 1.45/0.60  fof(f43,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f22])).
% 1.45/0.60  fof(f22,plain,(
% 1.45/0.60    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.45/0.60    inference(ennf_transformation,[],[f8])).
% 1.45/0.60  fof(f8,axiom,(
% 1.45/0.60    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.45/0.60  fof(f86,plain,(
% 1.45/0.60    ~spl2_5),
% 1.45/0.60    inference(avatar_split_clause,[],[f57,f83])).
% 1.45/0.60  fof(f57,plain,(
% 1.45/0.60    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 1.45/0.60    inference(definition_unfolding,[],[f36,f56,f56])).
% 1.45/0.60  fof(f56,plain,(
% 1.45/0.60    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.45/0.60    inference(definition_unfolding,[],[f51,f55])).
% 1.45/0.60  fof(f51,plain,(
% 1.45/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f3])).
% 1.45/0.60  fof(f3,axiom,(
% 1.45/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.45/0.60  fof(f36,plain,(
% 1.45/0.60    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 1.45/0.60    inference(cnf_transformation,[],[f29])).
% 1.45/0.60  fof(f29,plain,(
% 1.45/0.60    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.45/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f28])).
% 1.45/0.60  fof(f28,plain,(
% 1.45/0.60    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.45/0.60    introduced(choice_axiom,[])).
% 1.45/0.60  fof(f17,plain,(
% 1.45/0.60    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.45/0.60    inference(flattening,[],[f16])).
% 1.45/0.60  fof(f16,plain,(
% 1.45/0.60    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.45/0.60    inference(ennf_transformation,[],[f15])).
% 1.45/0.60  fof(f15,negated_conjecture,(
% 1.45/0.60    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 1.45/0.60    inference(negated_conjecture,[],[f14])).
% 1.45/0.60  fof(f14,conjecture,(
% 1.45/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).
% 1.45/0.60  fof(f81,plain,(
% 1.45/0.60    spl2_4),
% 1.45/0.60    inference(avatar_split_clause,[],[f45,f78])).
% 1.45/0.60  fof(f45,plain,(
% 1.45/0.60    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.45/0.60    inference(cnf_transformation,[],[f10])).
% 1.45/0.60  fof(f10,axiom,(
% 1.45/0.60    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.45/0.60  fof(f71,plain,(
% 1.45/0.60    spl2_2),
% 1.45/0.60    inference(avatar_split_clause,[],[f35,f68])).
% 1.45/0.60  fof(f35,plain,(
% 1.45/0.60    v1_funct_1(sK1)),
% 1.45/0.60    inference(cnf_transformation,[],[f29])).
% 1.45/0.60  fof(f66,plain,(
% 1.45/0.60    spl2_1),
% 1.45/0.60    inference(avatar_split_clause,[],[f34,f63])).
% 1.45/0.60  fof(f34,plain,(
% 1.45/0.60    v1_relat_1(sK1)),
% 1.45/0.60    inference(cnf_transformation,[],[f29])).
% 1.45/0.60  % SZS output end Proof for theBenchmark
% 1.45/0.60  % (8025)------------------------------
% 1.45/0.60  % (8025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.60  % (8025)Termination reason: Refutation
% 1.45/0.60  
% 1.45/0.60  % (8025)Memory used [KB]: 11385
% 1.45/0.60  % (8025)Time elapsed: 0.181 s
% 1.45/0.60  % (8025)------------------------------
% 1.45/0.60  % (8025)------------------------------
% 1.45/0.60  % (7997)Success in time 0.244 s
%------------------------------------------------------------------------------
