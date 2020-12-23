%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:15 EST 2020

% Result     : Theorem 6.53s
% Output     : Refutation 6.53s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 729 expanded)
%              Number of leaves         :   54 ( 258 expanded)
%              Depth                    :   14
%              Number of atoms          :  638 (1890 expanded)
%              Number of equality atoms :  231 ( 770 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5925,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f101,f111,f116,f133,f175,f207,f242,f243,f249,f275,f336,f862,f1413,f1420,f1422,f1430,f1451,f1489,f1521,f2452,f2456,f5008,f5224,f5412,f5802,f5803,f5896,f5924])).

fof(f5924,plain,
    ( k1_xboole_0 != sK5
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | r1_xboole_0(sK5,sK5) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f5896,plain,
    ( ~ spl10_55
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_56
    | spl10_68 ),
    inference(avatar_split_clause,[],[f5895,f1408,f809,f113,f108,f805])).

fof(f805,plain,
    ( spl10_55
  <=> r1_xboole_0(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).

fof(f108,plain,
    ( spl10_8
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f113,plain,
    ( spl10_9
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f809,plain,
    ( spl10_56
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f1408,plain,
    ( spl10_68
  <=> r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).

fof(f5895,plain,
    ( ~ r1_xboole_0(sK5,sK5)
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_56
    | spl10_68 ),
    inference(subsumption_resolution,[],[f5894,f235])).

fof(f235,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl10_8
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f229,f147])).

fof(f147,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f146,f42])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f146,plain,(
    ! [X0] : ~ r2_hidden(X0,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0))) ),
    inference(superposition,[],[f74,f50])).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f74,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k4_enumset1(X2,X2,X2,X2,X2,X2)))) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k4_enumset1(X2,X2,X2,X2,X2,X2)))) ) ),
    inference(definition_unfolding,[],[f56,f51,f67])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f229,plain,
    ( ! [X0] :
        ( r2_hidden(sK9(k1_xboole_0,X0),k1_xboole_0)
        | r1_xboole_0(k1_xboole_0,X0) )
    | ~ spl10_8
    | ~ spl10_9 ),
    inference(superposition,[],[f52,f219])).

fof(f219,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)
    | ~ spl10_8
    | ~ spl10_9 ),
    inference(forward_demodulation,[],[f218,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f218,plain,
    ( ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k9_relat_1(k1_xboole_0,X0),X1)
    | ~ spl10_8
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f217,f115])).

fof(f115,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k3_xboole_0(k9_relat_1(k1_xboole_0,X0),X1)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f215,f110])).

fof(f110,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f215,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k3_xboole_0(k9_relat_1(k1_xboole_0,X0),X1)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f54,f41])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_funct_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK9(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f24,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK9(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f5894,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ r1_xboole_0(sK5,sK5)
    | ~ spl10_56
    | spl10_68 ),
    inference(forward_demodulation,[],[f1530,f811])).

fof(f811,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK6)
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f809])).

fof(f1530,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK6),k3_zfmisc_1(sK0,sK1,sK2))
    | ~ r1_xboole_0(sK5,sK5)
    | spl10_68 ),
    inference(superposition,[],[f1410,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X1,X0)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f64,f119])).

fof(f119,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f118,f48])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( r1_xboole_0(sK8(X0),X0)
        & r2_hidden(sK8(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f23,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_xboole_0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( r1_xboole_0(sK8(X0),X0)
        & r2_hidden(sK8(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_xboole_0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f53,f50])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f1410,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k3_zfmisc_1(sK0,sK1,sK2))
    | spl10_68 ),
    inference(avatar_component_clause,[],[f1408])).

fof(f5803,plain,
    ( spl10_2
    | ~ spl10_153
    | spl10_164
    | spl10_165 ),
    inference(avatar_contradiction_clause,[],[f5801])).

fof(f5801,plain,
    ( $false
    | spl10_2
    | ~ spl10_153
    | spl10_164
    | spl10_165 ),
    inference(unit_resulting_resolution,[],[f82,f5183,f5007,f5187,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f5187,plain,
    ( k1_xboole_0 != sK5
    | spl10_165 ),
    inference(avatar_component_clause,[],[f5186])).

fof(f5186,plain,
    ( spl10_165
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_165])])).

fof(f5007,plain,
    ( k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK0,sK1)
    | ~ spl10_153 ),
    inference(avatar_component_clause,[],[f5005])).

fof(f5005,plain,
    ( spl10_153
  <=> k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_153])])).

fof(f5183,plain,
    ( k1_xboole_0 != sK4
    | spl10_164 ),
    inference(avatar_component_clause,[],[f5182])).

fof(f5182,plain,
    ( spl10_164
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_164])])).

fof(f82,plain,
    ( sK1 != sK5
    | spl10_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl10_2
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f5802,plain,
    ( spl10_1
    | ~ spl10_153
    | spl10_164
    | spl10_165 ),
    inference(avatar_contradiction_clause,[],[f5800])).

fof(f5800,plain,
    ( $false
    | spl10_1
    | ~ spl10_153
    | spl10_164
    | spl10_165 ),
    inference(unit_resulting_resolution,[],[f78,f5183,f5007,f5187,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,
    ( sK0 != sK4
    | spl10_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl10_1
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f5412,plain,
    ( ~ spl10_57
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_56
    | spl10_68 ),
    inference(avatar_split_clause,[],[f5411,f1408,f809,f113,f108,f814])).

fof(f814,plain,
    ( spl10_57
  <=> r1_xboole_0(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).

fof(f5411,plain,
    ( ~ r1_xboole_0(sK4,sK4)
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_56
    | spl10_68 ),
    inference(subsumption_resolution,[],[f5410,f235])).

fof(f5410,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ r1_xboole_0(sK4,sK4)
    | ~ spl10_56
    | spl10_68 ),
    inference(forward_demodulation,[],[f1531,f811])).

fof(f1531,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK6),k3_zfmisc_1(sK0,sK1,sK2))
    | ~ r1_xboole_0(sK4,sK4)
    | spl10_68 ),
    inference(superposition,[],[f1410,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f63,f119])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5224,plain,
    ( k1_xboole_0 != sK4
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | r1_xboole_0(sK4,sK4) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f5008,plain,
    ( spl10_153
    | spl10_58
    | spl10_59
    | ~ spl10_69
    | ~ spl10_72 ),
    inference(avatar_split_clause,[],[f5003,f1518,f1445,f825,f821,f5005])).

fof(f821,plain,
    ( spl10_58
  <=> k1_xboole_0 = k2_zfmisc_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f825,plain,
    ( spl10_59
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_59])])).

fof(f1445,plain,
    ( spl10_69
  <=> k3_zfmisc_1(sK0,sK1,sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).

fof(f1518,plain,
    ( spl10_72
  <=> k3_zfmisc_1(sK0,sK1,sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f5003,plain,
    ( k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK0,sK1)
    | spl10_58
    | spl10_59
    | ~ spl10_69
    | ~ spl10_72 ),
    inference(trivial_inequality_removal,[],[f4988])).

fof(f4988,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(sK0,sK1,sK2)
    | k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK0,sK1)
    | spl10_58
    | spl10_59
    | ~ spl10_69
    | ~ spl10_72 ),
    inference(superposition,[],[f1599,f1520])).

fof(f1520,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl10_72 ),
    inference(avatar_component_clause,[],[f1518])).

fof(f1599,plain,
    ( ! [X4,X5] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k2_zfmisc_1(X4,X5)
        | k2_zfmisc_1(sK4,sK5) = X4 )
    | spl10_58
    | spl10_59
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f1598,f822])).

fof(f822,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK4,sK5)
    | spl10_58 ),
    inference(avatar_component_clause,[],[f821])).

fof(f1598,plain,
    ( ! [X4,X5] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k2_zfmisc_1(X4,X5)
        | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
        | k2_zfmisc_1(sK4,sK5) = X4 )
    | spl10_59
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f1577,f826])).

fof(f826,plain,
    ( k1_xboole_0 != sK6
    | spl10_59 ),
    inference(avatar_component_clause,[],[f825])).

fof(f1577,plain,
    ( ! [X4,X5] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k2_zfmisc_1(X4,X5)
        | k1_xboole_0 = sK6
        | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
        | k2_zfmisc_1(sK4,sK5) = X4 )
    | ~ spl10_69 ),
    inference(superposition,[],[f61,f1447])).

fof(f1447,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | ~ spl10_69 ),
    inference(avatar_component_clause,[],[f1445])).

fof(f2456,plain,
    ( k1_xboole_0 != sK6
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | r1_xboole_0(sK6,sK6) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2452,plain,
    ( spl10_3
    | spl10_58
    | spl10_59
    | ~ spl10_69
    | ~ spl10_72 ),
    inference(avatar_split_clause,[],[f2435,f1518,f1445,f825,f821,f84])).

fof(f84,plain,
    ( spl10_3
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f2435,plain,
    ( sK2 = sK6
    | spl10_58
    | spl10_59
    | ~ spl10_69
    | ~ spl10_72 ),
    inference(trivial_inequality_removal,[],[f2428])).

fof(f2428,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(sK0,sK1,sK2)
    | sK2 = sK6
    | spl10_58
    | spl10_59
    | ~ spl10_69
    | ~ spl10_72 ),
    inference(superposition,[],[f1601,f1520])).

fof(f1601,plain,
    ( ! [X8,X9] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k2_zfmisc_1(X8,X9)
        | sK6 = X9 )
    | spl10_58
    | spl10_59
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f1600,f822])).

fof(f1600,plain,
    ( ! [X8,X9] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k2_zfmisc_1(X8,X9)
        | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
        | sK6 = X9 )
    | spl10_59
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f1579,f826])).

fof(f1579,plain,
    ( ! [X8,X9] :
        ( k3_zfmisc_1(sK0,sK1,sK2) != k2_zfmisc_1(X8,X9)
        | k1_xboole_0 = sK6
        | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
        | sK6 = X9 )
    | ~ spl10_69 ),
    inference(superposition,[],[f62,f1447])).

fof(f1521,plain,
    ( spl10_72
    | ~ spl10_6
    | spl10_13
    | spl10_14
    | ~ spl10_27 ),
    inference(avatar_split_clause,[],[f1509,f333,f169,f165,f98,f1518])).

fof(f98,plain,
    ( spl10_6
  <=> k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f165,plain,
    ( spl10_13
  <=> k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f169,plain,
    ( spl10_14
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f333,plain,
    ( spl10_27
  <=> k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f1509,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl10_6
    | spl10_13
    | spl10_14
    | ~ spl10_27 ),
    inference(equality_resolution,[],[f730])).

fof(f730,plain,
    ( ! [X2,X0,X3,X1] :
        ( k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(sK0,sK1,sK2) )
    | ~ spl10_6
    | spl10_13
    | spl10_14
    | ~ spl10_27 ),
    inference(forward_demodulation,[],[f729,f335])).

fof(f335,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6)
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f333])).

fof(f729,plain,
    ( ! [X2,X0,X3,X1] :
        ( k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(sK4,sK5,sK6) )
    | ~ spl10_6
    | spl10_13
    | spl10_14 ),
    inference(subsumption_resolution,[],[f728,f166])).

fof(f166,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK4,sK5,sK6)
    | spl10_13 ),
    inference(avatar_component_clause,[],[f165])).

fof(f728,plain,
    ( ! [X2,X0,X3,X1] :
        ( k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6)
        | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(sK4,sK5,sK6) )
    | ~ spl10_6
    | spl10_14 ),
    inference(subsumption_resolution,[],[f713,f170])).

fof(f170,plain,
    ( k1_xboole_0 != sK7
    | spl10_14 ),
    inference(avatar_component_clause,[],[f169])).

fof(f713,plain,
    ( ! [X2,X0,X3,X1] :
        ( k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k1_xboole_0 = sK7
        | k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6)
        | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(sK4,sK5,sK6) )
    | ~ spl10_6 ),
    inference(superposition,[],[f162,f100])).

fof(f100,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f162,plain,(
    ! [X6,X4,X2,X7,X5,X3] :
      ( k2_zfmisc_1(k3_zfmisc_1(X2,X3,X4),X5) != k2_zfmisc_1(X6,X7)
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4) = X6 ) ),
    inference(superposition,[],[f61,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f60,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

fof(f1489,plain,
    ( ~ spl10_70
    | spl10_50 ),
    inference(avatar_split_clause,[],[f1484,f759,f1486])).

fof(f1486,plain,
    ( spl10_70
  <=> r1_xboole_0(sK6,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f759,plain,
    ( spl10_50
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f1484,plain,
    ( ~ r1_xboole_0(sK6,sK6)
    | spl10_50 ),
    inference(trivial_inequality_removal,[],[f1481])).

fof(f1481,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(sK6,sK6)
    | spl10_50 ),
    inference(superposition,[],[f760,f143])).

fof(f760,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | spl10_50 ),
    inference(avatar_component_clause,[],[f759])).

fof(f1451,plain,
    ( spl10_69
    | ~ spl10_63 ),
    inference(avatar_split_clause,[],[f1440,f860,f1445])).

fof(f860,plain,
    ( spl10_63
  <=> ! [X1,X0] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_63])])).

fof(f1440,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | ~ spl10_63 ),
    inference(equality_resolution,[],[f861])).

fof(f861,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = X0 )
    | ~ spl10_63 ),
    inference(avatar_component_clause,[],[f860])).

fof(f1430,plain,
    ( ~ spl10_8
    | ~ spl10_9
    | spl10_56 ),
    inference(avatar_contradiction_clause,[],[f1429])).

fof(f1429,plain,
    ( $false
    | ~ spl10_8
    | ~ spl10_9
    | spl10_56 ),
    inference(subsumption_resolution,[],[f1426,f235])).

fof(f1426,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl10_56 ),
    inference(trivial_inequality_removal,[],[f1425])).

fof(f1425,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl10_56 ),
    inference(superposition,[],[f810,f123])).

fof(f810,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK6)
    | spl10_56 ),
    inference(avatar_component_clause,[],[f809])).

fof(f1422,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK4,sK5)
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK6)
    | ~ r1_xboole_0(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2))
    | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1420,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | ~ r1_xboole_0(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2))
    | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1413,plain,
    ( ~ spl10_68
    | spl10_5
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f1412,f98,f93,f1408])).

fof(f93,plain,
    ( spl10_5
  <=> k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f1412,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k3_zfmisc_1(sK0,sK1,sK2))
    | spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f1396,f95])).

fof(f95,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | spl10_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f1396,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl10_6 ),
    inference(resolution,[],[f604,f119])).

fof(f604,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3),k2_zfmisc_1(X0,X1))
        | ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),X0) )
    | ~ spl10_6 ),
    inference(superposition,[],[f156,f100])).

fof(f156,plain,(
    ! [X26,X24,X23,X27,X25,X22] :
      ( r1_xboole_0(k2_zfmisc_1(k3_zfmisc_1(X22,X23,X24),X25),k2_zfmisc_1(X26,X27))
      | ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X22,X23),X24),X26) ) ),
    inference(superposition,[],[f63,f73])).

fof(f862,plain,
    ( spl10_50
    | spl10_63
    | ~ spl10_6
    | spl10_14 ),
    inference(avatar_split_clause,[],[f858,f169,f98,f860,f759])).

fof(f858,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
        | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = X0 )
    | ~ spl10_6
    | spl10_14 ),
    inference(subsumption_resolution,[],[f840,f170])).

fof(f840,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k1_xboole_0 = sK7
        | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
        | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = X0 )
    | ~ spl10_6 ),
    inference(superposition,[],[f160,f100])).

fof(f160,plain,(
    ! [X6,X4,X2,X7,X5,X3] :
      ( k2_zfmisc_1(k3_zfmisc_1(X2,X3,X4),X5) != k2_zfmisc_1(X6,X7)
      | k1_xboole_0 = X5
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)
      | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4) = X6 ) ),
    inference(superposition,[],[f61,f73])).

fof(f336,plain,
    ( spl10_27
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f331,f173,f333])).

fof(f173,plain,
    ( spl10_15
  <=> ! [X1,X0] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k3_zfmisc_1(sK4,sK5,sK6) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f331,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6)
    | ~ spl10_15 ),
    inference(equality_resolution,[],[f174])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k3_zfmisc_1(sK4,sK5,sK6) = X0 )
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f275,plain,
    ( spl10_5
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_14 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | spl10_5
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f270,f95])).

fof(f270,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_14 ),
    inference(resolution,[],[f268,f119])).

fof(f268,plain,
    ( ! [X0,X1] : r1_xboole_0(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3),k2_zfmisc_1(X0,X1))
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_9
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f267,f235])).

fof(f267,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_xboole_0,X1)
        | r1_xboole_0(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3),k2_zfmisc_1(X0,X1)) )
    | ~ spl10_6
    | ~ spl10_14 ),
    inference(forward_demodulation,[],[f144,f171])).

fof(f171,plain,
    ( k1_xboole_0 = sK7
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f169])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3),k2_zfmisc_1(X0,X1))
        | ~ r1_xboole_0(sK7,X1) )
    | ~ spl10_6 ),
    inference(superposition,[],[f64,f100])).

fof(f249,plain,
    ( spl10_4
    | ~ spl10_6
    | spl10_13
    | spl10_14 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | spl10_4
    | ~ spl10_6
    | spl10_13
    | spl10_14 ),
    inference(unit_resulting_resolution,[],[f90,f170,f100,f166,f62])).

fof(f90,plain,
    ( sK3 != sK7
    | spl10_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl10_4
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f243,plain,
    ( ~ spl10_8
    | ~ spl10_9
    | spl10_19 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl10_8
    | ~ spl10_9
    | spl10_19 ),
    inference(subsumption_resolution,[],[f206,f235])).

fof(f206,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2))
    | spl10_19 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl10_19
  <=> r1_xboole_0(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f242,plain,
    ( ~ spl10_8
    | ~ spl10_9
    | spl10_20 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | ~ spl10_8
    | ~ spl10_9
    | spl10_20 ),
    inference(subsumption_resolution,[],[f211,f235])).

fof(f211,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl10_20 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl10_20
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f207,plain,
    ( ~ spl10_19
    | spl10_10
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f200,f165,f130,f204])).

fof(f130,plain,
    ( spl10_10
  <=> r1_xboole_0(k3_zfmisc_1(sK4,sK5,sK6),k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f200,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2))
    | spl10_10
    | ~ spl10_13 ),
    inference(superposition,[],[f132,f167])).

fof(f167,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f165])).

fof(f132,plain,
    ( ~ r1_xboole_0(k3_zfmisc_1(sK4,sK5,sK6),k3_zfmisc_1(sK0,sK1,sK2))
    | spl10_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f175,plain,
    ( spl10_13
    | spl10_14
    | spl10_15
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f159,f98,f173,f169,f165])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
        | k1_xboole_0 = sK7
        | k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6)
        | k3_zfmisc_1(sK4,sK5,sK6) = X0 )
    | ~ spl10_6 ),
    inference(superposition,[],[f61,f100])).

fof(f133,plain,
    ( ~ spl10_10
    | spl10_5
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f128,f98,f93,f130])).

fof(f128,plain,
    ( ~ r1_xboole_0(k3_zfmisc_1(sK4,sK5,sK6),k3_zfmisc_1(sK0,sK1,sK2))
    | spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f126,f95])).

fof(f126,plain,
    ( ~ r1_xboole_0(k3_zfmisc_1(sK4,sK5,sK6),k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)
    | ~ spl10_6 ),
    inference(resolution,[],[f124,f119])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3),k2_zfmisc_1(X0,X1))
        | ~ r1_xboole_0(k3_zfmisc_1(sK4,sK5,sK6),X0) )
    | ~ spl10_6 ),
    inference(superposition,[],[f63,f100])).

fof(f116,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f44,f113])).

fof(f44,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

fof(f111,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f46,f108])).

fof(f46,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f101,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f69,f98])).

fof(f69,plain,(
    k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7) ),
    inference(definition_unfolding,[],[f38,f58,f58])).

fof(f38,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f22,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

fof(f96,plain,(
    ~ spl10_5 ),
    inference(avatar_split_clause,[],[f68,f93])).

fof(f68,plain,(
    k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) ),
    inference(definition_unfolding,[],[f39,f58])).

fof(f39,plain,(
    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f91,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f40,f88,f84,f80,f76])).

fof(f40,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n023.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 18:18:35 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.49  % (9422)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (9438)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (9440)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (9423)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (9426)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (9432)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (9447)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (9424)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (9432)Refutation not found, incomplete strategy% (9432)------------------------------
% 0.22/0.54  % (9432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9417)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (9432)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (9432)Memory used [KB]: 1663
% 0.22/0.54  % (9432)Time elapsed: 0.055 s
% 0.22/0.54  % (9427)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (9432)------------------------------
% 0.22/0.54  % (9432)------------------------------
% 0.22/0.54  % (9430)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (9430)Refutation not found, incomplete strategy% (9430)------------------------------
% 0.22/0.55  % (9430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (9430)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (9430)Memory used [KB]: 10618
% 0.22/0.55  % (9430)Time elapsed: 0.126 s
% 0.22/0.55  % (9430)------------------------------
% 0.22/0.55  % (9430)------------------------------
% 0.22/0.55  % (9429)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (9421)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (9419)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.56  % (9441)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.56  % (9442)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (9435)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (9448)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (9448)Refutation not found, incomplete strategy% (9448)------------------------------
% 0.22/0.56  % (9448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (9448)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (9448)Memory used [KB]: 1663
% 0.22/0.56  % (9448)Time elapsed: 0.136 s
% 0.22/0.56  % (9448)------------------------------
% 0.22/0.56  % (9448)------------------------------
% 0.22/0.56  % (9445)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (9446)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (9445)Refutation not found, incomplete strategy% (9445)------------------------------
% 0.22/0.56  % (9445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (9439)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.57  % (9437)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.57  % (9443)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.57  % (9436)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.57  % (9436)Refutation not found, incomplete strategy% (9436)------------------------------
% 0.22/0.57  % (9436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (9436)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (9436)Memory used [KB]: 1663
% 0.22/0.57  % (9436)Time elapsed: 0.138 s
% 0.22/0.57  % (9436)------------------------------
% 0.22/0.57  % (9436)------------------------------
% 0.22/0.57  % (9428)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.57  % (9434)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.58  % (9431)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.56/0.58  % (9420)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.56/0.58  % (9445)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (9445)Memory used [KB]: 6268
% 1.56/0.58  % (9445)Time elapsed: 0.138 s
% 1.56/0.58  % (9445)------------------------------
% 1.56/0.58  % (9445)------------------------------
% 1.56/0.58  % (9425)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.56/0.58  % (9434)Refutation not found, incomplete strategy% (9434)------------------------------
% 1.56/0.58  % (9434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (9433)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.56/0.59  % (9434)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.59  
% 1.56/0.59  % (9434)Memory used [KB]: 10618
% 1.56/0.59  % (9434)Time elapsed: 0.161 s
% 1.56/0.59  % (9434)------------------------------
% 1.56/0.59  % (9434)------------------------------
% 1.56/0.59  % (9446)Refutation not found, incomplete strategy% (9446)------------------------------
% 1.56/0.59  % (9446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.59  % (9446)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.59  
% 1.56/0.59  % (9446)Memory used [KB]: 6268
% 1.56/0.59  % (9446)Time elapsed: 0.141 s
% 1.56/0.59  % (9446)------------------------------
% 1.56/0.59  % (9446)------------------------------
% 1.94/0.66  % (9500)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.94/0.68  % (9502)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.94/0.69  % (9501)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.94/0.69  % (9502)Refutation not found, incomplete strategy% (9502)------------------------------
% 1.94/0.69  % (9502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.69  % (9502)Termination reason: Refutation not found, incomplete strategy
% 1.94/0.69  
% 1.94/0.69  % (9502)Memory used [KB]: 6140
% 1.94/0.69  % (9502)Time elapsed: 0.090 s
% 1.94/0.69  % (9502)------------------------------
% 1.94/0.69  % (9502)------------------------------
% 1.94/0.69  % (9421)Refutation not found, incomplete strategy% (9421)------------------------------
% 1.94/0.69  % (9421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.69  % (9421)Termination reason: Refutation not found, incomplete strategy
% 1.94/0.69  
% 1.94/0.69  % (9421)Memory used [KB]: 6140
% 1.94/0.69  % (9421)Time elapsed: 0.265 s
% 1.94/0.69  % (9421)------------------------------
% 1.94/0.69  % (9421)------------------------------
% 2.45/0.71  % (9503)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.45/0.71  % (9504)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.45/0.72  % (9505)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.45/0.74  % (9506)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.45/0.74  % (9504)Refutation not found, incomplete strategy% (9504)------------------------------
% 2.45/0.74  % (9504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.45/0.74  % (9504)Termination reason: Refutation not found, incomplete strategy
% 2.45/0.74  
% 2.45/0.74  % (9504)Memory used [KB]: 10874
% 2.45/0.74  % (9504)Time elapsed: 0.135 s
% 2.45/0.74  % (9504)------------------------------
% 2.45/0.74  % (9504)------------------------------
% 2.45/0.75  % (9417)Refutation not found, incomplete strategy% (9417)------------------------------
% 2.45/0.75  % (9417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.45/0.75  % (9417)Termination reason: Refutation not found, incomplete strategy
% 2.45/0.75  
% 2.45/0.75  % (9417)Memory used [KB]: 1791
% 2.45/0.75  % (9417)Time elapsed: 0.305 s
% 2.45/0.75  % (9417)------------------------------
% 2.45/0.75  % (9417)------------------------------
% 2.89/0.82  % (9507)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.89/0.82  % (9442)Time limit reached!
% 2.89/0.82  % (9442)------------------------------
% 2.89/0.82  % (9442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.89/0.82  % (9442)Termination reason: Time limit
% 2.89/0.82  % (9442)Termination phase: Saturation
% 2.89/0.82  
% 2.89/0.82  % (9442)Memory used [KB]: 12665
% 2.89/0.82  % (9442)Time elapsed: 0.400 s
% 2.89/0.82  % (9442)------------------------------
% 2.89/0.82  % (9442)------------------------------
% 2.89/0.83  % (9513)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.89/0.86  % (9420)Time limit reached!
% 2.89/0.86  % (9420)------------------------------
% 2.89/0.86  % (9420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.89/0.86  % (9420)Termination reason: Time limit
% 2.89/0.86  
% 2.89/0.86  % (9420)Memory used [KB]: 6780
% 2.89/0.86  % (9420)Time elapsed: 0.409 s
% 2.89/0.86  % (9420)------------------------------
% 2.89/0.86  % (9420)------------------------------
% 3.54/0.87  % (9514)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.54/0.88  % (9515)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 3.72/0.90  % (9514)Refutation not found, incomplete strategy% (9514)------------------------------
% 3.72/0.90  % (9514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.72/0.90  % (9514)Termination reason: Refutation not found, incomplete strategy
% 3.72/0.90  
% 3.72/0.90  % (9514)Memory used [KB]: 10746
% 3.72/0.90  % (9514)Time elapsed: 0.123 s
% 3.72/0.90  % (9514)------------------------------
% 3.72/0.90  % (9514)------------------------------
% 3.95/0.97  % (9522)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 3.95/0.98  % (9424)Time limit reached!
% 3.95/0.98  % (9424)------------------------------
% 3.95/0.98  % (9424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/1.00  % (9524)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 4.31/1.00  % (9424)Termination reason: Time limit
% 4.31/1.00  
% 4.31/1.00  % (9424)Memory used [KB]: 15735
% 4.31/1.00  % (9424)Time elapsed: 0.509 s
% 4.31/1.00  % (9424)------------------------------
% 4.31/1.00  % (9424)------------------------------
% 4.31/1.04  % (9425)Time limit reached!
% 4.31/1.04  % (9425)------------------------------
% 4.31/1.04  % (9425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/1.04  % (9425)Termination reason: Time limit
% 4.31/1.04  
% 4.31/1.04  % (9425)Memory used [KB]: 3965
% 4.31/1.04  % (9425)Time elapsed: 0.610 s
% 4.31/1.04  % (9425)------------------------------
% 4.31/1.04  % (9425)------------------------------
% 4.31/1.06  % (9538)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 4.31/1.06  % (9538)Refutation not found, incomplete strategy% (9538)------------------------------
% 4.31/1.06  % (9538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/1.06  % (9538)Termination reason: Refutation not found, incomplete strategy
% 4.31/1.06  
% 4.31/1.06  % (9538)Memory used [KB]: 10746
% 4.31/1.06  % (9538)Time elapsed: 0.140 s
% 4.31/1.06  % (9538)------------------------------
% 4.31/1.06  % (9538)------------------------------
% 5.52/1.14  % (9583)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 5.52/1.17  % (9603)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 6.28/1.20  % (9626)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 6.53/1.21  % (9501)Refutation found. Thanks to Tanya!
% 6.53/1.21  % SZS status Theorem for theBenchmark
% 6.53/1.22  % SZS output start Proof for theBenchmark
% 6.53/1.22  fof(f5925,plain,(
% 6.53/1.22    $false),
% 6.53/1.22    inference(avatar_sat_refutation,[],[f91,f96,f101,f111,f116,f133,f175,f207,f242,f243,f249,f275,f336,f862,f1413,f1420,f1422,f1430,f1451,f1489,f1521,f2452,f2456,f5008,f5224,f5412,f5802,f5803,f5896,f5924])).
% 6.53/1.22  fof(f5924,plain,(
% 6.53/1.22    k1_xboole_0 != sK5 | ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | r1_xboole_0(sK5,sK5)),
% 6.53/1.22    introduced(theory_tautology_sat_conflict,[])).
% 6.53/1.22  fof(f5896,plain,(
% 6.53/1.22    ~spl10_55 | ~spl10_8 | ~spl10_9 | ~spl10_56 | spl10_68),
% 6.53/1.22    inference(avatar_split_clause,[],[f5895,f1408,f809,f113,f108,f805])).
% 6.53/1.22  fof(f805,plain,(
% 6.53/1.22    spl10_55 <=> r1_xboole_0(sK5,sK5)),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).
% 6.53/1.22  fof(f108,plain,(
% 6.53/1.22    spl10_8 <=> v1_funct_1(k1_xboole_0)),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 6.53/1.22  fof(f113,plain,(
% 6.53/1.22    spl10_9 <=> v1_relat_1(k1_xboole_0)),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 6.53/1.22  fof(f809,plain,(
% 6.53/1.22    spl10_56 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK6)),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).
% 6.53/1.22  fof(f1408,plain,(
% 6.53/1.22    spl10_68 <=> r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k3_zfmisc_1(sK0,sK1,sK2))),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).
% 6.53/1.22  fof(f5895,plain,(
% 6.53/1.22    ~r1_xboole_0(sK5,sK5) | (~spl10_8 | ~spl10_9 | ~spl10_56 | spl10_68)),
% 6.53/1.22    inference(subsumption_resolution,[],[f5894,f235])).
% 6.53/1.22  fof(f235,plain,(
% 6.53/1.22    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | (~spl10_8 | ~spl10_9)),
% 6.53/1.22    inference(subsumption_resolution,[],[f229,f147])).
% 6.53/1.22  fof(f147,plain,(
% 6.53/1.22    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 6.53/1.22    inference(forward_demodulation,[],[f146,f42])).
% 6.53/1.22  fof(f42,plain,(
% 6.53/1.22    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 6.53/1.22    inference(cnf_transformation,[],[f4])).
% 6.53/1.22  fof(f4,axiom,(
% 6.53/1.22    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 6.53/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 6.53/1.22  fof(f146,plain,(
% 6.53/1.22    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k4_enumset1(X0,X0,X0,X0,X0,X0)))) )),
% 6.53/1.22    inference(superposition,[],[f74,f50])).
% 6.53/1.22  fof(f50,plain,(
% 6.53/1.22    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 6.53/1.22    inference(cnf_transformation,[],[f19])).
% 6.53/1.22  fof(f19,plain,(
% 6.53/1.22    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 6.53/1.22    inference(rectify,[],[f1])).
% 6.53/1.22  fof(f1,axiom,(
% 6.53/1.22    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 6.53/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 6.53/1.22  fof(f74,plain,(
% 6.53/1.22    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k4_enumset1(X2,X2,X2,X2,X2,X2))))) )),
% 6.53/1.22    inference(equality_resolution,[],[f71])).
% 6.53/1.22  fof(f71,plain,(
% 6.53/1.22    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k4_enumset1(X2,X2,X2,X2,X2,X2))))) )),
% 6.53/1.22    inference(definition_unfolding,[],[f56,f51,f67])).
% 6.53/1.22  fof(f67,plain,(
% 6.53/1.22    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 6.53/1.22    inference(definition_unfolding,[],[f43,f66])).
% 6.53/1.22  fof(f66,plain,(
% 6.53/1.22    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 6.53/1.22    inference(definition_unfolding,[],[f59,f65])).
% 6.53/1.22  fof(f65,plain,(
% 6.53/1.22    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 6.53/1.22    inference(cnf_transformation,[],[f6])).
% 6.53/1.22  fof(f6,axiom,(
% 6.53/1.22    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 6.53/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 6.53/1.22  fof(f59,plain,(
% 6.53/1.22    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 6.53/1.22    inference(cnf_transformation,[],[f5])).
% 6.53/1.22  fof(f5,axiom,(
% 6.53/1.22    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 6.53/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 6.53/1.22  fof(f43,plain,(
% 6.53/1.22    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 6.53/1.22    inference(cnf_transformation,[],[f7])).
% 6.53/1.22  fof(f7,axiom,(
% 6.53/1.22    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 6.53/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).
% 6.53/1.22  fof(f51,plain,(
% 6.53/1.22    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.53/1.22    inference(cnf_transformation,[],[f3])).
% 6.53/1.22  fof(f3,axiom,(
% 6.53/1.22    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.53/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 6.53/1.22  fof(f56,plain,(
% 6.53/1.22    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 6.53/1.22    inference(cnf_transformation,[],[f37])).
% 6.53/1.22  fof(f37,plain,(
% 6.53/1.22    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 6.53/1.22    inference(flattening,[],[f36])).
% 6.53/1.22  fof(f36,plain,(
% 6.53/1.22    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 6.53/1.22    inference(nnf_transformation,[],[f10])).
% 6.53/1.22  fof(f10,axiom,(
% 6.53/1.22    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 6.53/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 6.53/1.22  fof(f229,plain,(
% 6.53/1.22    ( ! [X0] : (r2_hidden(sK9(k1_xboole_0,X0),k1_xboole_0) | r1_xboole_0(k1_xboole_0,X0)) ) | (~spl10_8 | ~spl10_9)),
% 6.53/1.22    inference(superposition,[],[f52,f219])).
% 6.53/1.22  fof(f219,plain,(
% 6.53/1.22    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) ) | (~spl10_8 | ~spl10_9)),
% 6.53/1.22    inference(forward_demodulation,[],[f218,f41])).
% 6.53/1.22  fof(f41,plain,(
% 6.53/1.22    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 6.53/1.22    inference(cnf_transformation,[],[f11])).
% 6.53/1.22  fof(f11,axiom,(
% 6.53/1.22    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 6.53/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 6.53/1.22  fof(f218,plain,(
% 6.53/1.22    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k9_relat_1(k1_xboole_0,X0),X1)) ) | (~spl10_8 | ~spl10_9)),
% 6.53/1.22    inference(subsumption_resolution,[],[f217,f115])).
% 6.53/1.22  fof(f115,plain,(
% 6.53/1.22    v1_relat_1(k1_xboole_0) | ~spl10_9),
% 6.53/1.22    inference(avatar_component_clause,[],[f113])).
% 6.53/1.22  fof(f217,plain,(
% 6.53/1.22    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k9_relat_1(k1_xboole_0,X0),X1) | ~v1_relat_1(k1_xboole_0)) ) | ~spl10_8),
% 6.53/1.22    inference(subsumption_resolution,[],[f215,f110])).
% 6.53/1.22  fof(f110,plain,(
% 6.53/1.22    v1_funct_1(k1_xboole_0) | ~spl10_8),
% 6.53/1.22    inference(avatar_component_clause,[],[f108])).
% 6.53/1.22  fof(f215,plain,(
% 6.53/1.22    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k9_relat_1(k1_xboole_0,X0),X1) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 6.53/1.22    inference(superposition,[],[f54,f41])).
% 6.53/1.22  fof(f54,plain,(
% 6.53/1.22    ( ! [X2,X0,X1] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 6.53/1.22    inference(cnf_transformation,[],[f26])).
% 6.53/1.22  fof(f26,plain,(
% 6.53/1.22    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 6.53/1.22    inference(flattening,[],[f25])).
% 6.53/1.22  fof(f25,plain,(
% 6.53/1.22    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 6.53/1.22    inference(ennf_transformation,[],[f12])).
% 6.53/1.22  fof(f12,axiom,(
% 6.53/1.22    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 6.53/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_funct_1)).
% 6.53/1.22  fof(f52,plain,(
% 6.53/1.22    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 6.53/1.22    inference(cnf_transformation,[],[f35])).
% 6.53/1.22  fof(f35,plain,(
% 6.53/1.22    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK9(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 6.53/1.22    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f24,f34])).
% 6.53/1.22  fof(f34,plain,(
% 6.53/1.22    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK9(X0,X1),k3_xboole_0(X0,X1)))),
% 6.53/1.22    introduced(choice_axiom,[])).
% 6.53/1.22  fof(f24,plain,(
% 6.53/1.22    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 6.53/1.22    inference(ennf_transformation,[],[f20])).
% 6.53/1.22  fof(f20,plain,(
% 6.53/1.22    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 6.53/1.22    inference(rectify,[],[f2])).
% 6.53/1.22  fof(f2,axiom,(
% 6.53/1.22    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 6.53/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 6.53/1.22  fof(f5894,plain,(
% 6.53/1.22    ~r1_xboole_0(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2)) | ~r1_xboole_0(sK5,sK5) | (~spl10_56 | spl10_68)),
% 6.53/1.22    inference(forward_demodulation,[],[f1530,f811])).
% 6.53/1.22  fof(f811,plain,(
% 6.53/1.22    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK6) | ~spl10_56),
% 6.53/1.22    inference(avatar_component_clause,[],[f809])).
% 6.53/1.22  fof(f1530,plain,(
% 6.53/1.22    ~r1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK6),k3_zfmisc_1(sK0,sK1,sK2)) | ~r1_xboole_0(sK5,sK5) | spl10_68),
% 6.53/1.22    inference(superposition,[],[f1410,f143])).
% 6.53/1.22  fof(f143,plain,(
% 6.53/1.22    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X1,X0) | ~r1_xboole_0(X0,X0)) )),
% 6.53/1.22    inference(resolution,[],[f64,f119])).
% 6.53/1.22  fof(f119,plain,(
% 6.53/1.22    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 6.53/1.22    inference(resolution,[],[f118,f48])).
% 6.53/1.22  fof(f48,plain,(
% 6.53/1.22    ( ! [X0] : (r2_hidden(sK8(X0),X0) | k1_xboole_0 = X0) )),
% 6.53/1.22    inference(cnf_transformation,[],[f33])).
% 6.53/1.22  fof(f33,plain,(
% 6.53/1.22    ! [X0] : ((r1_xboole_0(sK8(X0),X0) & r2_hidden(sK8(X0),X0)) | k1_xboole_0 = X0)),
% 6.53/1.22    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f23,f32])).
% 6.53/1.22  fof(f32,plain,(
% 6.53/1.22    ! [X0] : (? [X1] : (r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) => (r1_xboole_0(sK8(X0),X0) & r2_hidden(sK8(X0),X0)))),
% 6.53/1.22    introduced(choice_axiom,[])).
% 6.53/1.22  fof(f23,plain,(
% 6.53/1.22    ! [X0] : (? [X1] : (r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 6.53/1.22    inference(ennf_transformation,[],[f15])).
% 6.53/1.22  fof(f15,axiom,(
% 6.53/1.22    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 6.53/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 6.53/1.22  fof(f118,plain,(
% 6.53/1.22    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r1_xboole_0(X0,X0)) )),
% 6.53/1.22    inference(superposition,[],[f53,f50])).
% 6.53/1.22  fof(f53,plain,(
% 6.53/1.22    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 6.53/1.22    inference(cnf_transformation,[],[f35])).
% 6.53/1.22  fof(f64,plain,(
% 6.53/1.22    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) )),
% 6.53/1.22    inference(cnf_transformation,[],[f29])).
% 6.53/1.22  fof(f29,plain,(
% 6.53/1.22    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 6.53/1.22    inference(ennf_transformation,[],[f8])).
% 6.53/1.22  fof(f8,axiom,(
% 6.53/1.22    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 6.53/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 6.53/1.22  fof(f1410,plain,(
% 6.53/1.22    ~r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k3_zfmisc_1(sK0,sK1,sK2)) | spl10_68),
% 6.53/1.22    inference(avatar_component_clause,[],[f1408])).
% 6.53/1.22  fof(f5803,plain,(
% 6.53/1.22    spl10_2 | ~spl10_153 | spl10_164 | spl10_165),
% 6.53/1.22    inference(avatar_contradiction_clause,[],[f5801])).
% 6.53/1.22  fof(f5801,plain,(
% 6.53/1.22    $false | (spl10_2 | ~spl10_153 | spl10_164 | spl10_165)),
% 6.53/1.22    inference(unit_resulting_resolution,[],[f82,f5183,f5007,f5187,f62])).
% 6.53/1.22  fof(f62,plain,(
% 6.53/1.22    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X1 = X3) )),
% 6.53/1.22    inference(cnf_transformation,[],[f28])).
% 6.53/1.22  fof(f28,plain,(
% 6.53/1.22    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 6.53/1.22    inference(flattening,[],[f27])).
% 6.53/1.22  fof(f27,plain,(
% 6.53/1.22    ! [X0,X1,X2,X3] : (((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 6.53/1.22    inference(ennf_transformation,[],[f9])).
% 6.53/1.22  fof(f9,axiom,(
% 6.53/1.22    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.53/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 6.53/1.22  fof(f5187,plain,(
% 6.53/1.22    k1_xboole_0 != sK5 | spl10_165),
% 6.53/1.22    inference(avatar_component_clause,[],[f5186])).
% 6.53/1.22  fof(f5186,plain,(
% 6.53/1.22    spl10_165 <=> k1_xboole_0 = sK5),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_165])])).
% 6.53/1.22  fof(f5007,plain,(
% 6.53/1.22    k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK0,sK1) | ~spl10_153),
% 6.53/1.22    inference(avatar_component_clause,[],[f5005])).
% 6.53/1.22  fof(f5005,plain,(
% 6.53/1.22    spl10_153 <=> k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK0,sK1)),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_153])])).
% 6.53/1.22  fof(f5183,plain,(
% 6.53/1.22    k1_xboole_0 != sK4 | spl10_164),
% 6.53/1.22    inference(avatar_component_clause,[],[f5182])).
% 6.53/1.22  fof(f5182,plain,(
% 6.53/1.22    spl10_164 <=> k1_xboole_0 = sK4),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_164])])).
% 6.53/1.22  fof(f82,plain,(
% 6.53/1.22    sK1 != sK5 | spl10_2),
% 6.53/1.22    inference(avatar_component_clause,[],[f80])).
% 6.53/1.22  fof(f80,plain,(
% 6.53/1.22    spl10_2 <=> sK1 = sK5),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 6.53/1.22  fof(f5802,plain,(
% 6.53/1.22    spl10_1 | ~spl10_153 | spl10_164 | spl10_165),
% 6.53/1.22    inference(avatar_contradiction_clause,[],[f5800])).
% 6.53/1.22  fof(f5800,plain,(
% 6.53/1.22    $false | (spl10_1 | ~spl10_153 | spl10_164 | spl10_165)),
% 6.53/1.22    inference(unit_resulting_resolution,[],[f78,f5183,f5007,f5187,f61])).
% 6.53/1.22  fof(f61,plain,(
% 6.53/1.22    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X0 = X2) )),
% 6.53/1.22    inference(cnf_transformation,[],[f28])).
% 6.53/1.22  fof(f78,plain,(
% 6.53/1.22    sK0 != sK4 | spl10_1),
% 6.53/1.22    inference(avatar_component_clause,[],[f76])).
% 6.53/1.22  fof(f76,plain,(
% 6.53/1.22    spl10_1 <=> sK0 = sK4),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 6.53/1.22  fof(f5412,plain,(
% 6.53/1.22    ~spl10_57 | ~spl10_8 | ~spl10_9 | ~spl10_56 | spl10_68),
% 6.53/1.22    inference(avatar_split_clause,[],[f5411,f1408,f809,f113,f108,f814])).
% 6.53/1.22  fof(f814,plain,(
% 6.53/1.22    spl10_57 <=> r1_xboole_0(sK4,sK4)),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).
% 6.53/1.22  fof(f5411,plain,(
% 6.53/1.22    ~r1_xboole_0(sK4,sK4) | (~spl10_8 | ~spl10_9 | ~spl10_56 | spl10_68)),
% 6.53/1.22    inference(subsumption_resolution,[],[f5410,f235])).
% 6.53/1.22  fof(f5410,plain,(
% 6.53/1.22    ~r1_xboole_0(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2)) | ~r1_xboole_0(sK4,sK4) | (~spl10_56 | spl10_68)),
% 6.53/1.22    inference(forward_demodulation,[],[f1531,f811])).
% 6.53/1.22  fof(f1531,plain,(
% 6.53/1.22    ~r1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK6),k3_zfmisc_1(sK0,sK1,sK2)) | ~r1_xboole_0(sK4,sK4) | spl10_68),
% 6.53/1.22    inference(superposition,[],[f1410,f123])).
% 6.53/1.22  fof(f123,plain,(
% 6.53/1.22    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_xboole_0(X0,X0)) )),
% 6.53/1.22    inference(resolution,[],[f63,f119])).
% 6.53/1.22  fof(f63,plain,(
% 6.53/1.22    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 6.53/1.22    inference(cnf_transformation,[],[f29])).
% 6.53/1.22  fof(f5224,plain,(
% 6.53/1.22    k1_xboole_0 != sK4 | ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | r1_xboole_0(sK4,sK4)),
% 6.53/1.22    introduced(theory_tautology_sat_conflict,[])).
% 6.53/1.22  fof(f5008,plain,(
% 6.53/1.22    spl10_153 | spl10_58 | spl10_59 | ~spl10_69 | ~spl10_72),
% 6.53/1.22    inference(avatar_split_clause,[],[f5003,f1518,f1445,f825,f821,f5005])).
% 6.53/1.22  fof(f821,plain,(
% 6.53/1.22    spl10_58 <=> k1_xboole_0 = k2_zfmisc_1(sK4,sK5)),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).
% 6.53/1.22  fof(f825,plain,(
% 6.53/1.22    spl10_59 <=> k1_xboole_0 = sK6),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_59])])).
% 6.53/1.22  fof(f1445,plain,(
% 6.53/1.22    spl10_69 <=> k3_zfmisc_1(sK0,sK1,sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).
% 6.53/1.22  fof(f1518,plain,(
% 6.53/1.22    spl10_72 <=> k3_zfmisc_1(sK0,sK1,sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).
% 6.53/1.22  fof(f5003,plain,(
% 6.53/1.22    k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK0,sK1) | (spl10_58 | spl10_59 | ~spl10_69 | ~spl10_72)),
% 6.53/1.22    inference(trivial_inequality_removal,[],[f4988])).
% 6.53/1.22  fof(f4988,plain,(
% 6.53/1.22    k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(sK0,sK1,sK2) | k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK0,sK1) | (spl10_58 | spl10_59 | ~spl10_69 | ~spl10_72)),
% 6.53/1.22    inference(superposition,[],[f1599,f1520])).
% 6.53/1.22  fof(f1520,plain,(
% 6.53/1.22    k3_zfmisc_1(sK0,sK1,sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl10_72),
% 6.53/1.22    inference(avatar_component_clause,[],[f1518])).
% 6.53/1.22  fof(f1599,plain,(
% 6.53/1.22    ( ! [X4,X5] : (k3_zfmisc_1(sK0,sK1,sK2) != k2_zfmisc_1(X4,X5) | k2_zfmisc_1(sK4,sK5) = X4) ) | (spl10_58 | spl10_59 | ~spl10_69)),
% 6.53/1.22    inference(subsumption_resolution,[],[f1598,f822])).
% 6.53/1.22  fof(f822,plain,(
% 6.53/1.22    k1_xboole_0 != k2_zfmisc_1(sK4,sK5) | spl10_58),
% 6.53/1.22    inference(avatar_component_clause,[],[f821])).
% 6.53/1.22  fof(f1598,plain,(
% 6.53/1.22    ( ! [X4,X5] : (k3_zfmisc_1(sK0,sK1,sK2) != k2_zfmisc_1(X4,X5) | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | k2_zfmisc_1(sK4,sK5) = X4) ) | (spl10_59 | ~spl10_69)),
% 6.53/1.22    inference(subsumption_resolution,[],[f1577,f826])).
% 6.53/1.22  fof(f826,plain,(
% 6.53/1.22    k1_xboole_0 != sK6 | spl10_59),
% 6.53/1.22    inference(avatar_component_clause,[],[f825])).
% 6.53/1.22  fof(f1577,plain,(
% 6.53/1.22    ( ! [X4,X5] : (k3_zfmisc_1(sK0,sK1,sK2) != k2_zfmisc_1(X4,X5) | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | k2_zfmisc_1(sK4,sK5) = X4) ) | ~spl10_69),
% 6.53/1.22    inference(superposition,[],[f61,f1447])).
% 6.53/1.22  fof(f1447,plain,(
% 6.53/1.22    k3_zfmisc_1(sK0,sK1,sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | ~spl10_69),
% 6.53/1.22    inference(avatar_component_clause,[],[f1445])).
% 6.53/1.22  fof(f2456,plain,(
% 6.53/1.22    k1_xboole_0 != sK6 | ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | r1_xboole_0(sK6,sK6)),
% 6.53/1.22    introduced(theory_tautology_sat_conflict,[])).
% 6.53/1.22  fof(f2452,plain,(
% 6.53/1.22    spl10_3 | spl10_58 | spl10_59 | ~spl10_69 | ~spl10_72),
% 6.53/1.22    inference(avatar_split_clause,[],[f2435,f1518,f1445,f825,f821,f84])).
% 6.53/1.22  fof(f84,plain,(
% 6.53/1.22    spl10_3 <=> sK2 = sK6),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 6.53/1.22  fof(f2435,plain,(
% 6.53/1.22    sK2 = sK6 | (spl10_58 | spl10_59 | ~spl10_69 | ~spl10_72)),
% 6.53/1.22    inference(trivial_inequality_removal,[],[f2428])).
% 6.53/1.22  fof(f2428,plain,(
% 6.53/1.22    k3_zfmisc_1(sK0,sK1,sK2) != k3_zfmisc_1(sK0,sK1,sK2) | sK2 = sK6 | (spl10_58 | spl10_59 | ~spl10_69 | ~spl10_72)),
% 6.53/1.22    inference(superposition,[],[f1601,f1520])).
% 6.53/1.22  fof(f1601,plain,(
% 6.53/1.22    ( ! [X8,X9] : (k3_zfmisc_1(sK0,sK1,sK2) != k2_zfmisc_1(X8,X9) | sK6 = X9) ) | (spl10_58 | spl10_59 | ~spl10_69)),
% 6.53/1.22    inference(subsumption_resolution,[],[f1600,f822])).
% 6.53/1.22  fof(f1600,plain,(
% 6.53/1.22    ( ! [X8,X9] : (k3_zfmisc_1(sK0,sK1,sK2) != k2_zfmisc_1(X8,X9) | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | sK6 = X9) ) | (spl10_59 | ~spl10_69)),
% 6.53/1.22    inference(subsumption_resolution,[],[f1579,f826])).
% 6.53/1.22  fof(f1579,plain,(
% 6.53/1.22    ( ! [X8,X9] : (k3_zfmisc_1(sK0,sK1,sK2) != k2_zfmisc_1(X8,X9) | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | sK6 = X9) ) | ~spl10_69),
% 6.53/1.22    inference(superposition,[],[f62,f1447])).
% 6.53/1.22  fof(f1521,plain,(
% 6.53/1.22    spl10_72 | ~spl10_6 | spl10_13 | spl10_14 | ~spl10_27),
% 6.53/1.22    inference(avatar_split_clause,[],[f1509,f333,f169,f165,f98,f1518])).
% 6.53/1.22  fof(f98,plain,(
% 6.53/1.22    spl10_6 <=> k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 6.53/1.22  fof(f165,plain,(
% 6.53/1.22    spl10_13 <=> k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6)),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 6.53/1.22  fof(f169,plain,(
% 6.53/1.22    spl10_14 <=> k1_xboole_0 = sK7),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 6.53/1.22  fof(f333,plain,(
% 6.53/1.22    spl10_27 <=> k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6)),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 6.53/1.22  fof(f1509,plain,(
% 6.53/1.22    k3_zfmisc_1(sK0,sK1,sK2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (~spl10_6 | spl10_13 | spl10_14 | ~spl10_27)),
% 6.53/1.22    inference(equality_resolution,[],[f730])).
% 6.53/1.22  fof(f730,plain,(
% 6.53/1.22    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(sK0,sK1,sK2)) ) | (~spl10_6 | spl10_13 | spl10_14 | ~spl10_27)),
% 6.53/1.22    inference(forward_demodulation,[],[f729,f335])).
% 6.53/1.22  fof(f335,plain,(
% 6.53/1.22    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6) | ~spl10_27),
% 6.53/1.22    inference(avatar_component_clause,[],[f333])).
% 6.53/1.22  fof(f729,plain,(
% 6.53/1.22    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(sK4,sK5,sK6)) ) | (~spl10_6 | spl10_13 | spl10_14)),
% 6.53/1.22    inference(subsumption_resolution,[],[f728,f166])).
% 6.53/1.22  fof(f166,plain,(
% 6.53/1.22    k1_xboole_0 != k3_zfmisc_1(sK4,sK5,sK6) | spl10_13),
% 6.53/1.22    inference(avatar_component_clause,[],[f165])).
% 6.53/1.22  fof(f728,plain,(
% 6.53/1.22    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) | k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(sK4,sK5,sK6)) ) | (~spl10_6 | spl10_14)),
% 6.53/1.22    inference(subsumption_resolution,[],[f713,f170])).
% 6.53/1.22  fof(f170,plain,(
% 6.53/1.22    k1_xboole_0 != sK7 | spl10_14),
% 6.53/1.22    inference(avatar_component_clause,[],[f169])).
% 6.53/1.22  fof(f713,plain,(
% 6.53/1.22    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) | k1_xboole_0 = sK7 | k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(sK4,sK5,sK6)) ) | ~spl10_6),
% 6.53/1.22    inference(superposition,[],[f162,f100])).
% 6.53/1.22  fof(f100,plain,(
% 6.53/1.22    k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7) | ~spl10_6),
% 6.53/1.22    inference(avatar_component_clause,[],[f98])).
% 6.53/1.22  fof(f162,plain,(
% 6.53/1.22    ( ! [X6,X4,X2,X7,X5,X3] : (k2_zfmisc_1(k3_zfmisc_1(X2,X3,X4),X5) != k2_zfmisc_1(X6,X7) | k1_xboole_0 = X7 | k1_xboole_0 = X6 | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4) = X6) )),
% 6.53/1.22    inference(superposition,[],[f61,f73])).
% 6.53/1.22  fof(f73,plain,(
% 6.53/1.22    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 6.53/1.22    inference(definition_unfolding,[],[f60,f58])).
% 6.53/1.22  fof(f58,plain,(
% 6.53/1.22    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 6.53/1.22    inference(cnf_transformation,[],[f14])).
% 6.53/1.22  fof(f14,axiom,(
% 6.53/1.22    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 6.53/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 6.53/1.22  fof(f60,plain,(
% 6.53/1.22    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 6.53/1.22    inference(cnf_transformation,[],[f16])).
% 6.53/1.22  fof(f16,axiom,(
% 6.53/1.22    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)),
% 6.53/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).
% 6.53/1.22  fof(f1489,plain,(
% 6.53/1.22    ~spl10_70 | spl10_50),
% 6.53/1.22    inference(avatar_split_clause,[],[f1484,f759,f1486])).
% 6.53/1.22  fof(f1486,plain,(
% 6.53/1.22    spl10_70 <=> r1_xboole_0(sK6,sK6)),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).
% 6.53/1.22  fof(f759,plain,(
% 6.53/1.22    spl10_50 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).
% 6.53/1.22  fof(f1484,plain,(
% 6.53/1.22    ~r1_xboole_0(sK6,sK6) | spl10_50),
% 6.53/1.22    inference(trivial_inequality_removal,[],[f1481])).
% 6.53/1.22  fof(f1481,plain,(
% 6.53/1.22    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(sK6,sK6) | spl10_50),
% 6.53/1.22    inference(superposition,[],[f760,f143])).
% 6.53/1.22  fof(f760,plain,(
% 6.53/1.22    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | spl10_50),
% 6.53/1.22    inference(avatar_component_clause,[],[f759])).
% 6.53/1.22  fof(f1451,plain,(
% 6.53/1.22    spl10_69 | ~spl10_63),
% 6.53/1.22    inference(avatar_split_clause,[],[f1440,f860,f1445])).
% 6.53/1.22  fof(f860,plain,(
% 6.53/1.22    spl10_63 <=> ! [X1,X0] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = X0)),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_63])])).
% 6.53/1.22  fof(f1440,plain,(
% 6.53/1.22    k3_zfmisc_1(sK0,sK1,sK2) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | ~spl10_63),
% 6.53/1.22    inference(equality_resolution,[],[f861])).
% 6.53/1.22  fof(f861,plain,(
% 6.53/1.22    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = X0) ) | ~spl10_63),
% 6.53/1.22    inference(avatar_component_clause,[],[f860])).
% 6.53/1.22  fof(f1430,plain,(
% 6.53/1.22    ~spl10_8 | ~spl10_9 | spl10_56),
% 6.53/1.22    inference(avatar_contradiction_clause,[],[f1429])).
% 6.53/1.22  fof(f1429,plain,(
% 6.53/1.22    $false | (~spl10_8 | ~spl10_9 | spl10_56)),
% 6.53/1.22    inference(subsumption_resolution,[],[f1426,f235])).
% 6.53/1.22  fof(f1426,plain,(
% 6.53/1.22    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | spl10_56),
% 6.53/1.22    inference(trivial_inequality_removal,[],[f1425])).
% 6.53/1.22  fof(f1425,plain,(
% 6.53/1.22    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | spl10_56),
% 6.53/1.22    inference(superposition,[],[f810,f123])).
% 6.53/1.22  fof(f810,plain,(
% 6.53/1.22    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK6) | spl10_56),
% 6.53/1.22    inference(avatar_component_clause,[],[f809])).
% 6.53/1.22  fof(f1422,plain,(
% 6.53/1.22    k1_xboole_0 != k2_zfmisc_1(sK4,sK5) | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK6) | ~r1_xboole_0(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2)) | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k3_zfmisc_1(sK0,sK1,sK2))),
% 6.53/1.22    introduced(theory_tautology_sat_conflict,[])).
% 6.53/1.22  fof(f1420,plain,(
% 6.53/1.22    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | ~r1_xboole_0(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2)) | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k3_zfmisc_1(sK0,sK1,sK2))),
% 6.53/1.22    introduced(theory_tautology_sat_conflict,[])).
% 6.53/1.22  fof(f1413,plain,(
% 6.53/1.22    ~spl10_68 | spl10_5 | ~spl10_6),
% 6.53/1.22    inference(avatar_split_clause,[],[f1412,f98,f93,f1408])).
% 6.53/1.22  fof(f93,plain,(
% 6.53/1.22    spl10_5 <=> k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 6.53/1.22  fof(f1412,plain,(
% 6.53/1.22    ~r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k3_zfmisc_1(sK0,sK1,sK2)) | (spl10_5 | ~spl10_6)),
% 6.53/1.22    inference(subsumption_resolution,[],[f1396,f95])).
% 6.53/1.22  fof(f95,plain,(
% 6.53/1.22    k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) | spl10_5),
% 6.53/1.22    inference(avatar_component_clause,[],[f93])).
% 6.53/1.22  fof(f1396,plain,(
% 6.53/1.22    ~r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) | ~spl10_6),
% 6.53/1.22    inference(resolution,[],[f604,f119])).
% 6.53/1.22  fof(f604,plain,(
% 6.53/1.22    ( ! [X0,X1] : (r1_xboole_0(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3),k2_zfmisc_1(X0,X1)) | ~r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),X0)) ) | ~spl10_6),
% 6.53/1.22    inference(superposition,[],[f156,f100])).
% 6.53/1.22  fof(f156,plain,(
% 6.53/1.22    ( ! [X26,X24,X23,X27,X25,X22] : (r1_xboole_0(k2_zfmisc_1(k3_zfmisc_1(X22,X23,X24),X25),k2_zfmisc_1(X26,X27)) | ~r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X22,X23),X24),X26)) )),
% 6.53/1.22    inference(superposition,[],[f63,f73])).
% 6.53/1.22  fof(f862,plain,(
% 6.53/1.22    spl10_50 | spl10_63 | ~spl10_6 | spl10_14),
% 6.53/1.22    inference(avatar_split_clause,[],[f858,f169,f98,f860,f759])).
% 6.53/1.22  fof(f858,plain,(
% 6.53/1.22    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = X0) ) | (~spl10_6 | spl10_14)),
% 6.53/1.22    inference(subsumption_resolution,[],[f840,f170])).
% 6.53/1.22  fof(f840,plain,(
% 6.53/1.22    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) | k1_xboole_0 = sK7 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = X0) ) | ~spl10_6),
% 6.53/1.22    inference(superposition,[],[f160,f100])).
% 6.53/1.22  fof(f160,plain,(
% 6.53/1.22    ( ! [X6,X4,X2,X7,X5,X3] : (k2_zfmisc_1(k3_zfmisc_1(X2,X3,X4),X5) != k2_zfmisc_1(X6,X7) | k1_xboole_0 = X5 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4) | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4) = X6) )),
% 6.53/1.22    inference(superposition,[],[f61,f73])).
% 6.53/1.22  fof(f336,plain,(
% 6.53/1.22    spl10_27 | ~spl10_15),
% 6.53/1.22    inference(avatar_split_clause,[],[f331,f173,f333])).
% 6.53/1.22  fof(f173,plain,(
% 6.53/1.22    spl10_15 <=> ! [X1,X0] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) | k3_zfmisc_1(sK4,sK5,sK6) = X0)),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 6.53/1.22  fof(f331,plain,(
% 6.53/1.22    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK4,sK5,sK6) | ~spl10_15),
% 6.53/1.22    inference(equality_resolution,[],[f174])).
% 6.53/1.22  fof(f174,plain,(
% 6.53/1.22    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) | k3_zfmisc_1(sK4,sK5,sK6) = X0) ) | ~spl10_15),
% 6.53/1.22    inference(avatar_component_clause,[],[f173])).
% 6.53/1.22  fof(f275,plain,(
% 6.53/1.22    spl10_5 | ~spl10_6 | ~spl10_8 | ~spl10_9 | ~spl10_14),
% 6.53/1.22    inference(avatar_contradiction_clause,[],[f274])).
% 6.53/1.22  fof(f274,plain,(
% 6.53/1.22    $false | (spl10_5 | ~spl10_6 | ~spl10_8 | ~spl10_9 | ~spl10_14)),
% 6.53/1.22    inference(subsumption_resolution,[],[f270,f95])).
% 6.53/1.22  fof(f270,plain,(
% 6.53/1.22    k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) | (~spl10_6 | ~spl10_8 | ~spl10_9 | ~spl10_14)),
% 6.53/1.22    inference(resolution,[],[f268,f119])).
% 6.53/1.22  fof(f268,plain,(
% 6.53/1.22    ( ! [X0,X1] : (r1_xboole_0(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3),k2_zfmisc_1(X0,X1))) ) | (~spl10_6 | ~spl10_8 | ~spl10_9 | ~spl10_14)),
% 6.53/1.22    inference(subsumption_resolution,[],[f267,f235])).
% 6.53/1.22  fof(f267,plain,(
% 6.53/1.22    ( ! [X0,X1] : (~r1_xboole_0(k1_xboole_0,X1) | r1_xboole_0(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3),k2_zfmisc_1(X0,X1))) ) | (~spl10_6 | ~spl10_14)),
% 6.53/1.22    inference(forward_demodulation,[],[f144,f171])).
% 6.53/1.22  fof(f171,plain,(
% 6.53/1.22    k1_xboole_0 = sK7 | ~spl10_14),
% 6.53/1.22    inference(avatar_component_clause,[],[f169])).
% 6.53/1.22  fof(f144,plain,(
% 6.53/1.22    ( ! [X0,X1] : (r1_xboole_0(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3),k2_zfmisc_1(X0,X1)) | ~r1_xboole_0(sK7,X1)) ) | ~spl10_6),
% 6.53/1.22    inference(superposition,[],[f64,f100])).
% 6.53/1.22  fof(f249,plain,(
% 6.53/1.22    spl10_4 | ~spl10_6 | spl10_13 | spl10_14),
% 6.53/1.22    inference(avatar_contradiction_clause,[],[f248])).
% 6.53/1.22  fof(f248,plain,(
% 6.53/1.22    $false | (spl10_4 | ~spl10_6 | spl10_13 | spl10_14)),
% 6.53/1.22    inference(unit_resulting_resolution,[],[f90,f170,f100,f166,f62])).
% 6.53/1.22  fof(f90,plain,(
% 6.53/1.22    sK3 != sK7 | spl10_4),
% 6.53/1.22    inference(avatar_component_clause,[],[f88])).
% 6.53/1.22  fof(f88,plain,(
% 6.53/1.22    spl10_4 <=> sK3 = sK7),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 6.53/1.22  fof(f243,plain,(
% 6.53/1.22    ~spl10_8 | ~spl10_9 | spl10_19),
% 6.53/1.22    inference(avatar_contradiction_clause,[],[f240])).
% 6.53/1.22  fof(f240,plain,(
% 6.53/1.22    $false | (~spl10_8 | ~spl10_9 | spl10_19)),
% 6.53/1.22    inference(subsumption_resolution,[],[f206,f235])).
% 6.53/1.22  fof(f206,plain,(
% 6.53/1.22    ~r1_xboole_0(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2)) | spl10_19),
% 6.53/1.22    inference(avatar_component_clause,[],[f204])).
% 6.53/1.22  fof(f204,plain,(
% 6.53/1.22    spl10_19 <=> r1_xboole_0(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2))),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 6.53/1.22  fof(f242,plain,(
% 6.53/1.22    ~spl10_8 | ~spl10_9 | spl10_20),
% 6.53/1.22    inference(avatar_contradiction_clause,[],[f239])).
% 6.53/1.22  fof(f239,plain,(
% 6.53/1.22    $false | (~spl10_8 | ~spl10_9 | spl10_20)),
% 6.53/1.22    inference(subsumption_resolution,[],[f211,f235])).
% 6.53/1.22  fof(f211,plain,(
% 6.53/1.22    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | spl10_20),
% 6.53/1.22    inference(avatar_component_clause,[],[f209])).
% 6.53/1.22  fof(f209,plain,(
% 6.53/1.22    spl10_20 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 6.53/1.22  fof(f207,plain,(
% 6.53/1.22    ~spl10_19 | spl10_10 | ~spl10_13),
% 6.53/1.22    inference(avatar_split_clause,[],[f200,f165,f130,f204])).
% 6.53/1.22  fof(f130,plain,(
% 6.53/1.22    spl10_10 <=> r1_xboole_0(k3_zfmisc_1(sK4,sK5,sK6),k3_zfmisc_1(sK0,sK1,sK2))),
% 6.53/1.22    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 6.53/1.22  fof(f200,plain,(
% 6.53/1.22    ~r1_xboole_0(k1_xboole_0,k3_zfmisc_1(sK0,sK1,sK2)) | (spl10_10 | ~spl10_13)),
% 6.53/1.22    inference(superposition,[],[f132,f167])).
% 6.53/1.22  fof(f167,plain,(
% 6.53/1.22    k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6) | ~spl10_13),
% 6.53/1.22    inference(avatar_component_clause,[],[f165])).
% 6.53/1.22  fof(f132,plain,(
% 6.53/1.22    ~r1_xboole_0(k3_zfmisc_1(sK4,sK5,sK6),k3_zfmisc_1(sK0,sK1,sK2)) | spl10_10),
% 6.53/1.22    inference(avatar_component_clause,[],[f130])).
% 6.53/1.22  fof(f175,plain,(
% 6.53/1.22    spl10_13 | spl10_14 | spl10_15 | ~spl10_6),
% 6.53/1.22    inference(avatar_split_clause,[],[f159,f98,f173,f169,f165])).
% 6.53/1.22  fof(f159,plain,(
% 6.53/1.22    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) | k1_xboole_0 = sK7 | k1_xboole_0 = k3_zfmisc_1(sK4,sK5,sK6) | k3_zfmisc_1(sK4,sK5,sK6) = X0) ) | ~spl10_6),
% 6.53/1.22    inference(superposition,[],[f61,f100])).
% 6.53/1.22  fof(f133,plain,(
% 6.53/1.22    ~spl10_10 | spl10_5 | ~spl10_6),
% 6.53/1.22    inference(avatar_split_clause,[],[f128,f98,f93,f130])).
% 6.53/1.22  fof(f128,plain,(
% 6.53/1.22    ~r1_xboole_0(k3_zfmisc_1(sK4,sK5,sK6),k3_zfmisc_1(sK0,sK1,sK2)) | (spl10_5 | ~spl10_6)),
% 6.53/1.22    inference(subsumption_resolution,[],[f126,f95])).
% 6.53/1.22  fof(f126,plain,(
% 6.53/1.22    ~r1_xboole_0(k3_zfmisc_1(sK4,sK5,sK6),k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) | ~spl10_6),
% 6.53/1.22    inference(resolution,[],[f124,f119])).
% 6.53/1.22  fof(f124,plain,(
% 6.53/1.22    ( ! [X0,X1] : (r1_xboole_0(k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3),k2_zfmisc_1(X0,X1)) | ~r1_xboole_0(k3_zfmisc_1(sK4,sK5,sK6),X0)) ) | ~spl10_6),
% 6.53/1.22    inference(superposition,[],[f63,f100])).
% 6.53/1.22  fof(f116,plain,(
% 6.53/1.22    spl10_9),
% 6.53/1.22    inference(avatar_split_clause,[],[f44,f113])).
% 6.53/1.22  fof(f44,plain,(
% 6.53/1.22    v1_relat_1(k1_xboole_0)),
% 6.53/1.22    inference(cnf_transformation,[],[f13])).
% 6.53/1.22  fof(f13,axiom,(
% 6.53/1.22    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 6.53/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
% 6.53/1.22  fof(f111,plain,(
% 6.53/1.22    spl10_8),
% 6.53/1.22    inference(avatar_split_clause,[],[f46,f108])).
% 6.53/1.22  fof(f46,plain,(
% 6.53/1.22    v1_funct_1(k1_xboole_0)),
% 6.53/1.22    inference(cnf_transformation,[],[f13])).
% 6.53/1.22  fof(f101,plain,(
% 6.53/1.22    spl10_6),
% 6.53/1.22    inference(avatar_split_clause,[],[f69,f98])).
% 6.53/1.22  fof(f69,plain,(
% 6.53/1.22    k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3) = k2_zfmisc_1(k3_zfmisc_1(sK4,sK5,sK6),sK7)),
% 6.53/1.22    inference(definition_unfolding,[],[f38,f58,f58])).
% 6.53/1.22  fof(f38,plain,(
% 6.53/1.22    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 6.53/1.22    inference(cnf_transformation,[],[f31])).
% 6.53/1.22  fof(f31,plain,(
% 6.53/1.22    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 6.53/1.22    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f22,f30])).
% 6.53/1.22  fof(f30,plain,(
% 6.53/1.22    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 6.53/1.22    introduced(choice_axiom,[])).
% 6.53/1.22  fof(f22,plain,(
% 6.53/1.22    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 6.53/1.22    inference(flattening,[],[f21])).
% 6.53/1.22  fof(f21,plain,(
% 6.53/1.22    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 6.53/1.22    inference(ennf_transformation,[],[f18])).
% 6.53/1.22  fof(f18,negated_conjecture,(
% 6.53/1.22    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 6.53/1.22    inference(negated_conjecture,[],[f17])).
% 6.53/1.22  fof(f17,conjecture,(
% 6.53/1.22    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 6.53/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).
% 6.53/1.22  fof(f96,plain,(
% 6.53/1.22    ~spl10_5),
% 6.53/1.22    inference(avatar_split_clause,[],[f68,f93])).
% 6.53/1.22  fof(f68,plain,(
% 6.53/1.22    k1_xboole_0 != k2_zfmisc_1(k3_zfmisc_1(sK0,sK1,sK2),sK3)),
% 6.53/1.22    inference(definition_unfolding,[],[f39,f58])).
% 6.53/1.22  fof(f39,plain,(
% 6.53/1.22    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)),
% 6.53/1.22    inference(cnf_transformation,[],[f31])).
% 6.53/1.22  fof(f91,plain,(
% 6.53/1.22    ~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4),
% 6.53/1.22    inference(avatar_split_clause,[],[f40,f88,f84,f80,f76])).
% 6.53/1.22  fof(f40,plain,(
% 6.53/1.22    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 6.53/1.22    inference(cnf_transformation,[],[f31])).
% 6.53/1.22  % SZS output end Proof for theBenchmark
% 6.53/1.22  % (9501)------------------------------
% 6.53/1.22  % (9501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.53/1.22  % (9501)Termination reason: Refutation
% 6.53/1.22  
% 6.53/1.22  % (9501)Memory used [KB]: 14456
% 6.53/1.22  % (9501)Time elapsed: 0.615 s
% 6.53/1.22  % (9501)------------------------------
% 6.53/1.22  % (9501)------------------------------
% 6.53/1.22  % (9412)Success in time 0.831 s
%------------------------------------------------------------------------------
