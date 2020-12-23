%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:58 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 501 expanded)
%              Number of leaves         :   25 ( 146 expanded)
%              Depth                    :   19
%              Number of atoms          :  443 (1263 expanded)
%              Number of equality atoms :   87 ( 421 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1344,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f78,f82,f176,f242,f245,f250,f941,f1214,f1343])).

fof(f1343,plain,
    ( spl1_2
    | ~ spl1_4
    | ~ spl1_12 ),
    inference(avatar_contradiction_clause,[],[f1342])).

fof(f1342,plain,
    ( $false
    | spl1_2
    | ~ spl1_4
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f1341,f34])).

fof(f34,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f1341,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_4
    | ~ spl1_12 ),
    inference(trivial_inequality_removal,[],[f1340])).

fof(f1340,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK0)
    | spl1_2
    | ~ spl1_4
    | ~ spl1_12 ),
    inference(superposition,[],[f66,f973])).

fof(f973,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_4
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f122,f940])).

fof(f940,plain,
    ( ! [X1] :
        ( v1_relat_1(k5_relat_1(X1,k1_xboole_0))
        | ~ v1_relat_1(X1) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f939])).

fof(f939,plain,
    ( spl1_12
  <=> ! [X1] :
        ( v1_relat_1(k5_relat_1(X1,k1_xboole_0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f122,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f121,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f55,f40])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f39,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f121,plain,
    ( ! [X0] :
        ( k5_relat_1(X0,k1_xboole_0) = k4_xboole_0(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f120,f40])).

fof(f120,plain,
    ( ! [X0] :
        ( k5_relat_1(X0,k1_xboole_0) = k4_xboole_0(k5_relat_1(X0,k1_xboole_0),k4_xboole_0(k5_relat_1(X0,k1_xboole_0),k1_xboole_0))
        | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_4 ),
    inference(forward_demodulation,[],[f109,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f109,plain,
    ( ! [X0] :
        ( k5_relat_1(X0,k1_xboole_0) = k4_xboole_0(k5_relat_1(X0,k1_xboole_0),k4_xboole_0(k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)))
        | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_4 ),
    inference(superposition,[],[f56,f96])).

fof(f96,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_4 ),
    inference(resolution,[],[f95,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f53,f40])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f95,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f94,f77])).

fof(f77,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl1_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f94,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f44,f37])).

fof(f37,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f56,plain,(
    ! [X0] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f43,f47])).

fof(f43,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f66,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl1_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f1214,plain,
    ( spl1_1
    | ~ spl1_4
    | ~ spl1_9
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(avatar_contradiction_clause,[],[f1213])).

fof(f1213,plain,
    ( $false
    | spl1_1
    | ~ spl1_4
    | ~ spl1_9
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f1212,f34])).

fof(f1212,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_1
    | ~ spl1_4
    | ~ spl1_9
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(trivial_inequality_removal,[],[f1139])).

fof(f1139,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK0)
    | spl1_1
    | ~ spl1_4
    | ~ spl1_9
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(superposition,[],[f62,f1099])).

fof(f1099,plain,
    ( ! [X28] :
        ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X28)
        | ~ v1_relat_1(X28) )
    | ~ spl1_4
    | ~ spl1_9
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f1098,f264])).

fof(f264,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_9
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f263,f87])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(trivial_inequality_removal,[],[f86])).

fof(f86,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X1,X1) ) ),
    inference(superposition,[],[f52,f69])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f263,plain,
    ( ~ r1_tarski(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0))
    | k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_9
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f262,f40])).

fof(f262,plain,
    ( ~ r1_tarski(k4_relat_1(k1_xboole_0),k4_xboole_0(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_9
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f261,f57])).

fof(f261,plain,
    ( ~ r1_tarski(k4_relat_1(k1_xboole_0),k4_xboole_0(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0)))
    | k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_9
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f256,f232])).

fof(f232,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl1_9
  <=> v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f256,plain,
    ( ~ r1_tarski(k4_relat_1(k1_xboole_0),k4_xboole_0(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0)))
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_11 ),
    inference(superposition,[],[f111,f252])).

fof(f252,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl1_11 ),
    inference(resolution,[],[f241,f88])).

fof(f241,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl1_11
  <=> r1_tarski(k2_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f111,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f56,f53])).

fof(f1098,plain,
    ( ! [X28] :
        ( k4_relat_1(k1_xboole_0) = k5_relat_1(k4_relat_1(k1_xboole_0),X28)
        | ~ v1_relat_1(X28) )
    | ~ spl1_4
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f1097,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f1097,plain,
    ( ! [X28] :
        ( k4_relat_1(k1_xboole_0) = k5_relat_1(k4_relat_1(k1_xboole_0),X28)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(k4_relat_1(X28)) )
    | ~ spl1_4
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f1000,f77])).

fof(f1000,plain,
    ( ! [X28] :
        ( k4_relat_1(k1_xboole_0) = k5_relat_1(k4_relat_1(k1_xboole_0),X28)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(k4_relat_1(X28)) )
    | ~ spl1_4
    | ~ spl1_12 ),
    inference(superposition,[],[f137,f973])).

fof(f137,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(k4_relat_1(X0),X1)) = k5_relat_1(k4_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f133,f41])).

fof(f133,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(k4_relat_1(X0),X1)) = k5_relat_1(k4_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f45,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f62,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl1_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f941,plain,
    ( spl1_5
    | spl1_12
    | ~ spl1_4
    | ~ spl1_9
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f937,f239,f231,f75,f939,f153])).

fof(f153,plain,
    ( spl1_5
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f937,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X1,k1_xboole_0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0)) )
    | ~ spl1_4
    | ~ spl1_9
    | ~ spl1_11 ),
    inference(duplicate_literal_removal,[],[f936])).

fof(f936,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X1,k1_xboole_0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_4
    | ~ spl1_9
    | ~ spl1_11 ),
    inference(superposition,[],[f735,f122])).

fof(f735,plain,
    ( ! [X4,X3] :
        ( v1_relat_1(k5_relat_1(X3,k5_relat_1(X4,k1_xboole_0)))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X4) )
    | ~ spl1_4
    | ~ spl1_9
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f729,f77])).

fof(f729,plain,
    ( ! [X4,X3] :
        ( v1_relat_1(k5_relat_1(X3,k5_relat_1(X4,k1_xboole_0)))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(X4) )
    | ~ spl1_9
    | ~ spl1_11 ),
    inference(superposition,[],[f421,f264])).

fof(f421,plain,(
    ! [X4,X5,X3] :
      ( v1_relat_1(k5_relat_1(X5,k5_relat_1(X4,k4_relat_1(X3))))
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f418,f413])).

fof(f413,plain,(
    ! [X10,X11] :
      ( v1_relat_1(k5_relat_1(X11,k4_relat_1(X10)))
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11) ) ),
    inference(subsumption_resolution,[],[f395,f41])).

fof(f395,plain,(
    ! [X10,X11] :
      ( v1_relat_1(k5_relat_1(X11,k4_relat_1(X10)))
      | ~ v1_relat_1(k4_relat_1(X11))
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11) ) ),
    inference(duplicate_literal_removal,[],[f387])).

fof(f387,plain,(
    ! [X10,X11] :
      ( v1_relat_1(k5_relat_1(X11,k4_relat_1(X10)))
      | ~ v1_relat_1(k4_relat_1(X11))
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11) ) ),
    inference(superposition,[],[f141,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X1,k4_relat_1(X0))) = k5_relat_1(X0,k4_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f132,f41])).

fof(f132,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X1,k4_relat_1(X0))) = k5_relat_1(X0,k4_relat_1(X1))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f45,f42])).

fof(f141,plain,(
    ! [X2,X3] :
      ( v1_relat_1(k4_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f140,f41])).

fof(f140,plain,(
    ! [X2,X3] :
      ( v1_relat_1(k4_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_relat_1(k4_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f135,f41])).

fof(f135,plain,(
    ! [X2,X3] :
      ( v1_relat_1(k4_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_relat_1(k4_relat_1(X3))
      | ~ v1_relat_1(k4_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f48,f45])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f418,plain,(
    ! [X4,X5,X3] :
      ( v1_relat_1(k5_relat_1(X5,k5_relat_1(X4,k4_relat_1(X3))))
      | ~ v1_relat_1(k5_relat_1(X3,k4_relat_1(X4)))
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f413,f136])).

fof(f250,plain,
    ( ~ spl1_4
    | ~ spl1_9
    | spl1_10 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | ~ spl1_4
    | ~ spl1_9
    | spl1_10 ),
    inference(subsumption_resolution,[],[f248,f232])).

fof(f248,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl1_4
    | spl1_10 ),
    inference(subsumption_resolution,[],[f246,f77])).

fof(f246,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | spl1_10 ),
    inference(resolution,[],[f237,f48])).

fof(f237,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | spl1_10 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl1_10
  <=> v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f245,plain,
    ( ~ spl1_4
    | spl1_9 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl1_4
    | spl1_9 ),
    inference(subsumption_resolution,[],[f243,f77])).

fof(f243,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_9 ),
    inference(resolution,[],[f233,f41])).

fof(f233,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | spl1_9 ),
    inference(avatar_component_clause,[],[f231])).

fof(f242,plain,
    ( ~ spl1_9
    | ~ spl1_10
    | spl1_11
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f229,f75,f239,f235,f231])).

fof(f229,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f226,f77])).

fof(f226,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl1_4 ),
    inference(superposition,[],[f223,f122])).

fof(f223,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),X0))),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f217,f77])).

fof(f217,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),X0))),k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f169,f37])).

fof(f169,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(X0),X1))),k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f164,f41])).

fof(f164,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(X0),X1))),k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f139,f42])).

fof(f139,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(X1,X0))),k2_relat_1(k4_relat_1(X1)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f138,f41])).

fof(f138,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(X1,X0))),k2_relat_1(k4_relat_1(X1)))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f134,f41])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(X1,X0))),k2_relat_1(k4_relat_1(X1)))
      | ~ v1_relat_1(k4_relat_1(X1))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f44,f45])).

fof(f176,plain,
    ( ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(subsumption_resolution,[],[f174,f77])).

fof(f174,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(condensation,[],[f173])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_5 ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_5 ),
    inference(resolution,[],[f154,f48])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k5_relat_1(X0,k1_xboole_0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f153])).

fof(f82,plain,(
    ~ spl1_3 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f34,f73])).

fof(f73,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl1_3
  <=> ! [X0] : ~ v1_relat_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f78,plain,
    ( spl1_3
    | spl1_4 ),
    inference(avatar_split_clause,[],[f70,f75,f72])).

fof(f70,plain,(
    ! [X0] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f46,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f67,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f35,f64,f60])).

fof(f35,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:55:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (12848)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (12872)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (12852)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (12851)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (12861)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (12856)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (12854)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (12877)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (12871)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (12849)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (12870)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (12873)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (12869)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (12863)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (12875)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (12853)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (12862)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (12855)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (12865)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (12865)Refutation not found, incomplete strategy% (12865)------------------------------
% 0.20/0.54  % (12865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (12865)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (12865)Memory used [KB]: 10618
% 0.20/0.54  % (12865)Time elapsed: 0.128 s
% 0.20/0.54  % (12865)------------------------------
% 0.20/0.54  % (12865)------------------------------
% 0.20/0.54  % (12864)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (12857)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (12874)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (12876)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (12867)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (12850)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (12868)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (12860)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (12859)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (12858)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (12870)Refutation not found, incomplete strategy% (12870)------------------------------
% 0.20/0.55  % (12870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (12870)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (12870)Memory used [KB]: 10618
% 0.20/0.55  % (12870)Time elapsed: 0.134 s
% 0.20/0.55  % (12870)------------------------------
% 0.20/0.55  % (12870)------------------------------
% 0.20/0.57  % (12866)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.87/0.62  % (12875)Refutation found. Thanks to Tanya!
% 1.87/0.62  % SZS status Theorem for theBenchmark
% 1.87/0.62  % SZS output start Proof for theBenchmark
% 1.87/0.62  fof(f1344,plain,(
% 1.87/0.62    $false),
% 1.87/0.62    inference(avatar_sat_refutation,[],[f67,f78,f82,f176,f242,f245,f250,f941,f1214,f1343])).
% 1.87/0.62  fof(f1343,plain,(
% 1.87/0.62    spl1_2 | ~spl1_4 | ~spl1_12),
% 1.87/0.62    inference(avatar_contradiction_clause,[],[f1342])).
% 1.87/0.62  fof(f1342,plain,(
% 1.87/0.62    $false | (spl1_2 | ~spl1_4 | ~spl1_12)),
% 1.87/0.62    inference(subsumption_resolution,[],[f1341,f34])).
% 1.87/0.62  fof(f34,plain,(
% 1.87/0.62    v1_relat_1(sK0)),
% 1.87/0.62    inference(cnf_transformation,[],[f30])).
% 1.87/0.62  fof(f30,plain,(
% 1.87/0.62    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.87/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f29])).
% 1.87/0.62  fof(f29,plain,(
% 1.87/0.62    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.87/0.62    introduced(choice_axiom,[])).
% 1.87/0.62  fof(f18,plain,(
% 1.87/0.62    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.87/0.62    inference(ennf_transformation,[],[f17])).
% 1.87/0.62  fof(f17,negated_conjecture,(
% 1.87/0.62    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.87/0.62    inference(negated_conjecture,[],[f16])).
% 1.87/0.62  fof(f16,conjecture,(
% 1.87/0.62    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 1.87/0.62  fof(f1341,plain,(
% 1.87/0.62    ~v1_relat_1(sK0) | (spl1_2 | ~spl1_4 | ~spl1_12)),
% 1.87/0.62    inference(trivial_inequality_removal,[],[f1340])).
% 1.87/0.62  fof(f1340,plain,(
% 1.87/0.62    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK0) | (spl1_2 | ~spl1_4 | ~spl1_12)),
% 1.87/0.62    inference(superposition,[],[f66,f973])).
% 1.87/0.62  fof(f973,plain,(
% 1.87/0.62    ( ! [X0] : (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | (~spl1_4 | ~spl1_12)),
% 1.87/0.62    inference(subsumption_resolution,[],[f122,f940])).
% 1.87/0.62  fof(f940,plain,(
% 1.87/0.62    ( ! [X1] : (v1_relat_1(k5_relat_1(X1,k1_xboole_0)) | ~v1_relat_1(X1)) ) | ~spl1_12),
% 1.87/0.62    inference(avatar_component_clause,[],[f939])).
% 1.87/0.62  fof(f939,plain,(
% 1.87/0.62    spl1_12 <=> ! [X1] : (v1_relat_1(k5_relat_1(X1,k1_xboole_0)) | ~v1_relat_1(X1))),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 1.87/0.62  fof(f122,plain,(
% 1.87/0.62    ( ! [X0] : (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) ) | ~spl1_4),
% 1.87/0.62    inference(forward_demodulation,[],[f121,f69])).
% 1.87/0.62  fof(f69,plain,(
% 1.87/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.87/0.62    inference(forward_demodulation,[],[f55,f40])).
% 1.87/0.62  fof(f40,plain,(
% 1.87/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.87/0.62    inference(cnf_transformation,[],[f3])).
% 1.87/0.62  fof(f3,axiom,(
% 1.87/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.87/0.62  fof(f55,plain,(
% 1.87/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.87/0.62    inference(definition_unfolding,[],[f39,f47])).
% 1.87/0.62  fof(f47,plain,(
% 1.87/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f4])).
% 1.87/0.62  fof(f4,axiom,(
% 1.87/0.62    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.87/0.62  fof(f39,plain,(
% 1.87/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f2])).
% 1.87/0.62  fof(f2,axiom,(
% 1.87/0.62    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.87/0.62  fof(f121,plain,(
% 1.87/0.62    ( ! [X0] : (k5_relat_1(X0,k1_xboole_0) = k4_xboole_0(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) ) | ~spl1_4),
% 1.87/0.62    inference(forward_demodulation,[],[f120,f40])).
% 1.87/0.62  fof(f120,plain,(
% 1.87/0.62    ( ! [X0] : (k5_relat_1(X0,k1_xboole_0) = k4_xboole_0(k5_relat_1(X0,k1_xboole_0),k4_xboole_0(k5_relat_1(X0,k1_xboole_0),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) ) | ~spl1_4),
% 1.87/0.62    inference(forward_demodulation,[],[f109,f57])).
% 1.87/0.62  fof(f57,plain,(
% 1.87/0.62    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.87/0.62    inference(equality_resolution,[],[f51])).
% 1.87/0.62  fof(f51,plain,(
% 1.87/0.62    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.87/0.62    inference(cnf_transformation,[],[f32])).
% 1.87/0.62  fof(f32,plain,(
% 1.87/0.62    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.87/0.62    inference(flattening,[],[f31])).
% 1.87/0.62  fof(f31,plain,(
% 1.87/0.62    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.87/0.62    inference(nnf_transformation,[],[f5])).
% 1.87/0.62  fof(f5,axiom,(
% 1.87/0.62    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.87/0.62  fof(f109,plain,(
% 1.87/0.62    ( ! [X0] : (k5_relat_1(X0,k1_xboole_0) = k4_xboole_0(k5_relat_1(X0,k1_xboole_0),k4_xboole_0(k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0))) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) ) | ~spl1_4),
% 1.87/0.62    inference(superposition,[],[f56,f96])).
% 1.87/0.62  fof(f96,plain,(
% 1.87/0.62    ( ! [X0] : (k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) ) | ~spl1_4),
% 1.87/0.62    inference(resolution,[],[f95,f88])).
% 1.87/0.62  fof(f88,plain,(
% 1.87/0.62    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.87/0.62    inference(superposition,[],[f53,f40])).
% 1.87/0.62  fof(f53,plain,(
% 1.87/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f33])).
% 1.87/0.62  fof(f33,plain,(
% 1.87/0.62    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.87/0.62    inference(nnf_transformation,[],[f1])).
% 1.87/0.62  fof(f1,axiom,(
% 1.87/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.87/0.62  fof(f95,plain,(
% 1.87/0.62    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl1_4),
% 1.87/0.62    inference(subsumption_resolution,[],[f94,f77])).
% 1.87/0.62  fof(f77,plain,(
% 1.87/0.62    v1_relat_1(k1_xboole_0) | ~spl1_4),
% 1.87/0.62    inference(avatar_component_clause,[],[f75])).
% 1.87/0.62  fof(f75,plain,(
% 1.87/0.62    spl1_4 <=> v1_relat_1(k1_xboole_0)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 1.87/0.62  fof(f94,plain,(
% 1.87/0.62    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(superposition,[],[f44,f37])).
% 1.87/0.62  fof(f37,plain,(
% 1.87/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.87/0.62    inference(cnf_transformation,[],[f15])).
% 1.87/0.62  fof(f15,axiom,(
% 1.87/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.87/0.62  fof(f44,plain,(
% 1.87/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f22])).
% 1.87/0.62  fof(f22,plain,(
% 1.87/0.62    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.87/0.62    inference(ennf_transformation,[],[f13])).
% 1.87/0.62  fof(f13,axiom,(
% 1.87/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.87/0.62  fof(f56,plain,(
% 1.87/0.62    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(definition_unfolding,[],[f43,f47])).
% 1.87/0.62  fof(f43,plain,(
% 1.87/0.62    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f21])).
% 1.87/0.62  fof(f21,plain,(
% 1.87/0.62    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.87/0.62    inference(ennf_transformation,[],[f12])).
% 1.87/0.62  fof(f12,axiom,(
% 1.87/0.62    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 1.87/0.62  fof(f66,plain,(
% 1.87/0.62    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl1_2),
% 1.87/0.62    inference(avatar_component_clause,[],[f64])).
% 1.87/0.62  fof(f64,plain,(
% 1.87/0.62    spl1_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 1.87/0.62  fof(f1214,plain,(
% 1.87/0.62    spl1_1 | ~spl1_4 | ~spl1_9 | ~spl1_11 | ~spl1_12),
% 1.87/0.62    inference(avatar_contradiction_clause,[],[f1213])).
% 1.87/0.62  fof(f1213,plain,(
% 1.87/0.62    $false | (spl1_1 | ~spl1_4 | ~spl1_9 | ~spl1_11 | ~spl1_12)),
% 1.87/0.62    inference(subsumption_resolution,[],[f1212,f34])).
% 1.87/0.62  fof(f1212,plain,(
% 1.87/0.62    ~v1_relat_1(sK0) | (spl1_1 | ~spl1_4 | ~spl1_9 | ~spl1_11 | ~spl1_12)),
% 1.87/0.62    inference(trivial_inequality_removal,[],[f1139])).
% 1.87/0.62  fof(f1139,plain,(
% 1.87/0.62    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK0) | (spl1_1 | ~spl1_4 | ~spl1_9 | ~spl1_11 | ~spl1_12)),
% 1.87/0.62    inference(superposition,[],[f62,f1099])).
% 1.87/0.62  fof(f1099,plain,(
% 1.87/0.62    ( ! [X28] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X28) | ~v1_relat_1(X28)) ) | (~spl1_4 | ~spl1_9 | ~spl1_11 | ~spl1_12)),
% 1.87/0.62    inference(forward_demodulation,[],[f1098,f264])).
% 1.87/0.62  fof(f264,plain,(
% 1.87/0.62    k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl1_9 | ~spl1_11)),
% 1.87/0.62    inference(subsumption_resolution,[],[f263,f87])).
% 1.87/0.62  fof(f87,plain,(
% 1.87/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.87/0.62    inference(trivial_inequality_removal,[],[f86])).
% 1.87/0.62  fof(f86,plain,(
% 1.87/0.62    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X1,X1)) )),
% 1.87/0.62    inference(superposition,[],[f52,f69])).
% 1.87/0.62  fof(f52,plain,(
% 1.87/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f33])).
% 1.87/0.62  fof(f263,plain,(
% 1.87/0.62    ~r1_tarski(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0)) | k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl1_9 | ~spl1_11)),
% 1.87/0.62    inference(forward_demodulation,[],[f262,f40])).
% 1.87/0.62  fof(f262,plain,(
% 1.87/0.62    ~r1_tarski(k4_relat_1(k1_xboole_0),k4_xboole_0(k4_relat_1(k1_xboole_0),k1_xboole_0)) | k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl1_9 | ~spl1_11)),
% 1.87/0.62    inference(forward_demodulation,[],[f261,f57])).
% 1.87/0.62  fof(f261,plain,(
% 1.87/0.62    ~r1_tarski(k4_relat_1(k1_xboole_0),k4_xboole_0(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0))) | k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl1_9 | ~spl1_11)),
% 1.87/0.62    inference(subsumption_resolution,[],[f256,f232])).
% 1.87/0.62  fof(f232,plain,(
% 1.87/0.62    v1_relat_1(k4_relat_1(k1_xboole_0)) | ~spl1_9),
% 1.87/0.62    inference(avatar_component_clause,[],[f231])).
% 1.87/0.62  fof(f231,plain,(
% 1.87/0.62    spl1_9 <=> v1_relat_1(k4_relat_1(k1_xboole_0))),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 1.87/0.62  fof(f256,plain,(
% 1.87/0.62    ~r1_tarski(k4_relat_1(k1_xboole_0),k4_xboole_0(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0))) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl1_11),
% 1.87/0.62    inference(superposition,[],[f111,f252])).
% 1.87/0.62  fof(f252,plain,(
% 1.87/0.62    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0)) | ~spl1_11),
% 1.87/0.62    inference(resolution,[],[f241,f88])).
% 1.87/0.62  fof(f241,plain,(
% 1.87/0.62    r1_tarski(k2_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0) | ~spl1_11),
% 1.87/0.62    inference(avatar_component_clause,[],[f239])).
% 1.87/0.62  fof(f239,plain,(
% 1.87/0.62    spl1_11 <=> r1_tarski(k2_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 1.87/0.62  fof(f111,plain,(
% 1.87/0.62    ( ! [X1] : (~r1_tarski(X1,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) | ~v1_relat_1(X1) | k1_xboole_0 = X1) )),
% 1.87/0.62    inference(superposition,[],[f56,f53])).
% 1.87/0.62  fof(f1098,plain,(
% 1.87/0.62    ( ! [X28] : (k4_relat_1(k1_xboole_0) = k5_relat_1(k4_relat_1(k1_xboole_0),X28) | ~v1_relat_1(X28)) ) | (~spl1_4 | ~spl1_12)),
% 1.87/0.62    inference(subsumption_resolution,[],[f1097,f41])).
% 1.87/0.62  fof(f41,plain,(
% 1.87/0.62    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f19])).
% 1.87/0.62  fof(f19,plain,(
% 1.87/0.62    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.87/0.62    inference(ennf_transformation,[],[f9])).
% 1.87/0.62  fof(f9,axiom,(
% 1.87/0.62    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.87/0.62  fof(f1097,plain,(
% 1.87/0.62    ( ! [X28] : (k4_relat_1(k1_xboole_0) = k5_relat_1(k4_relat_1(k1_xboole_0),X28) | ~v1_relat_1(X28) | ~v1_relat_1(k4_relat_1(X28))) ) | (~spl1_4 | ~spl1_12)),
% 1.87/0.62    inference(subsumption_resolution,[],[f1000,f77])).
% 1.87/0.62  fof(f1000,plain,(
% 1.87/0.62    ( ! [X28] : (k4_relat_1(k1_xboole_0) = k5_relat_1(k4_relat_1(k1_xboole_0),X28) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X28) | ~v1_relat_1(k4_relat_1(X28))) ) | (~spl1_4 | ~spl1_12)),
% 1.87/0.62    inference(superposition,[],[f137,f973])).
% 1.87/0.62  fof(f137,plain,(
% 1.87/0.62    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k4_relat_1(X0),X1)) = k5_relat_1(k4_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f133,f41])).
% 1.87/0.62  fof(f133,plain,(
% 1.87/0.62    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k4_relat_1(X0),X1)) = k5_relat_1(k4_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(superposition,[],[f45,f42])).
% 1.87/0.62  fof(f42,plain,(
% 1.87/0.62    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f20])).
% 1.87/0.62  fof(f20,plain,(
% 1.87/0.62    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.87/0.62    inference(ennf_transformation,[],[f11])).
% 1.87/0.62  fof(f11,axiom,(
% 1.87/0.62    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 1.87/0.62  fof(f45,plain,(
% 1.87/0.62    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f23])).
% 1.87/0.62  fof(f23,plain,(
% 1.87/0.62    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.87/0.62    inference(ennf_transformation,[],[f14])).
% 1.87/0.62  fof(f14,axiom,(
% 1.87/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 1.87/0.62  fof(f62,plain,(
% 1.87/0.62    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_1),
% 1.87/0.62    inference(avatar_component_clause,[],[f60])).
% 1.87/0.62  fof(f60,plain,(
% 1.87/0.62    spl1_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.87/0.62  fof(f941,plain,(
% 1.87/0.62    spl1_5 | spl1_12 | ~spl1_4 | ~spl1_9 | ~spl1_11),
% 1.87/0.62    inference(avatar_split_clause,[],[f937,f239,f231,f75,f939,f153])).
% 1.87/0.62  fof(f153,plain,(
% 1.87/0.62    spl1_5 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0)))),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 1.87/0.62  fof(f937,plain,(
% 1.87/0.62    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X1,k1_xboole_0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0))) ) | (~spl1_4 | ~spl1_9 | ~spl1_11)),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f936])).
% 1.87/0.62  fof(f936,plain,(
% 1.87/0.62    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X1,k1_xboole_0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~v1_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) ) | (~spl1_4 | ~spl1_9 | ~spl1_11)),
% 1.87/0.62    inference(superposition,[],[f735,f122])).
% 1.87/0.62  fof(f735,plain,(
% 1.87/0.62    ( ! [X4,X3] : (v1_relat_1(k5_relat_1(X3,k5_relat_1(X4,k1_xboole_0))) | ~v1_relat_1(X3) | ~v1_relat_1(X4)) ) | (~spl1_4 | ~spl1_9 | ~spl1_11)),
% 1.87/0.62    inference(subsumption_resolution,[],[f729,f77])).
% 1.87/0.62  fof(f729,plain,(
% 1.87/0.62    ( ! [X4,X3] : (v1_relat_1(k5_relat_1(X3,k5_relat_1(X4,k1_xboole_0))) | ~v1_relat_1(X3) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X4)) ) | (~spl1_9 | ~spl1_11)),
% 1.87/0.62    inference(superposition,[],[f421,f264])).
% 1.87/0.62  fof(f421,plain,(
% 1.87/0.62    ( ! [X4,X5,X3] : (v1_relat_1(k5_relat_1(X5,k5_relat_1(X4,k4_relat_1(X3)))) | ~v1_relat_1(X5) | ~v1_relat_1(X3) | ~v1_relat_1(X4)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f418,f413])).
% 1.87/0.62  fof(f413,plain,(
% 1.87/0.62    ( ! [X10,X11] : (v1_relat_1(k5_relat_1(X11,k4_relat_1(X10))) | ~v1_relat_1(X10) | ~v1_relat_1(X11)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f395,f41])).
% 1.87/0.62  fof(f395,plain,(
% 1.87/0.62    ( ! [X10,X11] : (v1_relat_1(k5_relat_1(X11,k4_relat_1(X10))) | ~v1_relat_1(k4_relat_1(X11)) | ~v1_relat_1(X10) | ~v1_relat_1(X11)) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f387])).
% 1.87/0.62  fof(f387,plain,(
% 1.87/0.62    ( ! [X10,X11] : (v1_relat_1(k5_relat_1(X11,k4_relat_1(X10))) | ~v1_relat_1(k4_relat_1(X11)) | ~v1_relat_1(X10) | ~v1_relat_1(X10) | ~v1_relat_1(X11)) )),
% 1.87/0.62    inference(superposition,[],[f141,f136])).
% 1.87/0.62  fof(f136,plain,(
% 1.87/0.62    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X1,k4_relat_1(X0))) = k5_relat_1(X0,k4_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f132,f41])).
% 1.87/0.62  fof(f132,plain,(
% 1.87/0.62    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X1,k4_relat_1(X0))) = k5_relat_1(X0,k4_relat_1(X1)) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(superposition,[],[f45,f42])).
% 1.87/0.62  fof(f141,plain,(
% 1.87/0.62    ( ! [X2,X3] : (v1_relat_1(k4_relat_1(k5_relat_1(X3,X2))) | ~v1_relat_1(X2) | ~v1_relat_1(X3)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f140,f41])).
% 1.87/0.62  fof(f140,plain,(
% 1.87/0.62    ( ! [X2,X3] : (v1_relat_1(k4_relat_1(k5_relat_1(X3,X2))) | ~v1_relat_1(k4_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X3)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f135,f41])).
% 1.87/0.62  fof(f135,plain,(
% 1.87/0.62    ( ! [X2,X3] : (v1_relat_1(k4_relat_1(k5_relat_1(X3,X2))) | ~v1_relat_1(k4_relat_1(X3)) | ~v1_relat_1(k4_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X3)) )),
% 1.87/0.62    inference(superposition,[],[f48,f45])).
% 1.87/0.62  fof(f48,plain,(
% 1.87/0.62    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f26])).
% 1.87/0.62  fof(f26,plain,(
% 1.87/0.62    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.87/0.62    inference(flattening,[],[f25])).
% 1.87/0.62  fof(f25,plain,(
% 1.87/0.62    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.87/0.62    inference(ennf_transformation,[],[f10])).
% 1.87/0.62  fof(f10,axiom,(
% 1.87/0.62    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.87/0.62  fof(f418,plain,(
% 1.87/0.62    ( ! [X4,X5,X3] : (v1_relat_1(k5_relat_1(X5,k5_relat_1(X4,k4_relat_1(X3)))) | ~v1_relat_1(k5_relat_1(X3,k4_relat_1(X4))) | ~v1_relat_1(X5) | ~v1_relat_1(X3) | ~v1_relat_1(X4)) )),
% 1.87/0.62    inference(superposition,[],[f413,f136])).
% 1.87/0.62  fof(f250,plain,(
% 1.87/0.62    ~spl1_4 | ~spl1_9 | spl1_10),
% 1.87/0.62    inference(avatar_contradiction_clause,[],[f249])).
% 2.01/0.62  fof(f249,plain,(
% 2.01/0.62    $false | (~spl1_4 | ~spl1_9 | spl1_10)),
% 2.01/0.62    inference(subsumption_resolution,[],[f248,f232])).
% 2.01/0.62  fof(f248,plain,(
% 2.01/0.62    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | (~spl1_4 | spl1_10)),
% 2.01/0.62    inference(subsumption_resolution,[],[f246,f77])).
% 2.01/0.62  fof(f246,plain,(
% 2.01/0.62    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | spl1_10),
% 2.01/0.62    inference(resolution,[],[f237,f48])).
% 2.01/0.62  fof(f237,plain,(
% 2.01/0.62    ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | spl1_10),
% 2.01/0.62    inference(avatar_component_clause,[],[f235])).
% 2.01/0.62  fof(f235,plain,(
% 2.01/0.62    spl1_10 <=> v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))),
% 2.01/0.62    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 2.01/0.62  fof(f245,plain,(
% 2.01/0.62    ~spl1_4 | spl1_9),
% 2.01/0.62    inference(avatar_contradiction_clause,[],[f244])).
% 2.01/0.62  fof(f244,plain,(
% 2.01/0.62    $false | (~spl1_4 | spl1_9)),
% 2.01/0.62    inference(subsumption_resolution,[],[f243,f77])).
% 2.01/0.62  fof(f243,plain,(
% 2.01/0.62    ~v1_relat_1(k1_xboole_0) | spl1_9),
% 2.01/0.62    inference(resolution,[],[f233,f41])).
% 2.01/0.62  fof(f233,plain,(
% 2.01/0.62    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | spl1_9),
% 2.01/0.62    inference(avatar_component_clause,[],[f231])).
% 2.01/0.62  fof(f242,plain,(
% 2.01/0.62    ~spl1_9 | ~spl1_10 | spl1_11 | ~spl1_4),
% 2.01/0.62    inference(avatar_split_clause,[],[f229,f75,f239,f235,f231])).
% 2.01/0.62  fof(f229,plain,(
% 2.01/0.62    r1_tarski(k2_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~spl1_4),
% 2.01/0.62    inference(subsumption_resolution,[],[f226,f77])).
% 2.01/0.62  fof(f226,plain,(
% 2.01/0.62    r1_tarski(k2_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~spl1_4),
% 2.01/0.62    inference(superposition,[],[f223,f122])).
% 2.01/0.62  fof(f223,plain,(
% 2.01/0.62    ( ! [X0] : (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),X0))),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl1_4),
% 2.01/0.62    inference(subsumption_resolution,[],[f217,f77])).
% 2.01/0.62  fof(f217,plain,(
% 2.01/0.62    ( ! [X0] : (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),X0))),k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 2.01/0.62    inference(superposition,[],[f169,f37])).
% 2.01/0.62  fof(f169,plain,(
% 2.01/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(X0),X1))),k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.01/0.62    inference(subsumption_resolution,[],[f164,f41])).
% 2.01/0.62  fof(f164,plain,(
% 2.01/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k4_relat_1(X0),X1))),k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.01/0.62    inference(superposition,[],[f139,f42])).
% 2.01/0.62  fof(f139,plain,(
% 2.01/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(X1,X0))),k2_relat_1(k4_relat_1(X1))) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 2.01/0.62    inference(subsumption_resolution,[],[f138,f41])).
% 2.01/0.62  fof(f138,plain,(
% 2.01/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(X1,X0))),k2_relat_1(k4_relat_1(X1))) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 2.01/0.62    inference(subsumption_resolution,[],[f134,f41])).
% 2.01/0.62  fof(f134,plain,(
% 2.01/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(X1,X0))),k2_relat_1(k4_relat_1(X1))) | ~v1_relat_1(k4_relat_1(X1)) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 2.01/0.62    inference(superposition,[],[f44,f45])).
% 2.01/0.62  fof(f176,plain,(
% 2.01/0.62    ~spl1_4 | ~spl1_5),
% 2.01/0.62    inference(avatar_contradiction_clause,[],[f175])).
% 2.01/0.62  fof(f175,plain,(
% 2.01/0.62    $false | (~spl1_4 | ~spl1_5)),
% 2.01/0.62    inference(subsumption_resolution,[],[f174,f77])).
% 2.01/0.62  fof(f174,plain,(
% 2.01/0.62    ~v1_relat_1(k1_xboole_0) | ~spl1_5),
% 2.01/0.62    inference(condensation,[],[f173])).
% 2.01/0.62  fof(f173,plain,(
% 2.01/0.62    ( ! [X0] : (~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl1_5),
% 2.01/0.62    inference(duplicate_literal_removal,[],[f170])).
% 2.01/0.62  fof(f170,plain,(
% 2.01/0.62    ( ! [X0] : (~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl1_5),
% 2.01/0.62    inference(resolution,[],[f154,f48])).
% 2.01/0.62  fof(f154,plain,(
% 2.01/0.62    ( ! [X0] : (~v1_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) ) | ~spl1_5),
% 2.01/0.62    inference(avatar_component_clause,[],[f153])).
% 2.01/0.62  fof(f82,plain,(
% 2.01/0.62    ~spl1_3),
% 2.01/0.62    inference(avatar_contradiction_clause,[],[f79])).
% 2.01/0.62  fof(f79,plain,(
% 2.01/0.62    $false | ~spl1_3),
% 2.01/0.62    inference(subsumption_resolution,[],[f34,f73])).
% 2.01/0.62  fof(f73,plain,(
% 2.01/0.62    ( ! [X0] : (~v1_relat_1(X0)) ) | ~spl1_3),
% 2.01/0.62    inference(avatar_component_clause,[],[f72])).
% 2.01/0.62  fof(f72,plain,(
% 2.01/0.62    spl1_3 <=> ! [X0] : ~v1_relat_1(X0)),
% 2.01/0.62    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 2.01/0.62  fof(f78,plain,(
% 2.01/0.62    spl1_3 | spl1_4),
% 2.01/0.62    inference(avatar_split_clause,[],[f70,f75,f72])).
% 2.01/0.62  fof(f70,plain,(
% 2.01/0.62    ( ! [X0] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 2.01/0.62    inference(resolution,[],[f46,f38])).
% 2.01/0.62  fof(f38,plain,(
% 2.01/0.62    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.01/0.62    inference(cnf_transformation,[],[f6])).
% 2.01/0.62  fof(f6,axiom,(
% 2.01/0.62    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.01/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.01/0.62  fof(f46,plain,(
% 2.01/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.01/0.62    inference(cnf_transformation,[],[f24])).
% 2.01/0.62  fof(f24,plain,(
% 2.01/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.01/0.62    inference(ennf_transformation,[],[f8])).
% 2.01/0.62  fof(f8,axiom,(
% 2.01/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.01/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.01/0.62  fof(f67,plain,(
% 2.01/0.62    ~spl1_1 | ~spl1_2),
% 2.01/0.62    inference(avatar_split_clause,[],[f35,f64,f60])).
% 2.01/0.62  fof(f35,plain,(
% 2.01/0.62    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 2.01/0.62    inference(cnf_transformation,[],[f30])).
% 2.01/0.62  % SZS output end Proof for theBenchmark
% 2.01/0.62  % (12875)------------------------------
% 2.01/0.62  % (12875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.62  % (12875)Termination reason: Refutation
% 2.01/0.62  
% 2.01/0.62  % (12875)Memory used [KB]: 6908
% 2.01/0.62  % (12875)Time elapsed: 0.215 s
% 2.01/0.62  % (12875)------------------------------
% 2.01/0.62  % (12875)------------------------------
% 2.01/0.63  % (12847)Success in time 0.263 s
%------------------------------------------------------------------------------
