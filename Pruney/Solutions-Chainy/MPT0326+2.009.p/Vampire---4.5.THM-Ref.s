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
% DateTime   : Thu Dec  3 12:42:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 141 expanded)
%              Number of leaves         :   17 (  46 expanded)
%              Depth                    :   16
%              Number of atoms          :  219 ( 455 expanded)
%              Number of equality atoms :   64 ( 123 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f671,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f99,f103,f496,f603,f667])).

fof(f667,plain,
    ( ~ spl6_1
    | spl6_39 ),
    inference(avatar_contradiction_clause,[],[f666])).

fof(f666,plain,
    ( $false
    | ~ spl6_1
    | spl6_39 ),
    inference(subsumption_resolution,[],[f665,f578])).

fof(f578,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl6_39 ),
    inference(avatar_component_clause,[],[f577])).

fof(f577,plain,
    ( spl6_39
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f665,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f638,f29])).

fof(f29,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(sK1,sK3)
    & ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
      | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) )
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ~ r1_tarski(X1,X3)
            & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X3,X2,X1] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3,X2,X1] :
        ( ~ r1_tarski(X1,X3)
        & ( r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2))
          | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)) ) )
   => ( ~ r1_tarski(sK1,sK3)
      & ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
        | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1,X2,X3] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
           => r1_tarski(X1,X3) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f638,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_1 ),
    inference(resolution,[],[f31,f46])).

fof(f46,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl6_1
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,X3)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f603,plain,
    ( spl6_8
    | spl6_9
    | ~ spl6_39 ),
    inference(avatar_contradiction_clause,[],[f602])).

fof(f602,plain,
    ( $false
    | spl6_8
    | spl6_9
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f601,f97])).

fof(f97,plain,
    ( k1_xboole_0 != sK0
    | spl6_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_9
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f601,plain,
    ( k1_xboole_0 = sK0
    | spl6_8
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f600,f93])).

fof(f93,plain,
    ( k1_xboole_0 != sK1
    | spl6_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl6_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

% (31750)Refutation not found, incomplete strategy% (31750)------------------------------
% (31750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31750)Termination reason: Refutation not found, incomplete strategy

% (31750)Memory used [KB]: 6140
% (31750)Time elapsed: 0.083 s
% (31750)------------------------------
% (31750)------------------------------
fof(f600,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_39 ),
    inference(trivial_inequality_removal,[],[f599])).

fof(f599,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl6_39 ),
    inference(superposition,[],[f34,f579])).

fof(f579,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f577])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f496,plain,(
    ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f495])).

fof(f495,plain,
    ( $false
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f454,f33])).

% (31751)Refutation not found, incomplete strategy% (31751)------------------------------
% (31751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31751)Termination reason: Refutation not found, incomplete strategy

% (31751)Memory used [KB]: 10618
% (31751)Time elapsed: 0.081 s
% (31751)------------------------------
% (31751)------------------------------
fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f454,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f29,f430])).

fof(f430,plain,
    ( ! [X8] : k1_xboole_0 = X8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f425,f42])).

fof(f42,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f425,plain,
    ( ! [X8] :
        ( k1_xboole_0 = X8
        | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X8) )
    | ~ spl6_9 ),
    inference(resolution,[],[f373,f33])).

fof(f373,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X1
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
    | ~ spl6_9 ),
    inference(superposition,[],[f369,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f369,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(X0,k1_xboole_0),X1)
        | k1_xboole_0 = X1 )
    | ~ spl6_9 ),
    inference(resolution,[],[f285,f38])).

fof(f38,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f285,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(X1,X2),X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_9 ),
    inference(resolution,[],[f119,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
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

fof(f119,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0),X0)
        | k1_xboole_0 = X1
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
    | ~ spl6_9 ),
    inference(superposition,[],[f114,f34])).

fof(f114,plain,
    ( r2_hidden(sK4(k1_xboole_0),k1_xboole_0)
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f52,f98])).

fof(f98,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f52,plain,(
    r2_hidden(sK4(sK0),sK0) ),
    inference(resolution,[],[f27,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f27,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f103,plain,(
    ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f101,f33])).

fof(f101,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f29,f94])).

fof(f94,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f99,plain,
    ( spl6_8
    | spl6_9
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f90,f48,f96,f92])).

fof(f48,plain,
    ( spl6_2
  <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f90,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(superposition,[],[f34,f62])).

fof(f62,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f55,f29])).

fof(f55,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f50,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X0,X2)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f51,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f28,f48,f44])).

fof(f28,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:14:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (31753)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.46  % (31755)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (31770)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.48  % (31763)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (31763)Refutation not found, incomplete strategy% (31763)------------------------------
% 0.22/0.48  % (31763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (31763)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (31763)Memory used [KB]: 6012
% 0.22/0.48  % (31763)Time elapsed: 0.059 s
% 0.22/0.48  % (31763)------------------------------
% 0.22/0.48  % (31763)------------------------------
% 0.22/0.48  % (31765)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (31754)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (31752)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (31750)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (31751)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (31770)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f671,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f51,f99,f103,f496,f603,f667])).
% 0.22/0.50  fof(f667,plain,(
% 0.22/0.50    ~spl6_1 | spl6_39),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f666])).
% 0.22/0.50  fof(f666,plain,(
% 0.22/0.50    $false | (~spl6_1 | spl6_39)),
% 0.22/0.50    inference(subsumption_resolution,[],[f665,f578])).
% 0.22/0.50  fof(f578,plain,(
% 0.22/0.50    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl6_39),
% 0.22/0.50    inference(avatar_component_clause,[],[f577])).
% 0.22/0.50  fof(f577,plain,(
% 0.22/0.50    spl6_39 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.22/0.50  fof(f665,plain,(
% 0.22/0.50    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_1),
% 0.22/0.50    inference(subsumption_resolution,[],[f638,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ~r1_tarski(sK1,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    (~r1_tarski(sK1,sK3) & (r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))) & ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f19,f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0)) => (? [X3,X2,X1] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ? [X3,X2,X1] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,sK0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(X2,X3)))) => (~r1_tarski(sK1,sK3) & (r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.22/0.50    inference(negated_conjecture,[],[f8])).
% 0.22/0.50  fof(f8,conjecture,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).
% 0.22/0.50  fof(f638,plain,(
% 0.22/0.50    r1_tarski(sK1,sK3) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_1),
% 0.22/0.50    inference(resolution,[],[f31,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl6_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    spl6_1 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (r1_tarski(X1,X3) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.22/0.50    inference(flattening,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.22/0.50  fof(f603,plain,(
% 0.22/0.50    spl6_8 | spl6_9 | ~spl6_39),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f602])).
% 0.22/0.50  fof(f602,plain,(
% 0.22/0.50    $false | (spl6_8 | spl6_9 | ~spl6_39)),
% 0.22/0.50    inference(subsumption_resolution,[],[f601,f97])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    k1_xboole_0 != sK0 | spl6_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f96])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    spl6_9 <=> k1_xboole_0 = sK0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.50  fof(f601,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | (spl6_8 | ~spl6_39)),
% 0.22/0.50    inference(subsumption_resolution,[],[f600,f93])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    k1_xboole_0 != sK1 | spl6_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f92])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    spl6_8 <=> k1_xboole_0 = sK1),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.50  % (31750)Refutation not found, incomplete strategy% (31750)------------------------------
% 0.22/0.50  % (31750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (31750)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (31750)Memory used [KB]: 6140
% 0.22/0.50  % (31750)Time elapsed: 0.083 s
% 0.22/0.50  % (31750)------------------------------
% 0.22/0.50  % (31750)------------------------------
% 0.22/0.50  fof(f600,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_39),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f599])).
% 0.22/0.50  fof(f599,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl6_39),
% 0.22/0.50    inference(superposition,[],[f34,f579])).
% 0.22/0.50  fof(f579,plain,(
% 0.22/0.50    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_39),
% 0.22/0.50    inference(avatar_component_clause,[],[f577])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.50  fof(f496,plain,(
% 0.22/0.50    ~spl6_9),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f495])).
% 0.22/0.50  fof(f495,plain,(
% 0.22/0.50    $false | ~spl6_9),
% 0.22/0.50    inference(subsumption_resolution,[],[f454,f33])).
% 0.22/0.50  % (31751)Refutation not found, incomplete strategy% (31751)------------------------------
% 0.22/0.50  % (31751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (31751)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (31751)Memory used [KB]: 10618
% 0.22/0.50  % (31751)Time elapsed: 0.081 s
% 0.22/0.50  % (31751)------------------------------
% 0.22/0.50  % (31751)------------------------------
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.50  fof(f454,plain,(
% 0.22/0.50    ~r1_tarski(k1_xboole_0,sK3) | ~spl6_9),
% 0.22/0.50    inference(backward_demodulation,[],[f29,f430])).
% 0.22/0.50  fof(f430,plain,(
% 0.22/0.50    ( ! [X8] : (k1_xboole_0 = X8) ) | ~spl6_9),
% 0.22/0.50    inference(subsumption_resolution,[],[f425,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f425,plain,(
% 0.22/0.50    ( ! [X8] : (k1_xboole_0 = X8 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X8)) ) | ~spl6_9),
% 0.22/0.50    inference(resolution,[],[f373,f33])).
% 0.22/0.50  fof(f373,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X1 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) ) | ~spl6_9),
% 0.22/0.50    inference(superposition,[],[f369,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.50  fof(f369,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(X0,k1_xboole_0),X1) | k1_xboole_0 = X1) ) | ~spl6_9),
% 0.22/0.50    inference(resolution,[],[f285,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.50  fof(f285,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(X1,X2),X0) | k1_xboole_0 = X0) ) | ~spl6_9),
% 0.22/0.50    inference(resolution,[],[f119,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X1 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) ) | ~spl6_9),
% 0.22/0.50    inference(superposition,[],[f114,f34])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    r2_hidden(sK4(k1_xboole_0),k1_xboole_0) | ~spl6_9),
% 0.22/0.50    inference(backward_demodulation,[],[f52,f98])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | ~spl6_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f96])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    r2_hidden(sK4(sK0),sK0)),
% 0.22/0.50    inference(resolution,[],[f27,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK4(X0),X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.22/0.50    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ~spl6_8),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f102])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    $false | ~spl6_8),
% 0.22/0.50    inference(subsumption_resolution,[],[f101,f33])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ~r1_tarski(k1_xboole_0,sK3) | ~spl6_8),
% 0.22/0.50    inference(backward_demodulation,[],[f29,f94])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~spl6_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f92])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl6_8 | spl6_9 | ~spl6_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f90,f48,f96,f92])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    spl6_2 <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl6_2),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f89])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl6_2),
% 0.22/0.50    inference(superposition,[],[f34,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | ~spl6_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f55,f29])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    r1_tarski(sK1,sK3) | k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | ~spl6_2),
% 0.22/0.50    inference(resolution,[],[f50,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (r1_tarski(X0,X2) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | ~spl6_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f48])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    spl6_1 | spl6_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f48,f44])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (31770)------------------------------
% 0.22/0.50  % (31770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (31770)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (31770)Memory used [KB]: 6396
% 0.22/0.50  % (31770)Time elapsed: 0.081 s
% 0.22/0.50  % (31770)------------------------------
% 0.22/0.50  % (31770)------------------------------
% 0.22/0.50  % (31756)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (31757)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (31748)Success in time 0.141 s
%------------------------------------------------------------------------------
