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
% DateTime   : Thu Dec  3 12:44:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 234 expanded)
%              Number of leaves         :   15 (  63 expanded)
%              Depth                    :   19
%              Number of atoms          :  260 ( 636 expanded)
%              Number of equality atoms :   60 ( 210 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(subsumption_resolution,[],[f135,f103])).

fof(f103,plain,(
    sK1 != sK2 ),
    inference(subsumption_resolution,[],[f102,f76])).

fof(f76,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f75,f43])).

% (12915)Termination reason: Refutation not found, incomplete strategy
fof(f43,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f75,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f74,f42])).

fof(f42,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f74,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f73,f72])).

fof(f72,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f71,f41])).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f71,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f44,f42])).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f73,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0))
      | ~ m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f64,f42])).

fof(f64,plain,(
    ! [X0] :
      ( r1_tarski(k1_subset_1(X0),k3_subset_1(X0,k1_subset_1(X0)))
      | ~ m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_subset_1(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

% (12915)Memory used [KB]: 10618
fof(f102,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | sK1 != sK2 ),
    inference(backward_demodulation,[],[f70,f101])).

fof(f101,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f99,f72])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f47,f43])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f70,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK1),sK1)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f69])).

fof(f69,plain,
    ( sK1 != sK2
    | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
    inference(backward_demodulation,[],[f40,f41])).

fof(f40,plain,
    ( sK2 != k2_subset_1(sK1)
    | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f24])).

% (12915)Time elapsed: 0.090 s
% (12915)------------------------------
% (12915)------------------------------
fof(f24,plain,
    ( ( sK2 != k2_subset_1(sK1)
      | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) )
    & ( sK2 = k2_subset_1(sK1)
      | r1_tarski(k3_subset_1(sK1,sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK2 != k2_subset_1(sK1)
        | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) )
      & ( sK2 = k2_subset_1(sK1)
        | r1_tarski(k3_subset_1(sK1,sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f135,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f130,f72])).

fof(f130,plain,(
    sK2 = k3_subset_1(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f100,f128])).

fof(f128,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f125,f81])).

fof(f81,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f52,f76])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f125,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,sK2),X0) ),
    inference(resolution,[],[f123,f67])).

fof(f67,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f19])).

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f123,plain,(
    ! [X8,X9] :
      ( ~ sP0(sK2,X9,k4_xboole_0(sK1,sK2))
      | r1_tarski(k4_xboole_0(sK1,sK2),X8) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X8,X9] :
      ( r1_tarski(k4_xboole_0(sK1,sK2),X8)
      | ~ sP0(sK2,X9,k4_xboole_0(sK1,sK2))
      | r1_tarski(k4_xboole_0(sK1,sK2),X8) ) ),
    inference(resolution,[],[f109,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X2)
      | ~ sP0(X2,X3,X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f57,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f109,plain,(
    ! [X4] :
      ( r2_hidden(sK3(k4_xboole_0(sK1,sK2),X4),sK2)
      | r1_tarski(k4_xboole_0(sK1,sK2),X4) ) ),
    inference(resolution,[],[f85,f104])).

fof(f104,plain,(
    r1_tarski(k4_xboole_0(sK1,sK2),sK2) ),
    inference(subsumption_resolution,[],[f92,f103])).

fof(f92,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK2)
    | sK1 = sK2 ),
    inference(backward_demodulation,[],[f68,f89])).

fof(f89,plain,(
    k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f46,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f68,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | sK1 = sK2 ),
    inference(backward_demodulation,[],[f39,f41])).

fof(f39,plain,
    ( sK2 = k2_subset_1(sK1)
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK3(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f53,f54])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f100,plain,(
    sK2 = k3_subset_1(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f98,f89])).

fof(f98,plain,(
    sK2 = k3_subset_1(sK1,k3_subset_1(sK1,sK2)) ),
    inference(resolution,[],[f47,f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:43:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (12919)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (12913)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (12913)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (12908)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (12934)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (12915)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (12915)Refutation not found, incomplete strategy% (12915)------------------------------
% 0.21/0.54  % (12915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f135,f103])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    sK1 != sK2),
% 0.21/0.55    inference(subsumption_resolution,[],[f102,f76])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f75,f43])).
% 0.21/0.55  % (12915)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f74,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | ~m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f73,f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(forward_demodulation,[],[f71,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f44,f42])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) | ~m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f64,f42])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_subset_1(X0),k3_subset_1(X0,k1_subset_1(X0))) | ~m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(equality_resolution,[],[f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 0.21/0.55  % (12915)Memory used [KB]: 10618
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    ~r1_tarski(k1_xboole_0,sK1) | sK1 != sK2),
% 0.21/0.55    inference(backward_demodulation,[],[f70,f101])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f99,f72])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 0.21/0.55    inference(resolution,[],[f47,f43])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ~r1_tarski(k3_subset_1(sK1,sK1),sK1) | sK1 != sK2),
% 0.21/0.55    inference(inner_rewriting,[],[f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    sK1 != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)),
% 0.21/0.55    inference(backward_demodulation,[],[f40,f41])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    sK2 != k2_subset_1(sK1) | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  % (12915)Time elapsed: 0.090 s
% 0.21/0.55  % (12915)------------------------------
% 0.21/0.55  % (12915)------------------------------
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    (sK2 != k2_subset_1(sK1) | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)) & (sK2 = k2_subset_1(sK1) | r1_tarski(k3_subset_1(sK1,sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK2 != k2_subset_1(sK1) | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)) & (sK2 = k2_subset_1(sK1) | r1_tarski(k3_subset_1(sK1,sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(flattening,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.21/0.55    inference(negated_conjecture,[],[f12])).
% 0.21/0.55  fof(f12,conjecture,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    sK1 = sK2),
% 0.21/0.55    inference(forward_demodulation,[],[f130,f72])).
% 0.21/0.55  fof(f130,plain,(
% 0.21/0.55    sK2 = k3_subset_1(sK1,k1_xboole_0)),
% 0.21/0.55    inference(backward_demodulation,[],[f100,f128])).
% 0.21/0.55  fof(f128,plain,(
% 0.21/0.55    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 0.21/0.55    inference(resolution,[],[f125,f81])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 0.21/0.55    inference(resolution,[],[f52,f76])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(flattening,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.55  fof(f125,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,sK2),X0)) )),
% 0.21/0.55    inference(resolution,[],[f123,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(equality_resolution,[],[f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(nnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.21/0.55    inference(definition_folding,[],[f2,f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.55  fof(f123,plain,(
% 0.21/0.55    ( ! [X8,X9] : (~sP0(sK2,X9,k4_xboole_0(sK1,sK2)) | r1_tarski(k4_xboole_0(sK1,sK2),X8)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f122])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    ( ! [X8,X9] : (r1_tarski(k4_xboole_0(sK1,sK2),X8) | ~sP0(sK2,X9,k4_xboole_0(sK1,sK2)) | r1_tarski(k4_xboole_0(sK1,sK2),X8)) )),
% 0.21/0.55    inference(resolution,[],[f109,f88])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK3(X0,X1),X2) | ~sP0(X2,X3,X0) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(resolution,[],[f57,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~sP0(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.55    inference(rectify,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.55    inference(flattening,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.55    inference(nnf_transformation,[],[f19])).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    ( ! [X4] : (r2_hidden(sK3(k4_xboole_0(sK1,sK2),X4),sK2) | r1_tarski(k4_xboole_0(sK1,sK2),X4)) )),
% 0.21/0.55    inference(resolution,[],[f85,f104])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    r1_tarski(k4_xboole_0(sK1,sK2),sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f92,f103])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    r1_tarski(k4_xboole_0(sK1,sK2),sK2) | sK1 = sK2),
% 0.21/0.55    inference(backward_demodulation,[],[f68,f89])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2)),
% 0.21/0.55    inference(resolution,[],[f46,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    r1_tarski(k3_subset_1(sK1,sK2),sK2) | sK1 = sK2),
% 0.21/0.55    inference(backward_demodulation,[],[f39,f41])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    sK2 = k2_subset_1(sK1) | r1_tarski(k3_subset_1(sK1,sK2),sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r2_hidden(sK3(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(resolution,[],[f53,f54])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f31])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    sK2 = k3_subset_1(sK1,k4_xboole_0(sK1,sK2))),
% 0.21/0.55    inference(forward_demodulation,[],[f98,f89])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    sK2 = k3_subset_1(sK1,k3_subset_1(sK1,sK2))),
% 0.21/0.55    inference(resolution,[],[f47,f38])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (12913)------------------------------
% 0.21/0.55  % (12913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12913)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (12913)Memory used [KB]: 6268
% 0.21/0.55  % (12913)Time elapsed: 0.081 s
% 0.21/0.55  % (12913)------------------------------
% 0.21/0.55  % (12913)------------------------------
% 0.21/0.55  % (12905)Success in time 0.187 s
%------------------------------------------------------------------------------
