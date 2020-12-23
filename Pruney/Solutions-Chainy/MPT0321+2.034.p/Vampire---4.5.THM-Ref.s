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
% DateTime   : Thu Dec  3 12:42:34 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :  108 (4532 expanded)
%              Number of leaves         :   11 (1092 expanded)
%              Depth                    :   40
%              Number of atoms          :  298 (16963 expanded)
%              Number of equality atoms :   93 (6244 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1161,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1151,f1003])).

fof(f1003,plain,(
    ~ r1_tarski(sK3,sK1) ),
    inference(subsumption_resolution,[],[f540,f914])).

fof(f914,plain,(
    sK1 != sK3 ),
    inference(subsumption_resolution,[],[f33,f913])).

fof(f913,plain,(
    sK2 = sK4 ),
    inference(global_subsumption,[],[f604,f910])).

fof(f910,plain,(
    r1_tarski(sK2,sK4) ),
    inference(subsumption_resolution,[],[f886,f52])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f886,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2))
    | r1_tarski(sK2,sK4) ),
    inference(superposition,[],[f551,f854])).

fof(f854,plain,(
    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK1,sK4) ),
    inference(subsumption_resolution,[],[f600,f830])).

fof(f830,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK4)) ),
    inference(superposition,[],[f271,f804])).

fof(f804,plain,(
    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(k3_xboole_0(sK3,sK1),sK4) ),
    inference(forward_demodulation,[],[f774,f30])).

fof(f30,plain,(
    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( sK2 != sK4
      | sK1 != sK3 )
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK2 != sK4
        | sK1 != sK3 )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f774,plain,(
    k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(k3_xboole_0(sK3,sK1),sK4) ),
    inference(superposition,[],[f630,f55])).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f34,f52])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f630,plain,(
    ! [X0] : k2_zfmisc_1(k3_xboole_0(X0,sK3),sK4) = k2_zfmisc_1(k3_xboole_0(X0,sK1),sK4) ),
    inference(backward_demodulation,[],[f257,f612])).

fof(f612,plain,(
    ! [X2,X3] : k3_xboole_0(k2_zfmisc_1(X2,sK4),k2_zfmisc_1(X3,sK2)) = k2_zfmisc_1(k3_xboole_0(X2,X3),sK4) ),
    inference(superposition,[],[f51,f605])).

fof(f605,plain,(
    sK4 = k3_xboole_0(sK4,sK2) ),
    inference(resolution,[],[f602,f34])).

fof(f602,plain,(
    r1_tarski(sK4,sK2) ),
    inference(subsumption_resolution,[],[f598,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f598,plain,
    ( r1_tarski(sK4,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f572,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f572,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK4),k2_zfmisc_1(sK1,sK2)) ),
    inference(superposition,[],[f306,f541])).

fof(f541,plain,(
    sK1 = k3_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f538,f34])).

fof(f538,plain,(
    r1_tarski(sK1,sK3) ),
    inference(subsumption_resolution,[],[f534,f32])).

fof(f32,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f534,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f502,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f502,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK2)) ),
    inference(superposition,[],[f271,f431])).

fof(f431,plain,(
    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(k3_xboole_0(sK1,sK3),sK2) ),
    inference(backward_demodulation,[],[f361,f430])).

fof(f430,plain,(
    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2)) ),
    inference(subsumption_resolution,[],[f428,f181])).

fof(f181,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(sK4,X0)),k2_zfmisc_1(sK1,sK2)) ),
    inference(superposition,[],[f161,f30])).

fof(f161,plain,(
    ! [X23,X21,X22] : r1_tarski(k2_zfmisc_1(X21,k3_xboole_0(X22,X23)),k2_zfmisc_1(X21,X22)) ),
    inference(superposition,[],[f75,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f51,f55])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f66,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f63,f54])).

fof(f54,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f14])).

fof(f14,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X3,X2,X0)
      | r2_hidden(sK5(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f41,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f428,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2)),k2_zfmisc_1(sK1,sK2))
    | k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2)) ),
    inference(resolution,[],[f425,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f425,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2))) ),
    inference(forward_demodulation,[],[f424,f30])).

fof(f424,plain,(
    r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2))) ),
    inference(superposition,[],[f415,f55])).

fof(f415,plain,(
    ! [X10] : r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(sK4,X10)),k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2))) ),
    inference(forward_demodulation,[],[f414,f151])).

fof(f151,plain,(
    ! [X0] : k2_zfmisc_1(sK3,k3_xboole_0(sK4,X0)) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,X0)) ),
    inference(superposition,[],[f137,f30])).

fof(f414,plain,(
    ! [X10] : r1_tarski(k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,X10)),k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2))) ),
    inference(forward_demodulation,[],[f397,f51])).

fof(f397,plain,(
    ! [X10] : r1_tarski(k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,X10)),k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2))) ),
    inference(superposition,[],[f161,f361])).

fof(f361,plain,(
    k2_zfmisc_1(k3_xboole_0(sK1,sK3),sK2) = k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2)) ),
    inference(superposition,[],[f151,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f51,f55])).

fof(f306,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X0,sK3),sK4),k2_zfmisc_1(sK1,sK2)) ),
    inference(superposition,[],[f271,f30])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f257,plain,(
    ! [X0] : k2_zfmisc_1(k3_xboole_0(X0,sK3),sK4) = k3_xboole_0(k2_zfmisc_1(X0,sK4),k2_zfmisc_1(sK1,sK2)) ),
    inference(superposition,[],[f140,f30])).

fof(f271,plain,(
    ! [X37,X35,X36] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X35,X37),X36),k2_zfmisc_1(X37,X36)) ),
    inference(superposition,[],[f101,f140])).

fof(f101,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f68,f40])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X1)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f64,f54])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X2,X3,X0)
      | r2_hidden(sK5(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f42,f39])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f600,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK4))
    | k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK1,sK4) ),
    inference(resolution,[],[f572,f37])).

fof(f551,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,X2))
      | r1_tarski(sK2,X2) ) ),
    inference(forward_demodulation,[],[f550,f541])).

fof(f550,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X2))
      | r1_tarski(sK2,X2) ) ),
    inference(subsumption_resolution,[],[f542,f31])).

fof(f542,plain,(
    ! [X2] :
      ( k1_xboole_0 = sK1
      | ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X2))
      | r1_tarski(sK2,X2) ) ),
    inference(backward_demodulation,[],[f432,f541])).

fof(f432,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X2))
      | r1_tarski(sK2,X2)
      | k1_xboole_0 = k3_xboole_0(sK1,sK3) ) ),
    inference(backward_demodulation,[],[f389,f430])).

fof(f389,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2)),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X2))
      | r1_tarski(sK2,X2)
      | k1_xboole_0 = k3_xboole_0(sK1,sK3) ) ),
    inference(superposition,[],[f50,f361])).

fof(f604,plain,
    ( ~ r1_tarski(sK2,sK4)
    | sK2 = sK4 ),
    inference(resolution,[],[f602,f37])).

fof(f33,plain,
    ( sK2 != sK4
    | sK1 != sK3 ),
    inference(cnf_transformation,[],[f17])).

fof(f540,plain,
    ( ~ r1_tarski(sK3,sK1)
    | sK1 = sK3 ),
    inference(resolution,[],[f538,f37])).

fof(f1151,plain,(
    r1_tarski(sK3,sK1) ),
    inference(superposition,[],[f101,f1116])).

fof(f1116,plain,(
    sK3 = k3_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f1064,f77])).

fof(f77,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k3_xboole_0(X3,X4))
      | k3_xboole_0(X3,X4) = X3 ) ),
    inference(resolution,[],[f75,f37])).

fof(f1064,plain,(
    r1_tarski(sK3,k3_xboole_0(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f997,f32])).

fof(f997,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK3,k3_xboole_0(sK3,sK1)) ),
    inference(backward_demodulation,[],[f860,f913])).

fof(f860,plain,
    ( r1_tarski(sK3,k3_xboole_0(sK3,sK1))
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f836,f52])).

fof(f836,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2))
    | r1_tarski(sK3,k3_xboole_0(sK3,sK1))
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f128,f804])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(X0,sK4))
      | r1_tarski(sK3,X0)
      | k1_xboole_0 = sK4 ) ),
    inference(superposition,[],[f49,f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:33:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (641)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (677)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (678)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (640)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.21/0.51  % (671)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.21/0.52  % (642)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.21/0.52  % (685)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.21/0.52  % (638)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.21/0.52  % (636)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.21/0.52  % (677)Refutation not found, incomplete strategy% (677)------------------------------
% 1.21/0.52  % (677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (677)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (677)Memory used [KB]: 1663
% 1.21/0.52  % (677)Time elapsed: 0.116 s
% 1.21/0.52  % (677)------------------------------
% 1.21/0.52  % (677)------------------------------
% 1.21/0.52  % (678)Refutation not found, incomplete strategy% (678)------------------------------
% 1.21/0.52  % (678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (678)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (678)Memory used [KB]: 10746
% 1.21/0.52  % (678)Time elapsed: 0.065 s
% 1.21/0.52  % (678)------------------------------
% 1.21/0.52  % (678)------------------------------
% 1.35/0.53  % (646)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.53  % (667)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.53  % (682)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.53  % (639)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.54  % (668)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.54  % (670)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.54  % (681)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.54  % (637)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.54  % (681)Refutation not found, incomplete strategy% (681)------------------------------
% 1.35/0.54  % (681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (681)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (681)Memory used [KB]: 6268
% 1.35/0.54  % (681)Time elapsed: 0.131 s
% 1.35/0.54  % (681)------------------------------
% 1.35/0.54  % (681)------------------------------
% 1.35/0.54  % (684)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.54  % (679)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.54  % (638)Refutation not found, incomplete strategy% (638)------------------------------
% 1.35/0.54  % (638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (676)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.54  % (638)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (638)Memory used [KB]: 10746
% 1.35/0.54  % (638)Time elapsed: 0.126 s
% 1.35/0.54  % (638)------------------------------
% 1.35/0.54  % (638)------------------------------
% 1.35/0.54  % (683)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.54  % (674)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.54  % (676)Refutation not found, incomplete strategy% (676)------------------------------
% 1.35/0.54  % (676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (676)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (676)Memory used [KB]: 10746
% 1.35/0.54  % (676)Time elapsed: 0.134 s
% 1.35/0.54  % (676)------------------------------
% 1.35/0.54  % (676)------------------------------
% 1.35/0.55  % (669)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.55  % (649)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.55  % (672)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.55  % (649)Refutation not found, incomplete strategy% (649)------------------------------
% 1.35/0.55  % (649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (675)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.55  % (649)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (649)Memory used [KB]: 10618
% 1.35/0.55  % (649)Time elapsed: 0.137 s
% 1.35/0.55  % (649)------------------------------
% 1.35/0.55  % (649)------------------------------
% 1.35/0.55  % (647)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.55  % (680)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.56  % (645)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.56  % (644)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.56  % (682)Refutation not found, incomplete strategy% (682)------------------------------
% 1.35/0.56  % (682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (682)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (682)Memory used [KB]: 10746
% 1.35/0.56  % (682)Time elapsed: 0.152 s
% 1.35/0.56  % (682)------------------------------
% 1.35/0.56  % (682)------------------------------
% 1.35/0.57  % (645)Refutation not found, incomplete strategy% (645)------------------------------
% 1.35/0.57  % (645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.57  % (672)Refutation not found, incomplete strategy% (672)------------------------------
% 1.35/0.57  % (672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.57  % (672)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.57  
% 1.35/0.57  % (672)Memory used [KB]: 10618
% 1.35/0.57  % (672)Time elapsed: 0.159 s
% 1.35/0.57  % (672)------------------------------
% 1.35/0.57  % (672)------------------------------
% 1.35/0.57  % (645)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.57  
% 1.35/0.57  % (645)Memory used [KB]: 10746
% 1.35/0.57  % (645)Time elapsed: 0.162 s
% 1.35/0.57  % (645)------------------------------
% 1.35/0.57  % (645)------------------------------
% 1.97/0.63  % (700)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.97/0.64  % (644)Refutation found. Thanks to Tanya!
% 1.97/0.64  % SZS status Theorem for theBenchmark
% 1.97/0.64  % SZS output start Proof for theBenchmark
% 1.97/0.64  fof(f1161,plain,(
% 1.97/0.64    $false),
% 1.97/0.64    inference(subsumption_resolution,[],[f1151,f1003])).
% 1.97/0.64  fof(f1003,plain,(
% 1.97/0.64    ~r1_tarski(sK3,sK1)),
% 1.97/0.64    inference(subsumption_resolution,[],[f540,f914])).
% 1.97/0.64  fof(f914,plain,(
% 1.97/0.64    sK1 != sK3),
% 1.97/0.64    inference(subsumption_resolution,[],[f33,f913])).
% 1.97/0.64  fof(f913,plain,(
% 1.97/0.64    sK2 = sK4),
% 1.97/0.64    inference(global_subsumption,[],[f604,f910])).
% 1.97/0.64  fof(f910,plain,(
% 1.97/0.64    r1_tarski(sK2,sK4)),
% 1.97/0.64    inference(subsumption_resolution,[],[f886,f52])).
% 1.97/0.64  fof(f52,plain,(
% 1.97/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.97/0.64    inference(equality_resolution,[],[f36])).
% 1.97/0.64  fof(f36,plain,(
% 1.97/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.97/0.64    inference(cnf_transformation,[],[f19])).
% 1.97/0.64  fof(f19,plain,(
% 1.97/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.97/0.64    inference(flattening,[],[f18])).
% 1.97/0.64  fof(f18,plain,(
% 1.97/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.97/0.64    inference(nnf_transformation,[],[f3])).
% 1.97/0.64  fof(f3,axiom,(
% 1.97/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.97/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.97/0.64  fof(f886,plain,(
% 1.97/0.64    ~r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2)) | r1_tarski(sK2,sK4)),
% 1.97/0.64    inference(superposition,[],[f551,f854])).
% 1.97/0.64  fof(f854,plain,(
% 1.97/0.64    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK1,sK4)),
% 1.97/0.64    inference(subsumption_resolution,[],[f600,f830])).
% 1.97/0.64  fof(f830,plain,(
% 1.97/0.64    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK4))),
% 1.97/0.64    inference(superposition,[],[f271,f804])).
% 1.97/0.64  fof(f804,plain,(
% 1.97/0.64    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(k3_xboole_0(sK3,sK1),sK4)),
% 1.97/0.64    inference(forward_demodulation,[],[f774,f30])).
% 1.97/0.64  fof(f30,plain,(
% 1.97/0.64    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4)),
% 1.97/0.64    inference(cnf_transformation,[],[f17])).
% 1.97/0.64  fof(f17,plain,(
% 1.97/0.64    (sK2 != sK4 | sK1 != sK3) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4)),
% 1.97/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f10,f16])).
% 1.97/0.64  fof(f16,plain,(
% 1.97/0.64    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK2 != sK4 | sK1 != sK3) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,sK4))),
% 1.97/0.64    introduced(choice_axiom,[])).
% 1.97/0.64  fof(f10,plain,(
% 1.97/0.64    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 1.97/0.64    inference(flattening,[],[f9])).
% 1.97/0.64  fof(f9,plain,(
% 1.97/0.64    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 1.97/0.64    inference(ennf_transformation,[],[f8])).
% 1.97/0.64  fof(f8,negated_conjecture,(
% 1.97/0.64    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.97/0.64    inference(negated_conjecture,[],[f7])).
% 1.97/0.64  fof(f7,conjecture,(
% 1.97/0.64    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.97/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 1.97/0.64  fof(f774,plain,(
% 1.97/0.64    k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(k3_xboole_0(sK3,sK1),sK4)),
% 1.97/0.64    inference(superposition,[],[f630,f55])).
% 1.97/0.64  fof(f55,plain,(
% 1.97/0.64    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.97/0.64    inference(resolution,[],[f34,f52])).
% 1.97/0.64  fof(f34,plain,(
% 1.97/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.97/0.64    inference(cnf_transformation,[],[f11])).
% 1.97/0.64  fof(f11,plain,(
% 1.97/0.64    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.97/0.64    inference(ennf_transformation,[],[f4])).
% 1.97/0.64  fof(f4,axiom,(
% 1.97/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.97/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.97/0.64  fof(f630,plain,(
% 1.97/0.64    ( ! [X0] : (k2_zfmisc_1(k3_xboole_0(X0,sK3),sK4) = k2_zfmisc_1(k3_xboole_0(X0,sK1),sK4)) )),
% 1.97/0.64    inference(backward_demodulation,[],[f257,f612])).
% 1.97/0.64  fof(f612,plain,(
% 1.97/0.64    ( ! [X2,X3] : (k3_xboole_0(k2_zfmisc_1(X2,sK4),k2_zfmisc_1(X3,sK2)) = k2_zfmisc_1(k3_xboole_0(X2,X3),sK4)) )),
% 1.97/0.64    inference(superposition,[],[f51,f605])).
% 1.97/0.64  fof(f605,plain,(
% 1.97/0.64    sK4 = k3_xboole_0(sK4,sK2)),
% 1.97/0.64    inference(resolution,[],[f602,f34])).
% 1.97/0.64  fof(f602,plain,(
% 1.97/0.64    r1_tarski(sK4,sK2)),
% 1.97/0.64    inference(subsumption_resolution,[],[f598,f31])).
% 1.97/0.64  fof(f31,plain,(
% 1.97/0.64    k1_xboole_0 != sK1),
% 1.97/0.64    inference(cnf_transformation,[],[f17])).
% 1.97/0.64  fof(f598,plain,(
% 1.97/0.64    r1_tarski(sK4,sK2) | k1_xboole_0 = sK1),
% 1.97/0.64    inference(resolution,[],[f572,f50])).
% 1.97/0.64  fof(f50,plain,(
% 1.97/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 1.97/0.64    inference(cnf_transformation,[],[f13])).
% 1.97/0.64  fof(f13,plain,(
% 1.97/0.64    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 1.97/0.64    inference(ennf_transformation,[],[f5])).
% 1.97/0.64  fof(f5,axiom,(
% 1.97/0.64    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 1.97/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 1.97/0.64  fof(f572,plain,(
% 1.97/0.64    r1_tarski(k2_zfmisc_1(sK1,sK4),k2_zfmisc_1(sK1,sK2))),
% 1.97/0.64    inference(superposition,[],[f306,f541])).
% 1.97/0.64  fof(f541,plain,(
% 1.97/0.64    sK1 = k3_xboole_0(sK1,sK3)),
% 1.97/0.64    inference(resolution,[],[f538,f34])).
% 1.97/0.64  fof(f538,plain,(
% 1.97/0.64    r1_tarski(sK1,sK3)),
% 1.97/0.64    inference(subsumption_resolution,[],[f534,f32])).
% 1.97/0.64  fof(f32,plain,(
% 1.97/0.64    k1_xboole_0 != sK2),
% 1.97/0.64    inference(cnf_transformation,[],[f17])).
% 1.97/0.64  fof(f534,plain,(
% 1.97/0.64    r1_tarski(sK1,sK3) | k1_xboole_0 = sK2),
% 1.97/0.64    inference(resolution,[],[f502,f49])).
% 1.97/0.64  fof(f49,plain,(
% 1.97/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 1.97/0.64    inference(cnf_transformation,[],[f13])).
% 1.97/0.64  fof(f502,plain,(
% 1.97/0.64    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK2))),
% 1.97/0.64    inference(superposition,[],[f271,f431])).
% 1.97/0.64  fof(f431,plain,(
% 1.97/0.64    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(k3_xboole_0(sK1,sK3),sK2)),
% 1.97/0.64    inference(backward_demodulation,[],[f361,f430])).
% 1.97/0.64  fof(f430,plain,(
% 1.97/0.64    k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2))),
% 1.97/0.64    inference(subsumption_resolution,[],[f428,f181])).
% 1.97/0.64  fof(f181,plain,(
% 1.97/0.64    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(sK4,X0)),k2_zfmisc_1(sK1,sK2))) )),
% 1.97/0.64    inference(superposition,[],[f161,f30])).
% 1.97/0.64  fof(f161,plain,(
% 1.97/0.64    ( ! [X23,X21,X22] : (r1_tarski(k2_zfmisc_1(X21,k3_xboole_0(X22,X23)),k2_zfmisc_1(X21,X22))) )),
% 1.97/0.64    inference(superposition,[],[f75,f137])).
% 1.97/0.64  fof(f137,plain,(
% 1.97/0.64    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) )),
% 1.97/0.64    inference(superposition,[],[f51,f55])).
% 1.97/0.64  fof(f75,plain,(
% 1.97/0.64    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.97/0.64    inference(duplicate_literal_removal,[],[f70])).
% 1.97/0.64  fof(f70,plain,(
% 1.97/0.64    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0) | r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.97/0.64    inference(resolution,[],[f66,f40])).
% 1.97/0.64  fof(f40,plain,(
% 1.97/0.64    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.97/0.64    inference(cnf_transformation,[],[f23])).
% 1.97/0.64  fof(f23,plain,(
% 1.97/0.64    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.97/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).
% 1.97/0.64  fof(f22,plain,(
% 1.97/0.64    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.97/0.64    introduced(choice_axiom,[])).
% 1.97/0.64  fof(f21,plain,(
% 1.97/0.64    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.97/0.64    inference(rectify,[],[f20])).
% 1.97/0.64  fof(f20,plain,(
% 1.97/0.64    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.97/0.64    inference(nnf_transformation,[],[f12])).
% 1.97/0.64  fof(f12,plain,(
% 1.97/0.64    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.97/0.64    inference(ennf_transformation,[],[f1])).
% 1.97/0.64  fof(f1,axiom,(
% 1.97/0.64    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.97/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.97/0.64  fof(f66,plain,(
% 1.97/0.64    ( ! [X2,X0,X1] : (r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X0) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 1.97/0.64    inference(resolution,[],[f63,f54])).
% 1.97/0.64  fof(f54,plain,(
% 1.97/0.64    ( ! [X0,X1] : (sP0(X1,X0,k3_xboole_0(X0,X1))) )),
% 1.97/0.64    inference(equality_resolution,[],[f47])).
% 1.97/0.64  fof(f47,plain,(
% 1.97/0.64    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.97/0.64    inference(cnf_transformation,[],[f29])).
% 1.97/0.64  fof(f29,plain,(
% 1.97/0.64    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.97/0.64    inference(nnf_transformation,[],[f15])).
% 1.97/0.64  fof(f15,plain,(
% 1.97/0.64    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.97/0.64    inference(definition_folding,[],[f2,f14])).
% 1.97/0.64  fof(f14,plain,(
% 1.97/0.64    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.97/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.97/0.64  fof(f2,axiom,(
% 1.97/0.64    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.97/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.97/0.64  fof(f63,plain,(
% 1.97/0.64    ( ! [X2,X0,X3,X1] : (~sP0(X3,X2,X0) | r2_hidden(sK5(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 1.97/0.64    inference(resolution,[],[f41,f39])).
% 1.97/0.64  fof(f39,plain,(
% 1.97/0.64    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.97/0.64    inference(cnf_transformation,[],[f23])).
% 1.97/0.64  fof(f41,plain,(
% 1.97/0.64    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~sP0(X0,X1,X2)) )),
% 1.97/0.64    inference(cnf_transformation,[],[f28])).
% 1.97/0.64  fof(f28,plain,(
% 1.97/0.64    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.97/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).
% 1.97/0.64  fof(f27,plain,(
% 1.97/0.64    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.97/0.64    introduced(choice_axiom,[])).
% 1.97/0.64  fof(f26,plain,(
% 1.97/0.64    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.97/0.64    inference(rectify,[],[f25])).
% 1.97/0.64  fof(f25,plain,(
% 1.97/0.64    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.97/0.64    inference(flattening,[],[f24])).
% 1.97/0.64  fof(f24,plain,(
% 1.97/0.64    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.97/0.64    inference(nnf_transformation,[],[f14])).
% 1.97/0.64  fof(f428,plain,(
% 1.97/0.64    ~r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2)),k2_zfmisc_1(sK1,sK2)) | k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2))),
% 1.97/0.64    inference(resolution,[],[f425,f37])).
% 1.97/0.64  fof(f37,plain,(
% 1.97/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.97/0.64    inference(cnf_transformation,[],[f19])).
% 1.97/0.64  fof(f425,plain,(
% 1.97/0.64    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2)))),
% 1.97/0.64    inference(forward_demodulation,[],[f424,f30])).
% 1.97/0.64  fof(f424,plain,(
% 1.97/0.64    r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2)))),
% 1.97/0.64    inference(superposition,[],[f415,f55])).
% 1.97/0.64  fof(f415,plain,(
% 1.97/0.64    ( ! [X10] : (r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(sK4,X10)),k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2)))) )),
% 1.97/0.64    inference(forward_demodulation,[],[f414,f151])).
% 1.97/0.64  fof(f151,plain,(
% 1.97/0.64    ( ! [X0] : (k2_zfmisc_1(sK3,k3_xboole_0(sK4,X0)) = k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,X0))) )),
% 1.97/0.64    inference(superposition,[],[f137,f30])).
% 1.97/0.64  fof(f414,plain,(
% 1.97/0.64    ( ! [X10] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,X10)),k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2)))) )),
% 1.97/0.64    inference(forward_demodulation,[],[f397,f51])).
% 1.97/0.64  fof(f397,plain,(
% 1.97/0.64    ( ! [X10] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,X10)),k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2)))) )),
% 1.97/0.64    inference(superposition,[],[f161,f361])).
% 1.97/0.64  fof(f361,plain,(
% 1.97/0.64    k2_zfmisc_1(k3_xboole_0(sK1,sK3),sK2) = k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2))),
% 1.97/0.64    inference(superposition,[],[f151,f140])).
% 1.97/0.64  fof(f140,plain,(
% 1.97/0.64    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 1.97/0.64    inference(superposition,[],[f51,f55])).
% 1.97/0.64  fof(f306,plain,(
% 1.97/0.64    ( ! [X0] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X0,sK3),sK4),k2_zfmisc_1(sK1,sK2))) )),
% 1.97/0.64    inference(superposition,[],[f271,f30])).
% 1.97/0.64  fof(f51,plain,(
% 1.97/0.64    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 1.97/0.64    inference(cnf_transformation,[],[f6])).
% 1.97/0.64  fof(f6,axiom,(
% 1.97/0.64    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 1.97/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 1.97/0.64  fof(f257,plain,(
% 1.97/0.64    ( ! [X0] : (k2_zfmisc_1(k3_xboole_0(X0,sK3),sK4) = k3_xboole_0(k2_zfmisc_1(X0,sK4),k2_zfmisc_1(sK1,sK2))) )),
% 1.97/0.64    inference(superposition,[],[f140,f30])).
% 1.97/0.64  fof(f271,plain,(
% 1.97/0.64    ( ! [X37,X35,X36] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X35,X37),X36),k2_zfmisc_1(X37,X36))) )),
% 1.97/0.64    inference(superposition,[],[f101,f140])).
% 1.97/0.64  fof(f101,plain,(
% 1.97/0.64    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 1.97/0.64    inference(duplicate_literal_removal,[],[f94])).
% 1.97/0.64  fof(f94,plain,(
% 1.97/0.64    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1) | r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 1.97/0.64    inference(resolution,[],[f68,f40])).
% 1.97/0.64  fof(f68,plain,(
% 1.97/0.64    ( ! [X2,X0,X1] : (r2_hidden(sK5(k3_xboole_0(X0,X1),X2),X1) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 1.97/0.64    inference(resolution,[],[f64,f54])).
% 1.97/0.64  fof(f64,plain,(
% 1.97/0.64    ( ! [X2,X0,X3,X1] : (~sP0(X2,X3,X0) | r2_hidden(sK5(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 1.97/0.64    inference(resolution,[],[f42,f39])).
% 1.97/0.64  fof(f42,plain,(
% 1.97/0.64    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~sP0(X0,X1,X2)) )),
% 1.97/0.64    inference(cnf_transformation,[],[f28])).
% 1.97/0.64  fof(f600,plain,(
% 1.97/0.64    ~r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK4)) | k2_zfmisc_1(sK1,sK2) = k2_zfmisc_1(sK1,sK4)),
% 1.97/0.64    inference(resolution,[],[f572,f37])).
% 1.97/0.64  fof(f551,plain,(
% 1.97/0.64    ( ! [X2] : (~r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,X2)) | r1_tarski(sK2,X2)) )),
% 1.97/0.64    inference(forward_demodulation,[],[f550,f541])).
% 1.97/0.64  fof(f550,plain,(
% 1.97/0.64    ( ! [X2] : (~r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X2)) | r1_tarski(sK2,X2)) )),
% 1.97/0.64    inference(subsumption_resolution,[],[f542,f31])).
% 1.97/0.64  fof(f542,plain,(
% 1.97/0.64    ( ! [X2] : (k1_xboole_0 = sK1 | ~r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X2)) | r1_tarski(sK2,X2)) )),
% 1.97/0.64    inference(backward_demodulation,[],[f432,f541])).
% 1.97/0.64  fof(f432,plain,(
% 1.97/0.64    ( ! [X2] : (~r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X2)) | r1_tarski(sK2,X2) | k1_xboole_0 = k3_xboole_0(sK1,sK3)) )),
% 1.97/0.64    inference(backward_demodulation,[],[f389,f430])).
% 1.97/0.64  fof(f389,plain,(
% 1.97/0.64    ( ! [X2] : (~r1_tarski(k2_zfmisc_1(sK3,k3_xboole_0(sK4,sK2)),k2_zfmisc_1(k3_xboole_0(sK1,sK3),X2)) | r1_tarski(sK2,X2) | k1_xboole_0 = k3_xboole_0(sK1,sK3)) )),
% 1.97/0.64    inference(superposition,[],[f50,f361])).
% 1.97/0.64  fof(f604,plain,(
% 1.97/0.64    ~r1_tarski(sK2,sK4) | sK2 = sK4),
% 1.97/0.64    inference(resolution,[],[f602,f37])).
% 1.97/0.64  fof(f33,plain,(
% 1.97/0.64    sK2 != sK4 | sK1 != sK3),
% 1.97/0.64    inference(cnf_transformation,[],[f17])).
% 1.97/0.64  fof(f540,plain,(
% 1.97/0.64    ~r1_tarski(sK3,sK1) | sK1 = sK3),
% 1.97/0.64    inference(resolution,[],[f538,f37])).
% 1.97/0.64  fof(f1151,plain,(
% 1.97/0.64    r1_tarski(sK3,sK1)),
% 1.97/0.64    inference(superposition,[],[f101,f1116])).
% 1.97/0.64  fof(f1116,plain,(
% 1.97/0.64    sK3 = k3_xboole_0(sK3,sK1)),
% 1.97/0.64    inference(resolution,[],[f1064,f77])).
% 1.97/0.64  fof(f77,plain,(
% 1.97/0.64    ( ! [X4,X3] : (~r1_tarski(X3,k3_xboole_0(X3,X4)) | k3_xboole_0(X3,X4) = X3) )),
% 1.97/0.64    inference(resolution,[],[f75,f37])).
% 1.97/0.64  fof(f1064,plain,(
% 1.97/0.64    r1_tarski(sK3,k3_xboole_0(sK3,sK1))),
% 1.97/0.64    inference(subsumption_resolution,[],[f997,f32])).
% 1.97/0.64  fof(f997,plain,(
% 1.97/0.64    k1_xboole_0 = sK2 | r1_tarski(sK3,k3_xboole_0(sK3,sK1))),
% 1.97/0.64    inference(backward_demodulation,[],[f860,f913])).
% 1.97/0.64  fof(f860,plain,(
% 1.97/0.64    r1_tarski(sK3,k3_xboole_0(sK3,sK1)) | k1_xboole_0 = sK4),
% 1.97/0.64    inference(subsumption_resolution,[],[f836,f52])).
% 1.97/0.64  fof(f836,plain,(
% 1.97/0.64    ~r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK2)) | r1_tarski(sK3,k3_xboole_0(sK3,sK1)) | k1_xboole_0 = sK4),
% 1.97/0.64    inference(superposition,[],[f128,f804])).
% 1.97/0.64  fof(f128,plain,(
% 1.97/0.64    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(X0,sK4)) | r1_tarski(sK3,X0) | k1_xboole_0 = sK4) )),
% 1.97/0.64    inference(superposition,[],[f49,f30])).
% 1.97/0.64  % SZS output end Proof for theBenchmark
% 1.97/0.64  % (644)------------------------------
% 1.97/0.64  % (644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.64  % (644)Termination reason: Refutation
% 1.97/0.64  
% 1.97/0.64  % (644)Memory used [KB]: 7291
% 1.97/0.64  % (644)Time elapsed: 0.220 s
% 1.97/0.64  % (644)------------------------------
% 1.97/0.64  % (644)------------------------------
% 1.97/0.65  % (630)Success in time 0.281 s
%------------------------------------------------------------------------------
