%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0006+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   24 (  34 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 (  76 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f502,plain,(
    $false ),
    inference(resolution,[],[f473,f136])).

fof(f136,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f473,plain,(
    r2_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f55,f469])).

fof(f469,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f468,f179])).

fof(f179,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f140,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f140,plain,(
    ~ r2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f55,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f468,plain,(
    r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f449])).

fof(f449,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f168,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f168,plain,(
    ! [X44] :
      ( r2_hidden(sK10(sK1,X44),sK0)
      | r1_tarski(sK1,X44) ) ),
    inference(resolution,[],[f54,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f54,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( ~ r2_hidden(X2,X0)
                & r2_hidden(X2,X1) )
          & r2_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f35])).

fof(f35,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f55,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
