%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0230+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:34 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   29 (  41 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 (  93 expanded)
%              Number of equality atoms :   22 (  39 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f146,plain,(
    $false ),
    inference(subsumption_resolution,[],[f145,f25])).

fof(f25,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f145,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f143,f52])).

fof(f52,plain,(
    ~ sQ5_eqProxy(sK1,sK0) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ sQ5_eqProxy(X0,X1)
      | sQ5_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f33,plain,(
    ~ sQ5_eqProxy(sK0,sK1) ),
    inference(equality_proxy_replacement,[],[f10,f31])).

fof(f10,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f143,plain,
    ( sQ5_eqProxy(sK1,sK0)
    | ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(resolution,[],[f55,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_tarski(sK1,sK2))
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(resolution,[],[f9,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f9,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,k2_tarski(X0,sK2))
      | sQ5_eqProxy(X0,sK0) ) ),
    inference(resolution,[],[f47,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( sQ5_eqProxy(X0,X3)
      | sQ5_eqProxy(X1,X3)
      | ~ r2_hidden(X3,k2_tarski(X0,X1)) ) ),
    inference(equality_proxy_replacement,[],[f30,f31,f31])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f47,plain,(
    ~ sQ5_eqProxy(sK2,sK0) ),
    inference(resolution,[],[f32,f42])).

fof(f32,plain,(
    ~ sQ5_eqProxy(sK0,sK2) ),
    inference(equality_proxy_replacement,[],[f11,f31])).

fof(f11,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
