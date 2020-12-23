%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0397+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:28 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 115 expanded)
%              Number of leaves         :    8 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  114 ( 347 expanded)
%              Number of equality atoms :   15 (  80 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2098,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2097,f1726])).

fof(f1726,plain,(
    ~ r2_hidden(sK11(sK1,sK3(sK0,k1_setfam_1(sK1))),sK1) ),
    inference(subsumption_resolution,[],[f1725,f843])).

fof(f843,plain,(
    r2_hidden(sK3(sK0,k1_setfam_1(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f836,f750])).

fof(f750,plain,(
    ~ sQ12_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f650,f749])).

fof(f749,plain,(
    ! [X1,X0] :
      ( sQ12_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ12_eqProxy])])).

fof(f650,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f617])).

fof(f617,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    & k1_xboole_0 != sK0
    & r2_setfam_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f576,f616])).

fof(f616,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        & k1_xboole_0 != X0
        & r2_setfam_1(X1,X0) )
   => ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
      & k1_xboole_0 != sK0
      & r2_setfam_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f576,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r2_setfam_1(X1,X0) ) ),
    inference(flattening,[],[f575])).

fof(f575,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r2_setfam_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f559])).

fof(f559,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_setfam_1(X1,X0)
       => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f558])).

fof(f558,conjecture,(
    ! [X0,X1] :
      ( r2_setfam_1(X1,X0)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_setfam_1)).

fof(f836,plain,
    ( sQ12_eqProxy(k1_xboole_0,sK0)
    | r2_hidden(sK3(sK0,k1_setfam_1(sK1)),sK0) ),
    inference(resolution,[],[f651,f758])).

fof(f758,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | sQ12_eqProxy(k1_xboole_0,X0)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f669,f749])).

fof(f669,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f623])).

fof(f623,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f595,f622])).

fof(f622,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f595,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f594])).

fof(f594,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f569])).

fof(f569,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f651,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    inference(cnf_transformation,[],[f617])).

fof(f1725,plain,
    ( ~ r2_hidden(sK11(sK1,sK3(sK0,k1_setfam_1(sK1))),sK1)
    | ~ r2_hidden(sK3(sK0,k1_setfam_1(sK1)),sK0) ),
    inference(resolution,[],[f985,f814])).

fof(f814,plain,(
    ! [X1] :
      ( r1_tarski(sK11(sK1,X1),X1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f649,f734])).

fof(f734,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK11(X0,X2),X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f647])).

fof(f647,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(sK11(X0,X2),X2)
            & r2_hidden(sK11(X0,X2),X0) )
          | ~ r2_hidden(X2,X1) )
      | ~ r2_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f615,f646])).

fof(f646,plain,(
    ! [X2,X0] :
      ( ? [X3] :
          ( r1_tarski(X3,X2)
          & r2_hidden(X3,X0) )
     => ( r1_tarski(sK11(X0,X2),X2)
        & r2_hidden(sK11(X0,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f615,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X3,X2)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(X2,X1) )
      | ~ r2_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f574])).

fof(f574,plain,(
    ! [X0,X1] :
      ( r2_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X3,X2)
                  & r2_hidden(X3,X0) )
            & r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f546])).

fof(f546,axiom,(
    ! [X0,X1] :
      ( r2_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X3,X2)
                  & r2_hidden(X3,X0) )
            & r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_setfam_1)).

fof(f649,plain,(
    r2_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f617])).

% (8185)Refutation not found, incomplete strategy% (8185)------------------------------
% (8185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8185)Termination reason: Refutation not found, incomplete strategy

% (8185)Memory used [KB]: 12537
% (8185)Time elapsed: 0.216 s
% (8185)------------------------------
% (8185)------------------------------
fof(f985,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3(sK0,k1_setfam_1(sK1)))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f844,f666])).

fof(f666,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f590])).

fof(f590,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f589])).

fof(f589,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f571])).

fof(f571,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f844,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),sK3(sK0,k1_setfam_1(sK1))) ),
    inference(subsumption_resolution,[],[f837,f750])).

fof(f837,plain,
    ( sQ12_eqProxy(k1_xboole_0,sK0)
    | ~ r1_tarski(k1_setfam_1(sK1),sK3(sK0,k1_setfam_1(sK1))) ),
    inference(resolution,[],[f651,f757])).

fof(f757,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | sQ12_eqProxy(k1_xboole_0,X0)
      | ~ r1_tarski(X1,sK3(X0,X1)) ) ),
    inference(equality_proxy_replacement,[],[f670,f749])).

fof(f670,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f623])).

fof(f2097,plain,(
    r2_hidden(sK11(sK1,sK3(sK0,k1_setfam_1(sK1))),sK1) ),
    inference(resolution,[],[f877,f649])).

fof(f877,plain,(
    ! [X1] :
      ( ~ r2_setfam_1(X1,sK0)
      | r2_hidden(sK11(X1,sK3(sK0,k1_setfam_1(sK1))),X1) ) ),
    inference(resolution,[],[f843,f733])).

fof(f733,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK11(X0,X2),X0)
      | ~ r2_hidden(X2,X1)
      | ~ r2_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f647])).
%------------------------------------------------------------------------------
