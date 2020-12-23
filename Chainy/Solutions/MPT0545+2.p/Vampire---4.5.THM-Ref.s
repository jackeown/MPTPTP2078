%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0545+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:36 EST 2020

% Result     : Theorem 1.12s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   17 (  28 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   30 (  55 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f944,plain,(
    $false ),
    inference(subsumption_resolution,[],[f943,f863])).

fof(f863,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f835])).

fof(f835,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f796,f834])).

fof(f834,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f796,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f725])).

fof(f725,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(negated_conjecture,[],[f724])).

fof(f724,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

fof(f943,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f942,f906])).

% (18762)dis+1004_1_aac=none:acc=on:afp=40000:afq=1.2:anc=none:cond=on:fde=unused:gs=on:gsem=off:irw=on:nm=32:nwc=2:sd=1:ss=axioms:sos=theory:sp=reverse_arity:urr=ec_only_17 on theBenchmark
fof(f906,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f829])).

fof(f829,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f721])).

fof(f721,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f942,plain,(
    ~ r1_tarski(k9_relat_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f864,f940])).

fof(f940,plain,(
    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(resolution,[],[f913,f863])).

fof(f913,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f831])).

fof(f831,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f723])).

fof(f723,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f864,plain,(
    ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f835])).
%------------------------------------------------------------------------------
