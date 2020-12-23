%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0713+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:45 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   28 (  55 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :   13
%              Number of atoms          :   79 ( 194 expanded)
%              Number of equality atoms :   22 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3727,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3726,f1895])).

fof(f1895,plain,(
    v1_relat_1(sK26) ),
    inference(cnf_transformation,[],[f1572])).

fof(f1572,plain,
    ( k1_tarski(k1_funct_1(sK26,sK25)) != k2_relat_1(k7_relat_1(sK26,k1_tarski(sK25)))
    & r2_hidden(sK25,k1_relat_1(sK26))
    & v1_funct_1(sK26)
    & v1_relat_1(sK26) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25,sK26])],[f1040,f1571])).

fof(f1571,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
        & r2_hidden(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k1_tarski(k1_funct_1(sK26,sK25)) != k2_relat_1(k7_relat_1(sK26,k1_tarski(sK25)))
      & r2_hidden(sK25,k1_relat_1(sK26))
      & v1_funct_1(sK26)
      & v1_relat_1(sK26) ) ),
    introduced(choice_axiom,[])).

fof(f1040,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1039])).

fof(f1039,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f977])).

fof(f977,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) ) ) ),
    inference(negated_conjecture,[],[f976])).

fof(f976,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

fof(f3726,plain,(
    ~ v1_relat_1(sK26) ),
    inference(subsumption_resolution,[],[f3725,f1896])).

fof(f1896,plain,(
    v1_funct_1(sK26) ),
    inference(cnf_transformation,[],[f1572])).

fof(f3725,plain,
    ( ~ v1_funct_1(sK26)
    | ~ v1_relat_1(sK26) ),
    inference(subsumption_resolution,[],[f3719,f1897])).

fof(f1897,plain,(
    r2_hidden(sK25,k1_relat_1(sK26)) ),
    inference(cnf_transformation,[],[f1572])).

fof(f3719,plain,
    ( ~ r2_hidden(sK25,k1_relat_1(sK26))
    | ~ v1_funct_1(sK26)
    | ~ v1_relat_1(sK26) ),
    inference(trivial_inequality_removal,[],[f3718])).

fof(f3718,plain,
    ( k9_relat_1(sK26,k2_tarski(sK25,sK25)) != k9_relat_1(sK26,k2_tarski(sK25,sK25))
    | ~ r2_hidden(sK25,k1_relat_1(sK26))
    | ~ v1_funct_1(sK26)
    | ~ v1_relat_1(sK26) ),
    inference(duplicate_literal_removal,[],[f3680])).

fof(f3680,plain,
    ( k9_relat_1(sK26,k2_tarski(sK25,sK25)) != k9_relat_1(sK26,k2_tarski(sK25,sK25))
    | ~ r2_hidden(sK25,k1_relat_1(sK26))
    | ~ r2_hidden(sK25,k1_relat_1(sK26))
    | ~ v1_funct_1(sK26)
    | ~ v1_relat_1(sK26) ),
    inference(superposition,[],[f3358,f2005])).

fof(f2005,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1126])).

fof(f1126,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1125])).

fof(f1125,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f935])).

fof(f935,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

fof(f3358,plain,(
    k2_tarski(k1_funct_1(sK26,sK25),k1_funct_1(sK26,sK25)) != k9_relat_1(sK26,k2_tarski(sK25,sK25)) ),
    inference(backward_demodulation,[],[f2711,f3218])).

fof(f3218,plain,(
    ! [X320] : k9_relat_1(sK26,X320) = k2_relat_1(k7_relat_1(sK26,X320)) ),
    inference(resolution,[],[f1895,f2436])).

fof(f2436,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1375])).

fof(f1375,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f750])).

fof(f750,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f2711,plain,(
    k2_tarski(k1_funct_1(sK26,sK25),k1_funct_1(sK26,sK25)) != k2_relat_1(k7_relat_1(sK26,k2_tarski(sK25,sK25))) ),
    inference(definition_unfolding,[],[f1898,f2510,f2510])).

fof(f2510,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f1898,plain,(
    k1_tarski(k1_funct_1(sK26,sK25)) != k2_relat_1(k7_relat_1(sK26,k1_tarski(sK25))) ),
    inference(cnf_transformation,[],[f1572])).
%------------------------------------------------------------------------------
