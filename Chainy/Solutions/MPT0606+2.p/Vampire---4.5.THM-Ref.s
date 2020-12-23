%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0606+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  63 expanded)
%              Number of leaves         :    5 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :   96 ( 312 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1126,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1125,f943])).

fof(f943,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f936])).

fof(f936,plain,
    ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
    & r1_tarski(sK2,sK1)
    & v4_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f882,f935,f934])).

fof(f934,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
            & r1_tarski(X2,X1)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(sK1,sK0))
          & r1_tarski(X2,sK1)
          & v4_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f935,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,k7_relat_1(sK1,sK0))
        & r1_tarski(X2,sK1)
        & v4_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
      & r1_tarski(sK2,sK1)
      & v4_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f882,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f881])).

fof(f881,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f815])).

fof(f815,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( ( v4_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => ( r1_tarski(X2,X1)
             => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f814])).

fof(f814,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( r1_tarski(X2,X1)
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t210_relat_1)).

fof(f1125,plain,(
    ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1124,f944])).

fof(f944,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f936])).

fof(f1124,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1123,f1099])).

fof(f1099,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f1094,f944])).

fof(f1094,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f945,f993])).

fof(f993,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f942])).

fof(f942,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f933])).

fof(f933,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f650])).

fof(f650,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f945,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f936])).

fof(f1123,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1121,f946])).

fof(f946,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f936])).

fof(f1121,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f947,f963])).

fof(f963,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k7_relat_1(X1,X0))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f902])).

fof(f902,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k7_relat_1(X1,X0))
          | ~ r1_tarski(X2,X1)
          | ~ r1_tarski(k1_relat_1(X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f901])).

fof(f901,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k7_relat_1(X1,X0))
          | ~ r1_tarski(X2,X1)
          | ~ r1_tarski(k1_relat_1(X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f787])).

fof(f787,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( r1_tarski(X2,X1)
              & r1_tarski(k1_relat_1(X2),X0) )
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_relat_1)).

fof(f947,plain,(
    ~ r1_tarski(sK2,k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f936])).
%------------------------------------------------------------------------------
