%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0518+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:34 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   23 (  40 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  92 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f970,plain,(
    $false ),
    inference(subsumption_resolution,[],[f969,f919])).

fof(f919,plain,(
    ! [X22] : v1_relat_1(k8_relat_1(X22,sK1)) ),
    inference(resolution,[],[f823,f868])).

fof(f868,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f798])).

fof(f798,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f658])).

fof(f658,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f823,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f802])).

fof(f802,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f767,f801])).

fof(f801,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f767,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f695])).

fof(f695,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f694])).

fof(f694,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_relat_1)).

fof(f969,plain,(
    ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f968,f823])).

fof(f968,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f966,f918])).

fof(f918,plain,(
    ! [X21] : r1_tarski(k8_relat_1(X21,sK1),sK1) ),
    inference(resolution,[],[f823,f867])).

fof(f867,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f797])).

fof(f797,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f693])).

fof(f693,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f966,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK1),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f824,f844])).

fof(f844,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f784])).

fof(f784,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f783])).

fof(f783,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f706])).

fof(f706,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f824,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f802])).
%------------------------------------------------------------------------------
