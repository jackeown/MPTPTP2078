%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0396+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:28 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   37 (  63 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :   93 ( 164 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1084,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1079,f710])).

fof(f710,plain,(
    r2_hidden(sK10(sK0,k3_tarski(sK1)),sK0) ),
    inference(resolution,[],[f626,f654])).

fof(f654,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK10(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f613])).

fof(f613,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK10(X0,X1),X1)
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f589,f612])).

fof(f612,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK10(X0,X1),X1)
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f589,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f443])).

fof(f443,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f626,plain,(
    ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f597])).

fof(f597,plain,
    ( ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1))
    & r1_setfam_1(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f572,f596])).

fof(f596,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
        & r1_setfam_1(X0,X1) )
   => ( ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1))
      & r1_setfam_1(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f572,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
      & r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f556])).

fof(f556,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X0,X1)
       => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f555])).

fof(f555,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

fof(f1079,plain,(
    ~ r2_hidden(sK10(sK0,k3_tarski(sK1)),sK0) ),
    inference(resolution,[],[f1035,f711])).

fof(f711,plain,(
    ~ r1_tarski(sK10(sK0,k3_tarski(sK1)),k3_tarski(sK1)) ),
    inference(resolution,[],[f626,f655])).

fof(f655,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK10(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f613])).

fof(f1035,plain,(
    ! [X0] :
      ( r1_tarski(X0,k3_tarski(sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(duplicate_literal_removal,[],[f1021])).

fof(f1021,plain,(
    ! [X0] :
      ( r1_tarski(X0,k3_tarski(sK1))
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f765,f750])).

fof(f750,plain,(
    ! [X0] :
      ( r1_tarski(sK15(sK1,X0),k3_tarski(sK1))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f707,f659])).

fof(f659,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f592])).

fof(f592,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f316])).

fof(f316,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f707,plain,(
    ! [X0] :
      ( r2_hidden(sK15(sK1,X0),sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f625,f675])).

fof(f675,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK15(X1,X2),X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f624])).

fof(f624,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X2,sK15(X1,X2))
            & r2_hidden(sK15(X1,X2),X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f594,f623])).

fof(f623,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( r1_tarski(X2,X3)
          & r2_hidden(X3,X1) )
     => ( r1_tarski(X2,sK15(X1,X2))
        & r2_hidden(sK15(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f594,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f571])).

fof(f571,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f545])).

fof(f545,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f625,plain,(
    r1_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f597])).

fof(f765,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(sK15(sK1,X12),X13)
      | r1_tarski(X12,X13)
      | ~ r2_hidden(X12,sK0) ) ),
    inference(resolution,[],[f708,f632])).

fof(f632,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f580])).

fof(f580,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f579])).

fof(f579,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f708,plain,(
    ! [X1] :
      ( r1_tarski(X1,sK15(sK1,X1))
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f625,f676])).

fof(f676,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK15(X1,X2))
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f624])).
%------------------------------------------------------------------------------
