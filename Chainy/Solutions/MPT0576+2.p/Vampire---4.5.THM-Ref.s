%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0576+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  68 expanded)
%              Number of leaves         :    6 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  101 ( 317 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1030,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1018,f1000])).

fof(f1000,plain,(
    r1_tarski(k10_relat_1(sK3,sK0),k10_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f957,f872])).

fof(f872,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f857])).

fof(f857,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f836,f856,f855])).

fof(f855,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(X3,sK1))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f856,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(X3,sK1))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f836,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f835])).

fof(f835,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f767])).

fof(f767,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f766])).

fof(f766,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t180_relat_1)).

fof(f957,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | r1_tarski(k10_relat_1(X3,sK0),k10_relat_1(X3,sK1)) ) ),
    inference(resolution,[],[f874,f880])).

fof(f880,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f839])).

fof(f839,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f838])).

fof(f838,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f764])).

fof(f764,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f874,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f857])).

fof(f1018,plain,(
    ~ r1_tarski(k10_relat_1(sK3,sK0),k10_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f958,f953])).

fof(f953,plain,(
    ! [X2] : r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK3,X2)) ),
    inference(subsumption_resolution,[],[f952,f871])).

fof(f871,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f857])).

fof(f952,plain,(
    ! [X2] :
      ( r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK3,X2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f950,f872])).

fof(f950,plain,(
    ! [X2] :
      ( r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK3,X2))
      | ~ v1_relat_1(sK3)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f873,f883])).

fof(f883,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f843])).

fof(f843,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f842])).

fof(f842,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f765])).

fof(f765,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).

fof(f873,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f857])).

fof(f958,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,sK0),X0)
      | ~ r1_tarski(X0,k10_relat_1(sK3,sK1)) ) ),
    inference(resolution,[],[f875,f899])).

fof(f899,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f854])).

fof(f854,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f853])).

fof(f853,plain,(
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

fof(f875,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f857])).
%------------------------------------------------------------------------------
