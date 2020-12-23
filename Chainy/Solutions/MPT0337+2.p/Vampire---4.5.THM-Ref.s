%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0337+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:25 EST 2020

% Result     : Theorem 4.36s
% Output     : Refutation 4.36s
% Verified   : 
% Statistics : Number of formulae       :   26 (  60 expanded)
%              Number of leaves         :    5 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :   69 ( 182 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5325,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5304,f4510])).

fof(f4510,plain,(
    ~ r1_xboole_0(k3_tarski(sK0),sK8(sK1,k3_tarski(sK0))) ),
    inference(unit_resulting_resolution,[],[f1323,f770])).

fof(f770,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f498])).

fof(f498,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1323,plain,(
    ~ r1_xboole_0(sK8(sK1,k3_tarski(sK0)),k3_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f1301,f715])).

fof(f715,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(sK8(X0,X1),X1)
      | r1_xboole_0(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f609])).

fof(f609,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ( ~ r1_xboole_0(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f456,f608])).

fof(f608,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_xboole_0(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f456,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f443])).

fof(f443,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(f1301,plain,(
    ~ r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f701,f770])).

fof(f701,plain,(
    ~ r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f597])).

fof(f597,plain,
    ( ~ r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1))
    & ! [X2,X3] :
        ( r1_xboole_0(X2,X3)
        | ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(X2,sK0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f452,f596])).

fof(f596,plain,
    ( ? [X0,X1] :
        ( ~ r1_xboole_0(k3_tarski(X0),k3_tarski(X1))
        & ! [X2,X3] :
            ( r1_xboole_0(X2,X3)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X0) ) )
   => ( ~ r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1))
      & ! [X3,X2] :
          ( r1_xboole_0(X2,X3)
          | ~ r2_hidden(X3,sK1)
          | ~ r2_hidden(X2,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f452,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k3_tarski(X0),k3_tarski(X1))
      & ! [X2,X3] :
          ( r1_xboole_0(X2,X3)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f451])).

fof(f451,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k3_tarski(X0),k3_tarski(X1))
      & ! [X2,X3] :
          ( r1_xboole_0(X2,X3)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f367])).

fof(f367,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ! [X2,X3] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X2,X0) )
           => r1_xboole_0(X2,X3) )
       => r1_xboole_0(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f366])).

fof(f366,conjecture,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( r2_hidden(X3,X1)
            & r2_hidden(X2,X0) )
         => r1_xboole_0(X2,X3) )
     => r1_xboole_0(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_zfmisc_1)).

fof(f5304,plain,(
    r1_xboole_0(k3_tarski(sK0),sK8(sK1,k3_tarski(sK0))) ),
    inference(unit_resulting_resolution,[],[f1322,f2755])).

fof(f2755,plain,(
    ! [X0] :
      ( r1_xboole_0(k3_tarski(sK0),X0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f2754])).

fof(f2754,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_xboole_0(k3_tarski(sK0),X0)
      | r1_xboole_0(k3_tarski(sK0),X0) ) ),
    inference(resolution,[],[f1367,f714])).

fof(f714,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_xboole_0(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f609])).

fof(f1367,plain,(
    ! [X30,X29] :
      ( ~ r2_hidden(sK8(X30,X29),sK0)
      | ~ r2_hidden(X29,sK1)
      | r1_xboole_0(k3_tarski(X30),X29) ) ),
    inference(resolution,[],[f700,f715])).

fof(f700,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X2,X3)
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f597])).

fof(f1322,plain,(
    r2_hidden(sK8(sK1,k3_tarski(sK0)),sK1) ),
    inference(unit_resulting_resolution,[],[f1301,f714])).
%------------------------------------------------------------------------------
