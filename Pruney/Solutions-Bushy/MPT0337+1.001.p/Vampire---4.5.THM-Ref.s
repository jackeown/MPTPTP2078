%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0337+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   26 (  49 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :   14
%              Number of atoms          :   73 ( 150 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,plain,(
    $false ),
    inference(subsumption_resolution,[],[f32,f14])).

fof(f14,plain,(
    ~ r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1))
    & ! [X2,X3] :
        ( r1_xboole_0(X2,X3)
        | ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(X2,sK0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).

fof(f9,plain,
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

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k3_tarski(X0),k3_tarski(X1))
      & ! [X2,X3] :
          ( r1_xboole_0(X2,X3)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k3_tarski(X0),k3_tarski(X1))
      & ! [X2,X3] :
          ( r1_xboole_0(X2,X3)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ! [X2,X3] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X2,X0) )
           => r1_xboole_0(X2,X3) )
       => r1_xboole_0(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( r2_hidden(X3,X1)
            & r2_hidden(X2,X0) )
         => r1_xboole_0(X2,X3) )
     => r1_xboole_0(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_zfmisc_1)).

fof(f32,plain,(
    r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(resolution,[],[f29,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f29,plain,(
    r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0)) ),
    inference(duplicate_literal_removal,[],[f27])).

fof(f27,plain,
    ( r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0))
    | r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0)) ),
    inference(resolution,[],[f23,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(sK2(X0,X1),X1)
      | r1_xboole_0(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ( ~ r1_xboole_0(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f11])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_xboole_0(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(f23,plain,(
    ! [X0] :
      ( r1_xboole_0(sK2(sK1,X0),k3_tarski(sK0))
      | r1_xboole_0(k3_tarski(sK1),X0) ) ),
    inference(resolution,[],[f22,f15])).

fof(f22,plain,(
    ! [X0] :
      ( r1_xboole_0(k3_tarski(sK0),sK2(sK1,X0))
      | r1_xboole_0(k3_tarski(sK1),X0) ) ),
    inference(duplicate_literal_removal,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( r1_xboole_0(k3_tarski(sK1),X0)
      | r1_xboole_0(k3_tarski(sK0),sK2(sK1,X0))
      | r1_xboole_0(k3_tarski(sK0),sK2(sK1,X0)) ) ),
    inference(resolution,[],[f19,f17])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(sK2(sK0,X0),sK2(sK1,X1))
      | r1_xboole_0(k3_tarski(sK1),X1)
      | r1_xboole_0(k3_tarski(sK0),X0) ) ),
    inference(resolution,[],[f18,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | r1_xboole_0(X1,sK2(sK1,X0))
      | r1_xboole_0(k3_tarski(sK1),X0) ) ),
    inference(resolution,[],[f16,f13])).

fof(f13,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,sK1)
      | r1_xboole_0(X2,X3)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
