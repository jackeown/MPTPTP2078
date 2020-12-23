%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0928+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  54 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 223 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2443,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2428,f22])).

fof(f22,plain,(
    ~ r1_tarski(k2_zfmisc_1(k3_zfmisc_1(sK0,sK2,sK4),sK6),k2_zfmisc_1(k3_zfmisc_1(sK1,sK3,sK5),sK7)) ),
    inference(definition_unfolding,[],[f18,f19,f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f18,plain,(
    ~ r1_tarski(k4_zfmisc_1(sK0,sK2,sK4,sK6),k4_zfmisc_1(sK1,sK3,sK5,sK7)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k4_zfmisc_1(sK0,sK2,sK4,sK6),k4_zfmisc_1(sK1,sK3,sK5,sK7))
    & r1_tarski(sK6,sK7)
    & r1_tarski(sK4,sK5)
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f7,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ~ r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7))
        & r1_tarski(X6,X7)
        & r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k4_zfmisc_1(sK0,sK2,sK4,sK6),k4_zfmisc_1(sK1,sK3,sK5,sK7))
      & r1_tarski(sK6,sK7)
      & r1_tarski(sK4,sK5)
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ~ r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7))
      & r1_tarski(X6,X7)
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ~ r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7))
      & r1_tarski(X6,X7)
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( r1_tarski(X6,X7)
          & r1_tarski(X4,X5)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( r1_tarski(X6,X7)
        & r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_zfmisc_1(X0,X2,X4,X6),k4_zfmisc_1(X1,X3,X5,X7)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_mcart_1)).

fof(f2428,plain,(
    r1_tarski(k2_zfmisc_1(k3_zfmisc_1(sK0,sK2,sK4),sK6),k2_zfmisc_1(k3_zfmisc_1(sK1,sK3,sK5),sK7)) ),
    inference(resolution,[],[f2419,f26])).

fof(f26,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | r1_tarski(k2_zfmisc_1(X6,sK6),k2_zfmisc_1(X7,sK7)) ) ),
    inference(resolution,[],[f20,f17])).

fof(f17,plain,(
    r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,X3)
      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f2419,plain,(
    r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5)) ),
    inference(resolution,[],[f1010,f14])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f1010,plain,(
    ! [X175,X174] :
      ( ~ r1_tarski(X174,X175)
      | r1_tarski(k3_zfmisc_1(X174,sK2,sK4),k3_zfmisc_1(X175,sK3,sK5)) ) ),
    inference(resolution,[],[f141,f15])).

fof(f15,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f141,plain,(
    ! [X74,X72,X75,X73] :
      ( ~ r1_tarski(X73,X75)
      | r1_tarski(k3_zfmisc_1(X72,X73,sK4),k3_zfmisc_1(X74,X75,sK5))
      | ~ r1_tarski(X72,X74) ) ),
    inference(resolution,[],[f21,f16])).

fof(f16,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(X4,X5)
      | r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      | ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      | ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_mcart_1)).

%------------------------------------------------------------------------------
