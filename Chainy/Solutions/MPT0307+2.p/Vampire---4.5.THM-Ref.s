%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0307+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:23 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   22 (  36 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 ( 102 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1923,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1922,f769])).

fof(f769,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f607])).

% (26005)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
fof(f607,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK4),k2_zfmisc_1(sK3,sK5))
    & r1_tarski(sK4,sK5)
    & r1_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f417,f606])).

fof(f606,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k2_zfmisc_1(sK2,sK4),k2_zfmisc_1(sK3,sK5))
      & r1_tarski(sK4,sK5)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f417,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f416])).

fof(f416,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f328])).

fof(f328,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f327])).

fof(f327,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f1922,plain,(
    ~ r1_tarski(sK2,sK3) ),
    inference(subsumption_resolution,[],[f1921,f770])).

fof(f770,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f607])).

fof(f1921,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r1_tarski(sK2,sK3) ),
    inference(resolution,[],[f1066,f1915])).

fof(f1915,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,sK4),k2_zfmisc_1(X0,sK5))
      | ~ r1_tarski(X0,sK3) ) ),
    inference(resolution,[],[f1065,f1894])).

fof(f1894,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(sK3,sK5))
      | ~ r1_tarski(k2_zfmisc_1(sK2,sK4),X0) ) ),
    inference(resolution,[],[f1091,f771])).

fof(f771,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK2,sK4),k2_zfmisc_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f607])).

fof(f1091,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f544])).

fof(f544,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f543])).

fof(f543,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1065,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f508])).

fof(f508,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f326])).

fof(f326,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f1066,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f508])).
%------------------------------------------------------------------------------
