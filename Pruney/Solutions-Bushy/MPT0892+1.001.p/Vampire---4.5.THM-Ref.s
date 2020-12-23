%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0892+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   22 (  62 expanded)
%              Number of leaves         :    4 (  19 expanded)
%              Depth                    :   12
%              Number of atoms          :   54 ( 170 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(resolution,[],[f78,f17])).

fof(f17,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f11,f14,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f11,plain,(
    ~ r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( r1_xboole_0(sK2,sK5)
      | r1_xboole_0(sK1,sK4)
      | r1_xboole_0(sK0,sK3) )
    & ~ r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( r1_xboole_0(X2,X5)
          | r1_xboole_0(X1,X4)
          | r1_xboole_0(X0,X3) )
        & ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
   => ( ( r1_xboole_0(sK2,sK5)
        | r1_xboole_0(sK1,sK4)
        | r1_xboole_0(sK0,sK3) )
      & ~ r1_xboole_0(k3_zfmisc_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( r1_xboole_0(X2,X5)
        | r1_xboole_0(X1,X4)
        | r1_xboole_0(X0,X3) )
      & ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
       => ( ~ r1_xboole_0(X2,X5)
          & ~ r1_xboole_0(X1,X4)
          & ~ r1_xboole_0(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
     => ( ~ r1_xboole_0(X2,X5)
        & ~ r1_xboole_0(X1,X4)
        & ~ r1_xboole_0(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_mcart_1)).

fof(f78,plain,(
    ! [X6,X4,X7,X5] : r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X4),X5),k2_zfmisc_1(k2_zfmisc_1(sK3,X6),X7)) ),
    inference(resolution,[],[f69,f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f69,plain,(
    ! [X2,X3] : r1_xboole_0(k2_zfmisc_1(sK0,X2),k2_zfmisc_1(sK3,X3)) ),
    inference(resolution,[],[f64,f15])).

fof(f64,plain,(
    r1_xboole_0(sK0,sK3) ),
    inference(resolution,[],[f47,f17])).

fof(f47,plain,(
    ! [X6,X4,X7,X5] :
      ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X4,sK1),X5),k2_zfmisc_1(k2_zfmisc_1(X6,sK4),X7))
      | r1_xboole_0(sK0,sK3) ) ),
    inference(resolution,[],[f40,f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK4))
      | r1_xboole_0(sK0,sK3) ) ),
    inference(resolution,[],[f36,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,
    ( r1_xboole_0(sK1,sK4)
    | r1_xboole_0(sK0,sK3) ),
    inference(resolution,[],[f30,f17])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(X1,sK5))
      | r1_xboole_0(sK1,sK4)
      | r1_xboole_0(sK0,sK3) ) ),
    inference(resolution,[],[f16,f12])).

fof(f12,plain,
    ( r1_xboole_0(sK2,sK5)
    | r1_xboole_0(sK1,sK4)
    | r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
