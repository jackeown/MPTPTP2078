%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0291+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:41 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   32 (  63 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :   76 ( 169 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f336,plain,(
    $false ),
    inference(subsumption_resolution,[],[f335,f54])).

fof(f54,plain,(
    r2_hidden(sK2(k3_tarski(sK0),sK1),k3_tarski(sK0)) ),
    inference(resolution,[],[f35,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f35,plain,(
    r2_hidden(sK2(k3_tarski(sK0),sK1),k3_xboole_0(k3_tarski(sK0),sK1)) ),
    inference(resolution,[],[f12,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f12,plain,(
    ~ r1_xboole_0(k3_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k3_tarski(X0),X1)
      & ! [X2] :
          ( r1_xboole_0(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r1_xboole_0(X2,X1) )
       => r1_xboole_0(k3_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(f335,plain,(
    ~ r2_hidden(sK2(k3_tarski(sK0),sK1),k3_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f321,f55])).

fof(f55,plain,(
    r2_hidden(sK2(k3_tarski(sK0),sK1),sK1) ),
    inference(resolution,[],[f35,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f321,plain,
    ( ~ r2_hidden(sK2(k3_tarski(sK0),sK1),sK1)
    | ~ r2_hidden(sK2(k3_tarski(sK0),sK1),k3_tarski(sK0)) ),
    inference(resolution,[],[f169,f30])).

fof(f30,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK4(X0,X2))
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK4(X0,X2))
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f169,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4(sK0,sK2(k3_tarski(sK0),sK1)))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f102,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f102,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK4(sK0,sK2(k3_tarski(sK0),sK1)),sK1)) ),
    inference(resolution,[],[f89,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f89,plain,(
    r1_xboole_0(sK4(sK0,sK2(k3_tarski(sK0),sK1)),sK1) ),
    inference(resolution,[],[f43,f54])).

fof(f43,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k3_tarski(sK0))
      | r1_xboole_0(sK4(sK0,X6),sK1) ) ),
    inference(resolution,[],[f11,f29])).

fof(f29,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK4(X0,X2),X0)
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X2),X0)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | r1_xboole_0(X2,sK1) ) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
