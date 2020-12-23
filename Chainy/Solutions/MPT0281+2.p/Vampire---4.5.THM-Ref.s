%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0281+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:21 EST 2020

% Result     : Theorem 5.31s
% Output     : Refutation 5.31s
% Verified   : 
% Statistics : Number of formulae       :   50 (  79 expanded)
%              Number of leaves         :   10 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  200 ( 333 expanded)
%              Number of equality atoms :   34 (  61 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9504,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9503,f1167])).

fof(f1167,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f860,f857])).

fof(f857,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f568])).

fof(f568,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f473])).

fof(f473,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f471,f472])).

fof(f472,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f471,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f470])).

fof(f470,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f284])).

fof(f284,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f860,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f603])).

fof(f603,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f481])).

fof(f481,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f480])).

fof(f480,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f9503,plain,(
    ~ r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f8183,f550])).

fof(f550,plain,(
    k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f465])).

fof(f465,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    & k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f385,f464])).

fof(f464,plain,
    ( ? [X0,X1] :
        ( ~ r3_xboole_0(X0,X1)
        & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) )
   => ( ~ r3_xboole_0(sK0,sK1)
      & k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f385,plain,(
    ? [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) ) ),
    inference(ennf_transformation,[],[f379])).

fof(f379,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))
       => r3_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f378])).

fof(f378,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))
     => r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_zfmisc_1)).

fof(f8183,plain,(
    ~ r2_hidden(k2_xboole_0(sK0,sK1),k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f1433,f1488,f867])).

fof(f867,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f627])).

fof(f627,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f496])).

fof(f496,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f494,f495])).

fof(f495,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f494,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f493])).

fof(f493,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f492])).

fof(f492,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f1488,plain,(
    ! [X0] : ~ r2_hidden(k2_xboole_0(X0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f1445,f858])).

fof(f858,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f567])).

fof(f567,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f473])).

fof(f1445,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(X0,sK1),sK0) ),
    inference(superposition,[],[f1416,f565])).

fof(f565,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1416,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(sK1,X0),sK0) ),
    inference(unit_resulting_resolution,[],[f922,f599])).

fof(f599,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f411])).

fof(f411,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f67])).

fof(f67,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f922,plain,(
    ~ r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f551,f558])).

fof(f558,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f469])).

fof(f469,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f468])).

fof(f468,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f551,plain,(
    ~ r3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f465])).

fof(f1433,plain,(
    ! [X0] : ~ r2_hidden(k2_xboole_0(sK0,X0),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1415,f858])).

fof(f1415,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),sK1) ),
    inference(unit_resulting_resolution,[],[f916,f599])).

fof(f916,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f551,f557])).

fof(f557,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f469])).
%------------------------------------------------------------------------------
