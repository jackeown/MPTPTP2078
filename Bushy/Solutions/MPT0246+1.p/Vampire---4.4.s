%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t41_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:06 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  41 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 ( 155 expanded)
%              Number of equality atoms :   52 ( 118 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f42,plain,(
    $false ),
    inference(subsumption_resolution,[],[f41,f22])).

fof(f22,plain,(
    k1_tarski(sK1) != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ! [X2] :
        ( sK1 = X2
        | ~ r2_hidden(X2,sK0) )
    & k1_xboole_0 != sK0
    & k1_tarski(sK1) != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( X1 = X2
            | ~ r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 )
   => ( ! [X2] :
          ( sK1 = X2
          | ~ r2_hidden(X2,sK0) )
      & k1_xboole_0 != sK0
      & k1_tarski(sK1) != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t41_zfmisc_1.p',t41_zfmisc_1)).

fof(f41,plain,(
    k1_tarski(sK1) = sK0 ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X1] :
      ( sK1 != X1
      | k1_tarski(X1) = sK0 ) ),
    inference(subsumption_resolution,[],[f34,f23])).

fof(f23,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X1] :
      ( sK1 != X1
      | k1_xboole_0 = sK0
      | k1_tarski(X1) = sK0 ) ),
    inference(duplicate_literal_removal,[],[f33])).

fof(f33,plain,(
    ! [X1] :
      ( sK1 != X1
      | k1_xboole_0 = sK0
      | k1_tarski(X1) = sK0
      | k1_tarski(X1) = sK0 ) ),
    inference(superposition,[],[f27,f31])).

fof(f31,plain,(
    ! [X0] :
      ( sK1 = sK2(sK0,X0)
      | k1_tarski(X0) = sK0 ) ),
    inference(subsumption_resolution,[],[f30,f23])).

fof(f30,plain,(
    ! [X0] :
      ( sK1 = sK2(sK0,X0)
      | k1_xboole_0 = sK0
      | k1_tarski(X0) = sK0 ) ),
    inference(resolution,[],[f24,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t41_zfmisc_1.p',l44_zfmisc_1)).

fof(f24,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
