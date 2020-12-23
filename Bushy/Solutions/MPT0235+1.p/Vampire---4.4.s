%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t30_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:05 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 397 expanded)
%              Number of leaves         :    7 (  97 expanded)
%              Depth                    :   22
%              Number of atoms          :  216 (2225 expanded)
%              Number of equality atoms :  122 (1220 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f268,plain,(
    $false ),
    inference(subsumption_resolution,[],[f264,f64])).

fof(f64,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t30_zfmisc_1.p',l3_zfmisc_1)).

fof(f264,plain,(
    ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(resolution,[],[f260,f62])).

fof(f62,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t30_zfmisc_1.p',d1_zfmisc_1)).

fof(f260,plain,(
    ~ r2_hidden(k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) ),
    inference(subsumption_resolution,[],[f259,f216])).

fof(f216,plain,(
    k1_tarski(sK0) = sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) ),
    inference(subsumption_resolution,[],[f214,f160])).

fof(f160,plain,
    ( k1_xboole_0 != sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | k1_tarski(sK0) = sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) ),
    inference(subsumption_resolution,[],[f159,f151])).

fof(f151,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))),k1_zfmisc_1(k1_tarski(sK0)))
    | k1_xboole_0 != sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) ),
    inference(resolution,[],[f150,f63])).

fof(f63,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f150,plain,
    ( ~ r1_tarski(sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))),k1_tarski(sK0))
    | k1_xboole_0 != sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X1] :
      ( k1_zfmisc_1(X1) != k1_zfmisc_1(k1_tarski(sK0))
      | k1_xboole_0 != sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(X1))
      | ~ r1_tarski(sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(X1)),X1) ) ),
    inference(resolution,[],[f69,f62])).

fof(f69,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK1(k1_xboole_0,k1_tarski(sK0),X1),X1)
      | k1_xboole_0 != sK1(k1_xboole_0,k1_tarski(sK0),X1)
      | k1_zfmisc_1(k1_tarski(sK0)) != X1 ) ),
    inference(superposition,[],[f39,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK1(X0,X1,X2) != X0
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t30_zfmisc_1.p',d2_tarski)).

fof(f39,plain,(
    k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f23])).

fof(f23,plain,
    ( ? [X0] : k1_zfmisc_1(k1_tarski(X0)) != k2_tarski(k1_xboole_0,k1_tarski(X0))
   => k1_zfmisc_1(k1_tarski(sK0)) != k2_tarski(k1_xboole_0,k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] : k1_zfmisc_1(k1_tarski(X0)) != k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t30_zfmisc_1.p',t30_zfmisc_1)).

fof(f159,plain,
    ( k1_xboole_0 != sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | k1_tarski(sK0) = sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | r2_hidden(sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))),k1_zfmisc_1(k1_tarski(sK0))) ),
    inference(subsumption_resolution,[],[f158,f39])).

fof(f158,plain,
    ( k1_xboole_0 != sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | k1_zfmisc_1(k1_tarski(sK0)) = k2_tarski(k1_xboole_0,k1_tarski(sK0))
    | k1_tarski(sK0) = sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | r2_hidden(sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))),k1_zfmisc_1(k1_tarski(sK0))) ),
    inference(subsumption_resolution,[],[f155,f65])).

fof(f65,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f155,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK0))
    | k1_xboole_0 != sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | k1_zfmisc_1(k1_tarski(sK0)) = k2_tarski(k1_xboole_0,k1_tarski(sK0))
    | k1_tarski(sK0) = sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | r2_hidden(sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))),k1_zfmisc_1(k1_tarski(sK0))) ),
    inference(superposition,[],[f150,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK1(X0,X1,X2) = X1
      | sK1(X0,X1,X2) = X0
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f214,plain,
    ( k1_tarski(sK0) = sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | k1_xboole_0 = sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) ),
    inference(duplicate_literal_removal,[],[f205])).

fof(f205,plain,
    ( k1_tarski(sK0) = sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | k1_tarski(sK0) = sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | k1_xboole_0 = sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) ),
    inference(resolution,[],[f189,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f189,plain,
    ( r1_tarski(sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))),k1_tarski(sK0))
    | k1_tarski(sK0) = sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) ),
    inference(resolution,[],[f165,f63])).

fof(f165,plain,
    ( r2_hidden(sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))),k1_zfmisc_1(k1_tarski(sK0)))
    | k1_tarski(sK0) = sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) ),
    inference(subsumption_resolution,[],[f164,f160])).

fof(f164,plain,
    ( k1_tarski(sK0) = sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | k1_xboole_0 = sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | r2_hidden(sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))),k1_zfmisc_1(k1_tarski(sK0))) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( k1_zfmisc_1(k1_tarski(sK0)) != X0
      | k1_tarski(sK0) = sK1(k1_xboole_0,k1_tarski(sK0),X0)
      | k1_xboole_0 = sK1(k1_xboole_0,k1_tarski(sK0),X0)
      | r2_hidden(sK1(k1_xboole_0,k1_tarski(sK0),X0),X0) ) ),
    inference(superposition,[],[f39,f43])).

fof(f259,plain,
    ( ~ r2_hidden(k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | k1_tarski(sK0) != sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0))) ),
    inference(trivial_inequality_removal,[],[f249])).

fof(f249,plain,
    ( ~ r2_hidden(k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | k1_tarski(sK0) != sK1(k1_xboole_0,k1_tarski(sK0),k1_zfmisc_1(k1_tarski(sK0)))
    | k1_zfmisc_1(k1_tarski(sK0)) != k1_zfmisc_1(k1_tarski(sK0)) ),
    inference(superposition,[],[f70,f216])).

fof(f70,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK1(k1_xboole_0,k1_tarski(sK0),X2),X2)
      | k1_tarski(sK0) != sK1(k1_xboole_0,k1_tarski(sK0),X2)
      | k1_zfmisc_1(k1_tarski(sK0)) != X2 ) ),
    inference(superposition,[],[f39,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK1(X0,X1,X2) != X1
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
