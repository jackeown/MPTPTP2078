%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 290 expanded)
%              Number of leaves         :   11 (  78 expanded)
%              Depth                    :   16
%              Number of atoms          :  219 (1143 expanded)
%              Number of equality atoms :  138 ( 722 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f491,plain,(
    $false ),
    inference(subsumption_resolution,[],[f484,f449])).

fof(f449,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f384,f448])).

fof(f448,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f365])).

fof(f365,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f67,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f65,f50])).

fof(f50,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_mcart_1(X1),X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f46,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f384,plain,(
    ! [X1] :
      ( k1_mcart_1(X1) != k4_xboole_0(k1_mcart_1(X1),k1_mcart_1(X1))
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f53,f67])).

fof(f53,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f484,plain,(
    r2_hidden(sK1,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f471])).

fof(f471,plain,
    ( sK0 != sK0
    | r2_hidden(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f279,f453])).

fof(f453,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f452,f118])).

fof(f118,plain,(
    ~ r2_hidden(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f93,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0,k1_xboole_0)
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0,k1_xboole_0)
      | ~ r2_hidden(sK0,k1_xboole_0) ) ),
    inference(superposition,[],[f80,f80])).

fof(f80,plain,(
    ! [X0] :
      ( k2_mcart_1(sK1) = X0
      | ~ r2_hidden(sK0,k1_xboole_0) ) ),
    inference(resolution,[],[f76,f50])).

fof(f76,plain,(
    ! [X1] :
      ( r2_hidden(k2_mcart_1(sK1),X1)
      | ~ r2_hidden(sK0,k1_xboole_0) ) ),
    inference(resolution,[],[f70,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X3] :
      ( r2_hidden(sK1,X3)
      | ~ r2_hidden(sK0,k1_xboole_0) ) ),
    inference(superposition,[],[f65,f54])).

fof(f54,plain,(
    k1_mcart_1(sK0) = sK1 ),
    inference(superposition,[],[f34,f27])).

fof(f27,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f34,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f93,plain,
    ( k2_mcart_1(sK1) != k4_xboole_0(k2_mcart_1(sK1),k2_mcart_1(sK1))
    | ~ r2_hidden(sK0,k1_xboole_0) ),
    inference(superposition,[],[f53,f80])).

fof(f452,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f451])).

fof(f451,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | sK0 != sK0
    | sK0 = sK1 ),
    inference(superposition,[],[f354,f57])).

fof(f57,plain,
    ( sK0 = sK2
    | sK0 = sK1 ),
    inference(superposition,[],[f56,f55])).

fof(f55,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f28,f54])).

fof(f28,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    k2_mcart_1(sK0) = sK2 ),
    inference(superposition,[],[f35,f27])).

fof(f35,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f8])).

fof(f354,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | sK0 != sK2 ),
    inference(superposition,[],[f49,f344])).

fof(f344,plain,
    ( k1_xboole_0 = k1_tarski(sK2)
    | sK0 != sK2 ),
    inference(resolution,[],[f240,f49])).

fof(f240,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k1_tarski(X0))
      | sK0 != X0
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(duplicate_literal_removal,[],[f231])).

fof(f231,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ r2_hidden(sK2,k1_tarski(X0))
      | k1_tarski(X0) = k1_xboole_0
      | k1_tarski(X0) = k1_xboole_0 ) ),
    inference(superposition,[],[f120,f61])).

fof(f61,plain,(
    ! [X1] :
      ( sK3(k1_tarski(X1)) = X1
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f50,f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f120,plain,(
    ! [X0] :
      ( sK0 != sK3(X0)
      | ~ r2_hidden(sK2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f32,f27])).

fof(f32,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f279,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | sK0 != sK1 ),
    inference(superposition,[],[f49,f262])).

fof(f262,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | sK0 != sK1 ),
    inference(resolution,[],[f239,f49])).

fof(f239,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK1,k1_tarski(X1))
      | sK0 != X1
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(duplicate_literal_removal,[],[f232])).

fof(f232,plain,(
    ! [X1] :
      ( sK0 != X1
      | ~ r2_hidden(sK1,k1_tarski(X1))
      | k1_xboole_0 = k1_tarski(X1)
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(superposition,[],[f87,f61])).

fof(f87,plain,(
    ! [X0] :
      ( sK0 != sK3(X0)
      | ~ r2_hidden(sK1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f31,f27])).

fof(f31,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:37:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (9052)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.48  % (9071)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.49  % (9052)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f491,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f484,f449])).
% 0.21/0.50  fof(f449,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f384,f448])).
% 0.21/0.50  fof(f448,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f365])).
% 0.21/0.50  fof(f365,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(superposition,[],[f67,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(resolution,[],[f65,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.50    inference(equality_resolution,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.50    inference(rectify,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(k1_mcart_1(X1),X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.21/0.50    inference(superposition,[],[f46,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.50    inference(nnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.50  fof(f384,plain,(
% 0.21/0.50    ( ! [X1] : (k1_mcart_1(X1) != k4_xboole_0(k1_mcart_1(X1),k1_mcart_1(X1)) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.21/0.50    inference(superposition,[],[f53,f67])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.50  fof(f484,plain,(
% 0.21/0.50    r2_hidden(sK1,k1_xboole_0)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f471])).
% 0.21/0.50  fof(f471,plain,(
% 0.21/0.50    sK0 != sK0 | r2_hidden(sK1,k1_xboole_0)),
% 0.21/0.50    inference(backward_demodulation,[],[f279,f453])).
% 0.21/0.50  fof(f453,plain,(
% 0.21/0.50    sK0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f452,f118])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ~r2_hidden(sK0,k1_xboole_0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f93,f117])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(sK0,k1_xboole_0) | X0 = X1) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0,k1_xboole_0) | ~r2_hidden(sK0,k1_xboole_0)) )),
% 0.21/0.50    inference(superposition,[],[f80,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X0] : (k2_mcart_1(sK1) = X0 | ~r2_hidden(sK0,k1_xboole_0)) )),
% 0.21/0.50    inference(resolution,[],[f76,f50])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X1] : (r2_hidden(k2_mcart_1(sK1),X1) | ~r2_hidden(sK0,k1_xboole_0)) )),
% 0.21/0.50    inference(resolution,[],[f70,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X3] : (r2_hidden(sK1,X3) | ~r2_hidden(sK0,k1_xboole_0)) )),
% 0.21/0.50    inference(superposition,[],[f65,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    k1_mcart_1(sK0) = sK1),
% 0.21/0.50    inference(superposition,[],[f34,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f16,f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.51    inference(negated_conjecture,[],[f10])).
% 0.21/0.51  fof(f10,conjecture,(
% 0.21/0.51    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    k2_mcart_1(sK1) != k4_xboole_0(k2_mcart_1(sK1),k2_mcart_1(sK1)) | ~r2_hidden(sK0,k1_xboole_0)),
% 0.21/0.51    inference(superposition,[],[f53,f80])).
% 0.21/0.51  fof(f452,plain,(
% 0.21/0.51    r2_hidden(sK0,k1_xboole_0) | sK0 = sK1),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f451])).
% 0.21/0.51  fof(f451,plain,(
% 0.21/0.51    r2_hidden(sK0,k1_xboole_0) | sK0 != sK0 | sK0 = sK1),
% 0.21/0.51    inference(superposition,[],[f354,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    sK0 = sK2 | sK0 = sK1),
% 0.21/0.51    inference(superposition,[],[f56,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 0.21/0.51    inference(backward_demodulation,[],[f28,f54])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    k2_mcart_1(sK0) = sK2),
% 0.21/0.51    inference(superposition,[],[f35,f27])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f354,plain,(
% 0.21/0.51    r2_hidden(sK2,k1_xboole_0) | sK0 != sK2),
% 0.21/0.51    inference(superposition,[],[f49,f344])).
% 0.21/0.51  fof(f344,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tarski(sK2) | sK0 != sK2),
% 0.21/0.51    inference(resolution,[],[f240,f49])).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK2,k1_tarski(X0)) | sK0 != X0 | k1_tarski(X0) = k1_xboole_0) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f231])).
% 0.21/0.51  fof(f231,plain,(
% 0.21/0.51    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK2,k1_tarski(X0)) | k1_tarski(X0) = k1_xboole_0 | k1_tarski(X0) = k1_xboole_0) )),
% 0.21/0.51    inference(superposition,[],[f120,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X1] : (sK3(k1_tarski(X1)) = X1 | k1_xboole_0 = k1_tarski(X1)) )),
% 0.21/0.51    inference(resolution,[],[f50,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    ( ! [X0] : (sK0 != sK3(X0) | ~r2_hidden(sK2,X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(superposition,[],[f32,f27])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.21/0.51    inference(equality_resolution,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.21/0.51    inference(equality_resolution,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f279,plain,(
% 0.21/0.51    r2_hidden(sK1,k1_xboole_0) | sK0 != sK1),
% 0.21/0.51    inference(superposition,[],[f49,f262])).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tarski(sK1) | sK0 != sK1),
% 0.21/0.51    inference(resolution,[],[f239,f49])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(sK1,k1_tarski(X1)) | sK0 != X1 | k1_xboole_0 = k1_tarski(X1)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f232])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    ( ! [X1] : (sK0 != X1 | ~r2_hidden(sK1,k1_tarski(X1)) | k1_xboole_0 = k1_tarski(X1) | k1_xboole_0 = k1_tarski(X1)) )),
% 0.21/0.51    inference(superposition,[],[f87,f61])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0] : (sK0 != sK3(X0) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(superposition,[],[f31,f27])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (9052)------------------------------
% 0.21/0.51  % (9052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9052)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (9052)Memory used [KB]: 1918
% 0.21/0.51  % (9052)Time elapsed: 0.075 s
% 0.21/0.51  % (9052)------------------------------
% 0.21/0.51  % (9052)------------------------------
% 0.21/0.51  % (9039)Success in time 0.148 s
%------------------------------------------------------------------------------
