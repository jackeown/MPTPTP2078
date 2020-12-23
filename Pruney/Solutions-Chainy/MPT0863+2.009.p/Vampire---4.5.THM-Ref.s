%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  85 expanded)
%              Number of leaves         :    6 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :  121 ( 335 expanded)
%              Number of equality atoms :   71 ( 237 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(subsumption_resolution,[],[f57,f53])).

fof(f53,plain,(
    sK1 != k1_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f50,f17])).

fof(f17,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ( sK4 != k2_mcart_1(sK0)
        & sK3 != k2_mcart_1(sK0) )
      | ( sK2 != k1_mcart_1(sK0)
        & sK1 != k1_mcart_1(sK0) ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ( ( k2_mcart_1(X0) != X4
            & k2_mcart_1(X0) != X3 )
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) )
   => ( ( ( sK4 != k2_mcart_1(sK0)
          & sK3 != k2_mcart_1(sK0) )
        | ( sK2 != k1_mcart_1(sK0)
          & sK1 != k1_mcart_1(sK0) ) )
      & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ( ( k2_mcart_1(X0) != X4
          & k2_mcart_1(X0) != X3 )
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
       => ( ( k2_mcart_1(X0) = X4
            | k2_mcart_1(X0) = X3 )
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
     => ( ( k2_mcart_1(X0) = X4
          | k2_mcart_1(X0) = X3 )
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_mcart_1)).

fof(f50,plain,
    ( sK1 != k1_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(trivial_inequality_removal,[],[f46])).

fof(f46,plain,
    ( sK4 != sK4
    | sK1 != k1_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f19,f40])).

fof(f40,plain,
    ( sK4 = k2_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f29,f16])).

fof(f16,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
      | k2_mcart_1(X0) = X2
      | k2_mcart_1(X0) = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).

fof(f19,plain,
    ( sK4 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f54,f52])).

fof(f52,plain,(
    sK2 != k1_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f51,f18])).

fof(f18,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,
    ( sK2 != k1_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(trivial_inequality_removal,[],[f45])).

fof(f45,plain,
    ( sK4 != sK4
    | sK2 != k1_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f20,f40])).

fof(f20,plain,
    ( sK4 != k2_mcart_1(sK0)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,
    ( sK2 = k1_mcart_1(sK0)
    | sK1 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f43,f33])).

fof(f33,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2)) ),
    inference(resolution,[],[f25,f16])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_tarski(X1,X2))
      | X0 = X2
      | X0 = X1 ) ),
    inference(condensation,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 = X3
      | X1 = X2
      | ~ r2_hidden(X1,k2_tarski(X2,X3))
      | ~ r2_hidden(X0,X4) ) ),
    inference(forward_demodulation,[],[f41,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 = X2
      | k2_mcart_1(k4_tarski(X0,X1)) = X3
      | ~ r2_hidden(X1,k2_tarski(X2,X3))
      | ~ r2_hidden(X0,X4) ) ),
    inference(forward_demodulation,[],[f39,f23])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X2
      | k2_mcart_1(k4_tarski(X0,X1)) = X3
      | ~ r2_hidden(X1,k2_tarski(X2,X3))
      | ~ r2_hidden(X0,X4) ) ),
    inference(resolution,[],[f29,f32])).

fof(f32,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X3,X1) ) ),
    inference(forward_demodulation,[],[f31,f22])).

fof(f22,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1) ) ),
    inference(forward_demodulation,[],[f30,f23])).

fof(f30,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(k2_mcart_1(k4_tarski(X3,X4)),X2)
      | ~ r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ! [X3,X4] : k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ! [X3,X4] : k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
     => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (8897)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (8902)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (8902)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f57,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    sK1 != k1_mcart_1(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f50,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    sK3 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ((sK4 != k2_mcart_1(sK0) & sK3 != k2_mcart_1(sK0)) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3,X4] : (((k2_mcart_1(X0) != X4 & k2_mcart_1(X0) != X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))) => (((sK4 != k2_mcart_1(sK0) & sK3 != k2_mcart_1(sK0)) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3,X4] : (((k2_mcart_1(X0) != X4 & k2_mcart_1(X0) != X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_mcart_1)).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    sK1 != k1_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    sK4 != sK4 | sK1 != k1_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 0.21/0.50    inference(superposition,[],[f19,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    sK4 = k2_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 0.21/0.50    inference(resolution,[],[f29,f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)))),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) | k2_mcart_1(X0) = X2 | k2_mcart_1(X0) = X3) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    sK4 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    sK1 = k1_mcart_1(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f54,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    sK2 != k1_mcart_1(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f51,f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    sK3 != k2_mcart_1(sK0) | sK2 != k1_mcart_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    sK2 != k1_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    sK4 != sK4 | sK2 != k1_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 0.21/0.50    inference(superposition,[],[f20,f40])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    sK4 != k2_mcart_1(sK0) | sK2 != k1_mcart_1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    sK2 = k1_mcart_1(sK0) | sK1 = k1_mcart_1(sK0)),
% 0.21/0.50    inference(resolution,[],[f43,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2))),
% 0.21/0.50    inference(resolution,[],[f25,f16])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X2 | X0 = X1) )),
% 0.21/0.50    inference(condensation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (X1 = X3 | X1 = X2 | ~r2_hidden(X1,k2_tarski(X2,X3)) | ~r2_hidden(X0,X4)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f41,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (X1 = X2 | k2_mcart_1(k4_tarski(X0,X1)) = X3 | ~r2_hidden(X1,k2_tarski(X2,X3)) | ~r2_hidden(X0,X4)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f39,f23])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X2 | k2_mcart_1(k4_tarski(X0,X1)) = X3 | ~r2_hidden(X1,k2_tarski(X2,X3)) | ~r2_hidden(X0,X4)) )),
% 0.21/0.50    inference(resolution,[],[f29,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X4,X2,X3,X1] : (r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(X4,X2) | ~r2_hidden(X3,X1)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f31,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X4,X2,X3,X1] : (~r2_hidden(X4,X2) | r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f30,f23])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X4,X2,X3,X1] : (r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(k2_mcart_1(k4_tarski(X3,X4)),X2) | ~r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(X3,X4) != X0 | ~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0 | ~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0) | (~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) => (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_mcart_1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (8902)------------------------------
% 0.21/0.50  % (8902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8902)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (8902)Memory used [KB]: 6268
% 0.21/0.50  % (8902)Time elapsed: 0.097 s
% 0.21/0.50  % (8902)------------------------------
% 0.21/0.50  % (8902)------------------------------
% 0.21/0.50  % (8894)Success in time 0.148 s
%------------------------------------------------------------------------------
