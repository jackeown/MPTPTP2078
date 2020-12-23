%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  70 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :   89 ( 259 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(global_subsumption,[],[f19,f34,f35])).

fof(f35,plain,(
    r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) ),
    inference(resolution,[],[f31,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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

fof(f31,plain,(
    r2_hidden(sK1,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f28,f17])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))
      | ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) )
    & r2_hidden(sK1,sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f11,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
              | ~ r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) )
            & r2_hidden(X1,X0) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ( ~ r2_hidden(k2_mcart_1(X1),k2_relat_1(sK0))
            | ~ r2_hidden(k1_mcart_1(X1),k1_relat_1(sK0)) )
          & r2_hidden(X1,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X1] :
        ( ( ~ r2_hidden(k2_mcart_1(X1),k2_relat_1(sK0))
          | ~ r2_hidden(k1_mcart_1(X1),k1_relat_1(sK0)) )
        & r2_hidden(X1,sK0) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))
        | ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) )
      & r2_hidden(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
            | ~ r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) )
          & r2_hidden(X1,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r2_hidden(X1,X0)
           => ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
              & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
            & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_mcart_1)).

fof(f28,plain,
    ( r2_hidden(sK1,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f27,f20])).

fof(f20,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f27,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | r2_hidden(sK1,X0) ) ),
    inference(resolution,[],[f18,f21])).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f18,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) ),
    inference(resolution,[],[f31,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))
    | ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:04:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (10940)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.45  % (10940)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(global_subsumption,[],[f19,f34,f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))),
% 0.21/0.45    inference(resolution,[],[f31,f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    r2_hidden(sK1,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.45    inference(subsumption_resolution,[],[f28,f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    v1_relat_1(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ((~r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))) & r2_hidden(sK1,sK0)) & v1_relat_1(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f11,f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : ((~r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) | ~r2_hidden(k1_mcart_1(X1),k1_relat_1(X0))) & r2_hidden(X1,X0)) & v1_relat_1(X0)) => (? [X1] : ((~r2_hidden(k2_mcart_1(X1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(X1),k1_relat_1(sK0))) & r2_hidden(X1,sK0)) & v1_relat_1(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ? [X1] : ((~r2_hidden(k2_mcart_1(X1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(X1),k1_relat_1(sK0))) & r2_hidden(X1,sK0)) => ((~r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))) & r2_hidden(sK1,sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f6,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : ((~r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) | ~r2_hidden(k1_mcart_1(X1),k1_relat_1(X0))) & r2_hidden(X1,X0)) & v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_hidden(X1,X0) => (r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)))))),
% 0.21/0.45    inference(negated_conjecture,[],[f4])).
% 0.21/0.45  fof(f4,conjecture,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_hidden(X1,X0) => (r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_mcart_1)).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    r2_hidden(sK1,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.45    inference(resolution,[],[f27,f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,plain,(
% 0.21/0.45    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_tarski(sK0,X0) | r2_hidden(sK1,X0)) )),
% 0.21/0.45    inference(resolution,[],[f18,f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(rectify,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    r2_hidden(sK1,sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))),
% 0.21/0.45    inference(resolution,[],[f31,f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ~r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (10940)------------------------------
% 0.21/0.45  % (10940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (10940)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (10940)Memory used [KB]: 5373
% 0.21/0.45  % (10940)Time elapsed: 0.036 s
% 0.21/0.45  % (10940)------------------------------
% 0.21/0.45  % (10940)------------------------------
% 0.21/0.45  % (10927)Success in time 0.095 s
%------------------------------------------------------------------------------
