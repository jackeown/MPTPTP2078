%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  78 expanded)
%              Number of leaves         :    8 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 230 expanded)
%              Number of equality atoms :   23 (  46 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(subsumption_resolution,[],[f178,f122])).

fof(f122,plain,(
    r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(resolution,[],[f57,f19])).

fof(f19,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
      | ~ r2_hidden(k1_mcart_1(sK0),sK1) )
    & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
          | ~ r2_hidden(k1_mcart_1(X0),X1) )
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
        | ~ r2_hidden(k1_mcart_1(sK0),sK1) )
      & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
       => ( r2_hidden(k2_mcart_1(X0),X2)
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1))
      | r2_hidden(k1_mcart_1(sK0),X0) ) ),
    inference(superposition,[],[f26,f38])).

fof(f38,plain,(
    sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    inference(superposition,[],[f29,f33])).

fof(f33,plain,(
    sK0 = k4_tarski(sK4(sK0),sK5(sK0)) ),
    inference(subsumption_resolution,[],[f32,f25])).

fof(f25,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f32,plain,
    ( sK0 = k4_tarski(sK4(sK0),sK5(sK0))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f19,f22])).

fof(f22,plain,(
    ! [X4,X0] :
      ( k4_tarski(sK4(X4),sK5(X4)) = X4
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK3(X0)
          & r2_hidden(sK3(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK4(X4),sK5(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f13,f15,f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK3(X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK4(X4),sK5(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f29,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) = k4_tarski(k1_mcart_1(k4_tarski(X1,X2)),k2_mcart_1(k4_tarski(X1,X2))) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_mcart_1)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f178,plain,(
    ~ r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(resolution,[],[f169,f20])).

fof(f20,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
    | ~ r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f169,plain,(
    r2_hidden(k2_mcart_1(sK0),sK2) ),
    inference(resolution,[],[f58,f19])).

fof(f58,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X2,X3))
      | r2_hidden(k2_mcart_1(sK0),X3) ) ),
    inference(superposition,[],[f27,f38])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:42:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (1852)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (1852)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f183,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f178,f122])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.21/0.47    inference(resolution,[],[f57,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    (~r2_hidden(k2_mcart_1(sK0),sK2) | ~r2_hidden(k1_mcart_1(sK0),sK1)) & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => ((~r2_hidden(k2_mcart_1(sK0),sK2) | ~r2_hidden(k1_mcart_1(sK0),sK1)) & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | r2_hidden(k1_mcart_1(sK0),X0)) )),
% 0.21/0.47    inference(superposition,[],[f26,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))),
% 0.21/0.47    inference(superposition,[],[f29,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    sK0 = k4_tarski(sK4(sK0),sK5(sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f32,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    sK0 = k4_tarski(sK4(sK0),sK5(sK0)) | ~v1_relat_1(k2_zfmisc_1(sK1,sK2))),
% 0.21/0.47    inference(resolution,[],[f19,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X4,X0] : (k4_tarski(sK4(X4),sK5(X4)) = X4 | ~r2_hidden(X4,X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0))) & (! [X4] : (k4_tarski(sK4(X4),sK5(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f13,f15,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK4(X4),sK5(X4)) = X4)),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(rectify,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X2,X1] : (k4_tarski(X1,X2) = k4_tarski(k1_mcart_1(k4_tarski(X1,X2)),k2_mcart_1(k4_tarski(X1,X2)))) )),
% 0.21/0.47    inference(equality_resolution,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | k4_tarski(X1,X2) != X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_mcart_1)).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    ~r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.21/0.47    inference(resolution,[],[f169,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ~r2_hidden(k2_mcart_1(sK0),sK2) | ~r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f169,plain,(
% 0.21/0.47    r2_hidden(k2_mcart_1(sK0),sK2)),
% 0.21/0.47    inference(resolution,[],[f58,f19])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X2,X3] : (~r2_hidden(sK0,k2_zfmisc_1(X2,X3)) | r2_hidden(k2_mcart_1(sK0),X3)) )),
% 0.21/0.47    inference(superposition,[],[f27,f38])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (1852)------------------------------
% 0.21/0.47  % (1852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (1852)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (1852)Memory used [KB]: 1791
% 0.21/0.47  % (1852)Time elapsed: 0.057 s
% 0.21/0.47  % (1852)------------------------------
% 0.21/0.47  % (1852)------------------------------
% 0.21/0.47  % (1846)Success in time 0.113 s
%------------------------------------------------------------------------------
