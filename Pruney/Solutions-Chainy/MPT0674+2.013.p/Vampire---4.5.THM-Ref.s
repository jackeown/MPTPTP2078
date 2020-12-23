%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 107 expanded)
%              Number of leaves         :    7 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  145 ( 407 expanded)
%              Number of equality atoms :   52 ( 127 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174,plain,(
    $false ),
    inference(subsumption_resolution,[],[f173,f28])).

fof(f28,plain,(
    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0))
    & r2_hidden(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
        & r2_hidden(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0))
      & r2_hidden(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(f173,plain,(
    k11_relat_1(sK1,sK0) = k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f170,f59])).

fof(f59,plain,(
    k1_xboole_0 != k11_relat_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f56,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f27,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f27,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f170,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | k11_relat_1(sK1,sK0) = k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(trivial_inequality_removal,[],[f169])).

fof(f169,plain,
    ( k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0)
    | k1_xboole_0 = k11_relat_1(sK1,sK0)
    | k11_relat_1(sK1,sK0) = k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(superposition,[],[f34,f156])).

fof(f156,plain,(
    k1_funct_1(sK1,sK0) = sK2(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(resolution,[],[f155,f111])).

fof(f111,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k11_relat_1(sK1,X7))
      | k1_funct_1(sK1,X7) = X6 ) ),
    inference(subsumption_resolution,[],[f110,f25])).

fof(f110,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k11_relat_1(sK1,X7))
      | k1_funct_1(sK1,X7) = X6
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f108,f26])).

fof(f26,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f108,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k11_relat_1(sK1,X7))
      | k1_funct_1(sK1,X7) = X6
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f45,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f45,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),sK1)
      | ~ r2_hidden(X5,k11_relat_1(sK1,X4)) ) ),
    inference(resolution,[],[f25,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f155,plain,(
    r2_hidden(sK2(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)),k11_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f154,f59])).

fof(f154,plain,
    ( r2_hidden(sK2(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)),k11_relat_1(sK1,sK0))
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( k11_relat_1(sK1,sK0) != X0
      | r2_hidden(sK2(X0,k1_funct_1(sK1,sK0)),X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f28,f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:52:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (1780)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (1780)Refutation not found, incomplete strategy% (1780)------------------------------
% 0.22/0.51  % (1780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1780)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (1780)Memory used [KB]: 6268
% 0.22/0.51  % (1780)Time elapsed: 0.066 s
% 0.22/0.51  % (1780)------------------------------
% 0.22/0.51  % (1780)------------------------------
% 0.22/0.51  % (1788)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (1788)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f173,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0)) & r2_hidden(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ? [X0,X1] : (k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0)) & r2_hidden(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0,X1] : (k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0,X1] : ((k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    k11_relat_1(sK1,sK0) = k1_tarski(k1_funct_1(sK1,sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f170,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    k1_xboole_0 != k11_relat_1(sK1,sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f56,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    v1_relat_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    k1_xboole_0 != k11_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 0.22/0.51    inference(resolution,[],[f27,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    k1_xboole_0 = k11_relat_1(sK1,sK0) | k11_relat_1(sK1,sK0) = k1_tarski(k1_funct_1(sK1,sK0))),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f169])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0) | k1_xboole_0 = k11_relat_1(sK1,sK0) | k11_relat_1(sK1,sK0) = k1_tarski(k1_funct_1(sK1,sK0))),
% 0.22/0.51    inference(superposition,[],[f34,f156])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    k1_funct_1(sK1,sK0) = sK2(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.22/0.51    inference(resolution,[],[f155,f111])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    ( ! [X6,X7] : (~r2_hidden(X6,k11_relat_1(sK1,X7)) | k1_funct_1(sK1,X7) = X6) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f110,f25])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    ( ! [X6,X7] : (~r2_hidden(X6,k11_relat_1(sK1,X7)) | k1_funct_1(sK1,X7) = X6 | ~v1_relat_1(sK1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f108,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    v1_funct_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ( ! [X6,X7] : (~r2_hidden(X6,k11_relat_1(sK1,X7)) | k1_funct_1(sK1,X7) = X6 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.22/0.51    inference(resolution,[],[f45,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(nnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),sK1) | ~r2_hidden(X5,k11_relat_1(sK1,X4))) )),
% 0.22/0.52    inference(resolution,[],[f25,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(nnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    r2_hidden(sK2(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)),k11_relat_1(sK1,sK0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f154,f59])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    r2_hidden(sK2(k11_relat_1(sK1,sK0),k1_funct_1(sK1,sK0)),k11_relat_1(sK1,sK0)) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.22/0.52    inference(equality_resolution,[],[f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X0] : (k11_relat_1(sK1,sK0) != X0 | r2_hidden(sK2(X0,k1_funct_1(sK1,sK0)),X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(superposition,[],[f28,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (1788)------------------------------
% 0.22/0.52  % (1788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1788)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (1788)Memory used [KB]: 1791
% 0.22/0.52  % (1788)Time elapsed: 0.081 s
% 0.22/0.52  % (1788)------------------------------
% 0.22/0.52  % (1788)------------------------------
% 0.22/0.52  % (1764)Success in time 0.149 s
%------------------------------------------------------------------------------
