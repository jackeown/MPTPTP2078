%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:03 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 353 expanded)
%              Number of leaves         :   15 ( 100 expanded)
%              Depth                    :   33
%              Number of atoms          :  210 ( 965 expanded)
%              Number of equality atoms :   93 ( 433 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f227,plain,(
    $false ),
    inference(subsumption_resolution,[],[f224,f42])).

fof(f42,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

% (32593)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f224,plain,(
    ! [X0] : ~ r1_xboole_0(k2_tarski(sK1(k1_xboole_0),X0),k1_xboole_0) ),
    inference(resolution,[],[f220,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f220,plain,(
    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f214,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK2(X4),sK3(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f34,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK2(X4),sK3(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f214,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f213,f68])).

fof(f68,plain,(
    ! [X4] :
      ( v1_relat_1(k5_relat_1(sK0,X4))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f38,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f213,plain,(
    ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f212,f164])).

fof(f164,plain,(
    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f157])).

fof(f157,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f39,f156])).

fof(f156,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f153,f42])).

fof(f153,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
      | ~ r1_xboole_0(k2_tarski(sK1(k1_xboole_0),X0),k1_xboole_0) ) ),
    inference(resolution,[],[f149,f58])).

fof(f149,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(resolution,[],[f143,f49])).

fof(f143,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(resolution,[],[f142,f69])).

fof(f69,plain,(
    ! [X5] :
      ( v1_relat_1(k5_relat_1(X5,sK0))
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f38,f53])).

fof(f142,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f141,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f141,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f139,f62])).

fof(f62,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f139,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[],[f45,f131])).

fof(f131,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(subsumption_resolution,[],[f128,f42])).

fof(f128,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
      | ~ r1_xboole_0(k2_tarski(sK1(k1_xboole_0),X0),k1_xboole_0) ) ),
    inference(resolution,[],[f124,f58])).

fof(f124,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f122,f49])).

fof(f122,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f121,f40])).

fof(f40,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f121,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f119,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f119,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f65,f41])).

fof(f41,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(sK0))
      | k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,sK0))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f38,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f45,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f39,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f212,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f211,f44])).

fof(f211,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f208,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f208,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f45,f200])).

fof(f200,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f197,f42])).

fof(f197,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
      | ~ r1_xboole_0(k2_tarski(sK1(k1_xboole_0),X0),k1_xboole_0) ) ),
    inference(resolution,[],[f196,f58])).

fof(f196,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f181,f38])).

fof(f181,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
      | r2_hidden(sK1(k1_xboole_0),k1_xboole_0) ) ),
    inference(resolution,[],[f168,f49])).

fof(f168,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f167,f41])).

fof(f167,plain,(
    ! [X0] :
      ( k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f162,f156])).

fof(f162,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | k2_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k2_relat_1(k5_relat_1(X0,k5_relat_1(k1_xboole_0,sK0)))
      | ~ v1_relat_1(X0) ) ),
    inference(backward_demodulation,[],[f140,f156])).

fof(f140,plain,(
    ! [X0] :
      ( k2_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k2_relat_1(k5_relat_1(X0,k5_relat_1(k1_xboole_0,sK0)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ) ),
    inference(subsumption_resolution,[],[f137,f43])).

fof(f137,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k2_relat_1(X0))
      | k2_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k2_relat_1(k5_relat_1(X0,k5_relat_1(k1_xboole_0,sK0)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ) ),
    inference(superposition,[],[f47,f131])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:45:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (32583)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (32591)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.28/0.54  % (32599)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.28/0.54  % (32589)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.54  % (32586)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.54  % (32606)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.28/0.54  % (32587)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.28/0.54  % (32591)Refutation not found, incomplete strategy% (32591)------------------------------
% 1.28/0.54  % (32591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (32591)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (32591)Memory used [KB]: 10618
% 1.28/0.54  % (32591)Time elapsed: 0.124 s
% 1.28/0.54  % (32591)------------------------------
% 1.28/0.54  % (32591)------------------------------
% 1.28/0.54  % (32585)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.54  % (32612)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.28/0.54  % (32605)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.54  % (32598)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.54  % (32605)Refutation not found, incomplete strategy% (32605)------------------------------
% 1.36/0.54  % (32605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (32605)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (32605)Memory used [KB]: 10618
% 1.36/0.54  % (32605)Time elapsed: 0.124 s
% 1.36/0.54  % (32605)------------------------------
% 1.36/0.54  % (32605)------------------------------
% 1.36/0.55  % (32584)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.55  % (32601)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.55  % (32607)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.55  % (32608)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.55  % (32610)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.55  % (32596)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.55  % (32606)Refutation found. Thanks to Tanya!
% 1.36/0.55  % SZS status Theorem for theBenchmark
% 1.36/0.55  % SZS output start Proof for theBenchmark
% 1.36/0.55  fof(f227,plain,(
% 1.36/0.55    $false),
% 1.36/0.55    inference(subsumption_resolution,[],[f224,f42])).
% 1.36/0.55  fof(f42,plain,(
% 1.36/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f3])).
% 1.36/0.55  % (32593)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.55  fof(f3,axiom,(
% 1.36/0.55    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.36/0.55  fof(f224,plain,(
% 1.36/0.55    ( ! [X0] : (~r1_xboole_0(k2_tarski(sK1(k1_xboole_0),X0),k1_xboole_0)) )),
% 1.36/0.55    inference(resolution,[],[f220,f58])).
% 1.36/0.55  fof(f58,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f28])).
% 1.36/0.55  fof(f28,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.36/0.55    inference(ennf_transformation,[],[f9])).
% 1.36/0.55  fof(f9,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.36/0.55  fof(f220,plain,(
% 1.36/0.55    r2_hidden(sK1(k1_xboole_0),k1_xboole_0)),
% 1.36/0.55    inference(resolution,[],[f214,f49])).
% 1.36/0.55  fof(f49,plain,(
% 1.36/0.55    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f35])).
% 1.36/0.55  fof(f35,plain,(
% 1.36/0.55    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0))) & (! [X4] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.36/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f34,f33])).
% 1.36/0.55  fof(f33,plain,(
% 1.36/0.55    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 1.36/0.55    introduced(choice_axiom,[])).
% 1.36/0.55  fof(f34,plain,(
% 1.36/0.55    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK2(X4),sK3(X4)) = X4)),
% 1.36/0.55    introduced(choice_axiom,[])).
% 1.36/0.55  fof(f32,plain,(
% 1.36/0.55    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.36/0.55    inference(rectify,[],[f31])).
% 1.36/0.55  fof(f31,plain,(
% 1.36/0.55    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 1.36/0.55    inference(nnf_transformation,[],[f25])).
% 1.36/0.55  fof(f25,plain,(
% 1.36/0.55    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f11])).
% 1.36/0.55  fof(f11,axiom,(
% 1.36/0.55    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.36/0.55  fof(f214,plain,(
% 1.36/0.55    ~v1_relat_1(k1_xboole_0)),
% 1.36/0.55    inference(resolution,[],[f213,f68])).
% 1.36/0.55  fof(f68,plain,(
% 1.36/0.55    ( ! [X4] : (v1_relat_1(k5_relat_1(sK0,X4)) | ~v1_relat_1(X4)) )),
% 1.36/0.55    inference(resolution,[],[f38,f53])).
% 1.36/0.55  fof(f53,plain,(
% 1.36/0.55    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f27])).
% 1.36/0.55  fof(f27,plain,(
% 1.36/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(flattening,[],[f26])).
% 1.36/0.55  fof(f26,plain,(
% 1.36/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f12])).
% 1.36/0.55  fof(f12,axiom,(
% 1.36/0.55    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.36/0.55  fof(f38,plain,(
% 1.36/0.55    v1_relat_1(sK0)),
% 1.36/0.55    inference(cnf_transformation,[],[f30])).
% 1.36/0.55  fof(f30,plain,(
% 1.36/0.55    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.36/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f29])).
% 1.36/0.55  fof(f29,plain,(
% 1.36/0.55    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.36/0.55    introduced(choice_axiom,[])).
% 1.36/0.55  fof(f19,plain,(
% 1.36/0.55    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f18])).
% 1.36/0.55  fof(f18,negated_conjecture,(
% 1.36/0.55    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.36/0.55    inference(negated_conjecture,[],[f17])).
% 1.36/0.55  fof(f17,conjecture,(
% 1.36/0.55    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 1.36/0.55  fof(f213,plain,(
% 1.36/0.55    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.36/0.55    inference(subsumption_resolution,[],[f212,f164])).
% 1.36/0.55  fof(f164,plain,(
% 1.36/0.55    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 1.36/0.55    inference(trivial_inequality_removal,[],[f157])).
% 1.36/0.55  fof(f157,plain,(
% 1.36/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 1.36/0.55    inference(backward_demodulation,[],[f39,f156])).
% 1.36/0.55  fof(f156,plain,(
% 1.36/0.55    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.36/0.55    inference(subsumption_resolution,[],[f153,f42])).
% 1.36/0.55  fof(f153,plain,(
% 1.36/0.55    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | ~r1_xboole_0(k2_tarski(sK1(k1_xboole_0),X0),k1_xboole_0)) )),
% 1.36/0.55    inference(resolution,[],[f149,f58])).
% 1.36/0.55  fof(f149,plain,(
% 1.36/0.55    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.36/0.55    inference(resolution,[],[f143,f49])).
% 1.36/0.55  fof(f143,plain,(
% 1.36/0.55    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.36/0.55    inference(resolution,[],[f142,f69])).
% 1.36/0.55  fof(f69,plain,(
% 1.36/0.55    ( ! [X5] : (v1_relat_1(k5_relat_1(X5,sK0)) | ~v1_relat_1(X5)) )),
% 1.36/0.55    inference(resolution,[],[f38,f53])).
% 1.36/0.55  fof(f142,plain,(
% 1.36/0.55    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.36/0.55    inference(forward_demodulation,[],[f141,f44])).
% 1.36/0.55  fof(f44,plain,(
% 1.36/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f1])).
% 1.36/0.55  fof(f1,axiom,(
% 1.36/0.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.36/0.55  fof(f141,plain,(
% 1.36/0.55    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.36/0.55    inference(forward_demodulation,[],[f139,f62])).
% 1.36/0.55  fof(f62,plain,(
% 1.36/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.36/0.55    inference(equality_resolution,[],[f55])).
% 1.36/0.55  fof(f55,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f37])).
% 1.36/0.55  fof(f37,plain,(
% 1.36/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.36/0.55    inference(flattening,[],[f36])).
% 1.36/0.55  fof(f36,plain,(
% 1.36/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.36/0.55    inference(nnf_transformation,[],[f8])).
% 1.36/0.55  fof(f8,axiom,(
% 1.36/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.36/0.55  fof(f139,plain,(
% 1.36/0.55    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.36/0.55    inference(superposition,[],[f45,f131])).
% 1.36/0.55  fof(f131,plain,(
% 1.36/0.55    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.36/0.55    inference(subsumption_resolution,[],[f128,f42])).
% 1.36/0.55  fof(f128,plain,(
% 1.36/0.55    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~r1_xboole_0(k2_tarski(sK1(k1_xboole_0),X0),k1_xboole_0)) )),
% 1.36/0.55    inference(resolution,[],[f124,f58])).
% 1.36/0.55  fof(f124,plain,(
% 1.36/0.55    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.36/0.55    inference(resolution,[],[f122,f49])).
% 1.36/0.55  fof(f122,plain,(
% 1.36/0.55    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.36/0.55    inference(forward_demodulation,[],[f121,f40])).
% 1.36/0.55  fof(f40,plain,(
% 1.36/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.36/0.55    inference(cnf_transformation,[],[f16])).
% 1.36/0.55  fof(f16,axiom,(
% 1.36/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.36/0.55  fof(f121,plain,(
% 1.36/0.55    k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~v1_relat_1(k1_xboole_0)),
% 1.36/0.55    inference(subsumption_resolution,[],[f119,f43])).
% 1.36/0.55  fof(f43,plain,(
% 1.36/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f2])).
% 1.36/0.55  fof(f2,axiom,(
% 1.36/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.36/0.55  fof(f119,plain,(
% 1.36/0.55    ~r1_tarski(k1_xboole_0,k1_relat_1(sK0)) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~v1_relat_1(k1_xboole_0)),
% 1.36/0.55    inference(superposition,[],[f65,f41])).
% 1.36/0.55  fof(f41,plain,(
% 1.36/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.36/0.55    inference(cnf_transformation,[],[f16])).
% 1.36/0.55  fof(f65,plain,(
% 1.36/0.55    ( ! [X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(sK0)) | k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,sK0)) | ~v1_relat_1(X1)) )),
% 1.36/0.55    inference(resolution,[],[f38,f46])).
% 1.36/0.55  fof(f46,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f22])).
% 1.36/0.55  fof(f22,plain,(
% 1.36/0.55    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(flattening,[],[f21])).
% 1.36/0.55  fof(f21,plain,(
% 1.36/0.55    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f14])).
% 1.36/0.55  fof(f14,axiom,(
% 1.36/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 1.36/0.55  fof(f45,plain,(
% 1.36/0.55    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f20])).
% 1.36/0.55  fof(f20,plain,(
% 1.36/0.55    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f13])).
% 1.36/0.55  fof(f13,axiom,(
% 1.36/0.55    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 1.36/0.55  fof(f39,plain,(
% 1.36/0.55    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.36/0.55    inference(cnf_transformation,[],[f30])).
% 1.36/0.55  fof(f212,plain,(
% 1.36/0.55    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.36/0.55    inference(forward_demodulation,[],[f211,f44])).
% 1.36/0.55  fof(f211,plain,(
% 1.36/0.55    k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.36/0.55    inference(forward_demodulation,[],[f208,f61])).
% 1.36/0.55  fof(f61,plain,(
% 1.36/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.36/0.55    inference(equality_resolution,[],[f56])).
% 1.36/0.55  fof(f56,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.36/0.55    inference(cnf_transformation,[],[f37])).
% 1.36/0.55  fof(f208,plain,(
% 1.36/0.55    k5_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.36/0.55    inference(superposition,[],[f45,f200])).
% 1.36/0.55  fof(f200,plain,(
% 1.36/0.55    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.36/0.55    inference(subsumption_resolution,[],[f197,f42])).
% 1.36/0.55  fof(f197,plain,(
% 1.36/0.55    ( ! [X0] : (k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~r1_xboole_0(k2_tarski(sK1(k1_xboole_0),X0),k1_xboole_0)) )),
% 1.36/0.55    inference(resolution,[],[f196,f58])).
% 1.36/0.55  fof(f196,plain,(
% 1.36/0.55    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.36/0.55    inference(resolution,[],[f181,f38])).
% 1.36/0.55  fof(f181,plain,(
% 1.36/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | r2_hidden(sK1(k1_xboole_0),k1_xboole_0)) )),
% 1.36/0.55    inference(resolution,[],[f168,f49])).
% 1.36/0.55  fof(f168,plain,(
% 1.36/0.55    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(forward_demodulation,[],[f167,f41])).
% 1.36/0.55  fof(f167,plain,(
% 1.36/0.55    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(forward_demodulation,[],[f162,f156])).
% 1.36/0.55  fof(f162,plain,(
% 1.36/0.55    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | k2_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k2_relat_1(k5_relat_1(X0,k5_relat_1(k1_xboole_0,sK0))) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(backward_demodulation,[],[f140,f156])).
% 1.36/0.55  fof(f140,plain,(
% 1.36/0.55    ( ! [X0] : (k2_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k2_relat_1(k5_relat_1(X0,k5_relat_1(k1_xboole_0,sK0))) | ~v1_relat_1(X0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0))) )),
% 1.36/0.55    inference(subsumption_resolution,[],[f137,f43])).
% 1.36/0.55  fof(f137,plain,(
% 1.36/0.55    ( ! [X0] : (~r1_tarski(k1_xboole_0,k2_relat_1(X0)) | k2_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k2_relat_1(k5_relat_1(X0,k5_relat_1(k1_xboole_0,sK0))) | ~v1_relat_1(X0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0))) )),
% 1.36/0.55    inference(superposition,[],[f47,f131])).
% 1.36/0.55  fof(f47,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f24])).
% 1.36/0.55  fof(f24,plain,(
% 1.36/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(flattening,[],[f23])).
% 1.36/0.55  fof(f23,plain,(
% 1.36/0.55    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f15])).
% 1.36/0.55  fof(f15,axiom,(
% 1.36/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).
% 1.36/0.55  % SZS output end Proof for theBenchmark
% 1.36/0.55  % (32606)------------------------------
% 1.36/0.55  % (32606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (32606)Termination reason: Refutation
% 1.36/0.55  
% 1.36/0.55  % (32606)Memory used [KB]: 1918
% 1.36/0.55  % (32606)Time elapsed: 0.101 s
% 1.36/0.55  % (32606)------------------------------
% 1.36/0.55  % (32606)------------------------------
% 1.36/0.55  % (32597)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.56  % (32582)Success in time 0.19 s
%------------------------------------------------------------------------------
