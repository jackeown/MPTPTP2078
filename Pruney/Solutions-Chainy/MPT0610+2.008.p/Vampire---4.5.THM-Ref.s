%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 130 expanded)
%              Number of leaves         :   13 (  38 expanded)
%              Depth                    :   23
%              Number of atoms          :  163 ( 457 expanded)
%              Number of equality atoms :   39 (  46 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1388,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1387,f30])).

fof(f30,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK0,X1)
          & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(sK0,X1)
        & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_xboole_0(sK0,sK1)
      & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

fof(f1387,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f1386])).

fof(f1386,plain,
    ( r1_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f1383,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f1383,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(X1,sK1),sK0)
      | r1_xboole_0(X1,sK1) ) ),
    inference(resolution,[],[f1380,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1380,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f1278,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1278,plain,(
    r1_xboole_0(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f1277])).

fof(f1277,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f42,f1209])).

fof(f1209,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f1208])).

fof(f1208,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f164,f1203])).

fof(f1203,plain,(
    k1_xboole_0 = k1_relat_1(k3_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f1201,f48])).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f45,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f1201,plain,(
    k1_xboole_0 = k5_xboole_0(k1_relat_1(k3_xboole_0(sK1,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1200,f31])).

fof(f1200,plain,(
    k1_xboole_0 = k5_xboole_0(k1_relat_1(k3_xboole_0(sK1,sK0)),k3_xboole_0(k1_relat_1(k3_xboole_0(sK1,sK0)),k1_xboole_0)) ),
    inference(resolution,[],[f1199,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f44,f36])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f1199,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0(sK1,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1197,f349])).

fof(f349,plain,(
    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(resolution,[],[f347,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f347,plain,(
    r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f346])).

fof(f346,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))
    | r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(resolution,[],[f342,f38])).

fof(f342,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k1_relat_1(sK1),X0),k1_relat_1(sK0))
      | r1_xboole_0(k1_relat_1(sK1),X0) ) ),
    inference(resolution,[],[f229,f37])).

fof(f229,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f39,f29])).

fof(f29,plain,(
    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f1197,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0(sK1,sK0)),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))) ),
    inference(resolution,[],[f1134,f28])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f1134,plain,(
    ! [X181] :
      ( ~ v1_relat_1(X181)
      | r1_tarski(k1_relat_1(k3_xboole_0(X181,sK0)),k3_xboole_0(k1_relat_1(X181),k1_relat_1(sK0))) ) ),
    inference(resolution,[],[f35,f27])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

fof(f164,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_relat_1(k3_xboole_0(sK1,X1))
      | k1_xboole_0 = k3_xboole_0(sK1,X1) ) ),
    inference(resolution,[],[f33,f50])).

fof(f50,plain,(
    ! [X1] : v1_relat_1(k3_xboole_0(sK1,X1)) ),
    inference(resolution,[],[f40,f28])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (21213)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.43  % (21201)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (21213)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f1388,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(subsumption_resolution,[],[f1387,f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21,f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.45    inference(flattening,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.21/0.45    inference(negated_conjecture,[],[f10])).
% 0.21/0.45  fof(f10,conjecture,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).
% 0.21/0.45  fof(f1387,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK1)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f1386])).
% 0.21/0.45  fof(f1386,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)),
% 0.21/0.45    inference(resolution,[],[f1383,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(rectify,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.45  fof(f1383,plain,(
% 0.21/0.45    ( ! [X1] : (~r2_hidden(sK2(X1,sK1),sK0) | r1_xboole_0(X1,sK1)) )),
% 0.21/0.45    inference(resolution,[],[f1380,f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f24])).
% 0.21/0.45  fof(f1380,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.45    inference(resolution,[],[f1278,f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f24])).
% 0.21/0.45  fof(f1278,plain,(
% 0.21/0.45    r1_xboole_0(sK1,sK0)),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f1277])).
% 0.21/0.45  fof(f1277,plain,(
% 0.21/0.45    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,sK0)),
% 0.21/0.45    inference(superposition,[],[f42,f1209])).
% 0.21/0.45  fof(f1209,plain,(
% 0.21/0.45    k1_xboole_0 = k3_xboole_0(sK1,sK0)),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f1208])).
% 0.21/0.45  fof(f1208,plain,(
% 0.21/0.45    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK1,sK0)),
% 0.21/0.45    inference(superposition,[],[f164,f1203])).
% 0.21/0.45  fof(f1203,plain,(
% 0.21/0.45    k1_xboole_0 = k1_relat_1(k3_xboole_0(sK1,sK0))),
% 0.21/0.45    inference(superposition,[],[f1201,f48])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.45    inference(forward_demodulation,[],[f45,f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.45    inference(definition_unfolding,[],[f32,f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.45  fof(f1201,plain,(
% 0.21/0.45    k1_xboole_0 = k5_xboole_0(k1_relat_1(k3_xboole_0(sK1,sK0)),k1_xboole_0)),
% 0.21/0.45    inference(forward_demodulation,[],[f1200,f31])).
% 0.21/0.45  fof(f1200,plain,(
% 0.21/0.45    k1_xboole_0 = k5_xboole_0(k1_relat_1(k3_xboole_0(sK1,sK0)),k3_xboole_0(k1_relat_1(k3_xboole_0(sK1,sK0)),k1_xboole_0))),
% 0.21/0.45    inference(resolution,[],[f1199,f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f44,f36])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.45  fof(f1199,plain,(
% 0.21/0.45    r1_tarski(k1_relat_1(k3_xboole_0(sK1,sK0)),k1_xboole_0)),
% 0.21/0.45    inference(forward_demodulation,[],[f1197,f349])).
% 0.21/0.45  fof(f349,plain,(
% 0.21/0.45    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))),
% 0.21/0.45    inference(resolution,[],[f347,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.45  fof(f347,plain,(
% 0.21/0.45    r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f346])).
% 0.21/0.45  fof(f346,plain,(
% 0.21/0.45    r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) | r1_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))),
% 0.21/0.45    inference(resolution,[],[f342,f38])).
% 0.21/0.45  fof(f342,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(sK2(k1_relat_1(sK1),X0),k1_relat_1(sK0)) | r1_xboole_0(k1_relat_1(sK1),X0)) )),
% 0.21/0.45    inference(resolution,[],[f229,f37])).
% 0.21/0.45  fof(f229,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK0))) )),
% 0.21/0.45    inference(resolution,[],[f39,f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f1197,plain,(
% 0.21/0.45    r1_tarski(k1_relat_1(k3_xboole_0(sK1,sK0)),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)))),
% 0.21/0.45    inference(resolution,[],[f1134,f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    v1_relat_1(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f1134,plain,(
% 0.21/0.45    ( ! [X181] : (~v1_relat_1(X181) | r1_tarski(k1_relat_1(k3_xboole_0(X181,sK0)),k3_xboole_0(k1_relat_1(X181),k1_relat_1(sK0)))) )),
% 0.21/0.45    inference(resolution,[],[f35,f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    v1_relat_1(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).
% 0.21/0.45  fof(f164,plain,(
% 0.21/0.45    ( ! [X1] : (k1_xboole_0 != k1_relat_1(k3_xboole_0(sK1,X1)) | k1_xboole_0 = k3_xboole_0(sK1,X1)) )),
% 0.21/0.45    inference(resolution,[],[f33,f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ( ! [X1] : (v1_relat_1(k3_xboole_0(sK1,X1))) )),
% 0.21/0.45    inference(resolution,[],[f40,f28])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(flattening,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f25])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (21213)------------------------------
% 0.21/0.45  % (21213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (21213)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (21213)Memory used [KB]: 2302
% 0.21/0.45  % (21213)Time elapsed: 0.036 s
% 0.21/0.45  % (21213)------------------------------
% 0.21/0.45  % (21213)------------------------------
% 0.21/0.46  % (21193)Success in time 0.103 s
%------------------------------------------------------------------------------
