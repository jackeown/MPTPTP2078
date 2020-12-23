%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 346 expanded)
%              Number of leaves         :   14 (  83 expanded)
%              Depth                    :   20
%              Number of atoms          :  240 (1254 expanded)
%              Number of equality atoms :   43 ( 243 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f997,plain,(
    $false ),
    inference(resolution,[],[f996,f590])).

fof(f590,plain,(
    ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f589])).

fof(f589,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f39,f588])).

fof(f588,plain,(
    k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f587])).

fof(f587,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f583,f107])).

fof(f107,plain,(
    ! [X6] : k1_xboole_0 = k7_relat_1(k7_relat_1(sK1,X6),k1_xboole_0) ),
    inference(resolution,[],[f98,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f98,plain,(
    ! [X0] : v1_xboole_0(k7_relat_1(k7_relat_1(sK1,X0),k1_xboole_0)) ),
    inference(resolution,[],[f72,f37])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_xboole_0(k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0)) ) ),
    inference(resolution,[],[f68,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_xboole_0(k7_relat_1(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f53,f40])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc16_relat_1)).

fof(f583,plain,
    ( k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(sK1,sK0),k1_xboole_0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(superposition,[],[f579,f531])).

fof(f531,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(resolution,[],[f522,f43])).

fof(f522,plain,
    ( v1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)))
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(resolution,[],[f452,f408])).

fof(f408,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))
      | v1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0))) ) ),
    inference(duplicate_literal_removal,[],[f402])).

fof(f402,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)))
      | ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))
      | v1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0))) ) ),
    inference(resolution,[],[f161,f83])).

% (30643)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f49,f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
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
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

% (30643)Refutation not found, incomplete strategy% (30643)------------------------------
% (30643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30643)Termination reason: Refutation not found, incomplete strategy

% (30643)Memory used [KB]: 10618
% (30643)Time elapsed: 0.116 s
% (30643)------------------------------
% (30643)------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f161,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,X0))),k1_relat_1(sK1))
      | v1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0))) ) ),
    inference(resolution,[],[f150,f46])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))
      | r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f56,f37])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f452,plain,
    ( r1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(resolution,[],[f435,f38])).

fof(f38,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f435,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X1) ) ),
    inference(duplicate_literal_removal,[],[f421])).

fof(f421,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X1)
      | ~ r1_xboole_0(X1,X0)
      | r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X1) ) ),
    inference(resolution,[],[f138,f85])).

fof(f85,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(sK3(X5,X6),X7)
      | ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X5,X6) ) ),
    inference(resolution,[],[f49,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f138,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK3(k1_relat_1(k7_relat_1(sK1,X1)),X2),X1)
      | r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X1)),X2) ) ),
    inference(resolution,[],[f130,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f55,f37])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f579,plain,(
    ! [X1] : k7_relat_1(sK1,X1) = k7_relat_1(k7_relat_1(sK1,X1),k1_relat_1(k7_relat_1(sK1,X1))) ),
    inference(superposition,[],[f446,f411])).

fof(f411,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK1,X0),X1) = k5_relat_1(k6_relat_1(X1),k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f102,f37])).

fof(f102,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(k7_relat_1(X1,X2),X3) = k5_relat_1(k6_relat_1(X3),k7_relat_1(X1,X2)) ) ),
    inference(resolution,[],[f51,f50])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f446,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK1,X0))),k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f70,f37])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(X0,X1))),k7_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f44,f50])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f39,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f996,plain,(
    r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f995,f40])).

fof(f995,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(forward_demodulation,[],[f994,f41])).

fof(f41,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f994,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f984,f588])).

fof(f984,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(k1_relat_1(k7_relat_1(sK1,X9)))
      | r1_xboole_0(k1_relat_1(sK1),X9) ) ),
    inference(resolution,[],[f973,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f973,plain,(
    ! [X1] :
      ( r2_hidden(sK3(k1_relat_1(sK1),X1),k1_relat_1(k7_relat_1(sK1,X1)))
      | r1_xboole_0(k1_relat_1(sK1),X1) ) ),
    inference(duplicate_literal_removal,[],[f967])).

fof(f967,plain,(
    ! [X1] :
      ( r2_hidden(sK3(k1_relat_1(sK1),X1),k1_relat_1(k7_relat_1(sK1,X1)))
      | r1_xboole_0(k1_relat_1(sK1),X1)
      | r1_xboole_0(k1_relat_1(sK1),X1) ) ),
    inference(resolution,[],[f208,f48])).

fof(f208,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK3(k1_relat_1(sK1),X4),X5)
      | r2_hidden(sK3(k1_relat_1(sK1),X4),k1_relat_1(k7_relat_1(sK1,X5)))
      | r1_xboole_0(k1_relat_1(sK1),X4) ) ),
    inference(resolution,[],[f170,f47])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1))) ) ),
    inference(resolution,[],[f57,f37])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:23:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (30646)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.49  % (30659)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.49  % (30655)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.49  % (30642)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (30644)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (30649)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.50  % (30651)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (30653)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (30648)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  % (30650)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (30656)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (30658)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.52  % (30640)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.52  % (30661)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.52  % (30641)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (30649)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f997,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(resolution,[],[f996,f590])).
% 0.21/0.52  fof(f590,plain,(
% 0.21/0.52    ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f589])).
% 0.21/0.52  fof(f589,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.52    inference(backward_demodulation,[],[f39,f588])).
% 0.21/0.52  fof(f588,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f587])).
% 0.21/0.52  fof(f587,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(sK1,sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.52    inference(forward_demodulation,[],[f583,f107])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X6] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK1,X6),k1_xboole_0)) )),
% 0.21/0.52    inference(resolution,[],[f98,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ( ! [X0] : (v1_xboole_0(k7_relat_1(k7_relat_1(sK1,X0),k1_xboole_0))) )),
% 0.21/0.52    inference(resolution,[],[f72,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_xboole_0(k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0))) )),
% 0.21/0.52    inference(resolution,[],[f68,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | v1_xboole_0(k7_relat_1(X0,k1_xboole_0))) )),
% 0.21/0.52    inference(resolution,[],[f53,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | (~v1_xboole_0(X1) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_xboole_0(X1) & v1_relat_1(X0)) => (v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc16_relat_1)).
% 0.21/0.52  fof(f583,plain,(
% 0.21/0.52    k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(sK1,sK0),k1_xboole_0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.52    inference(superposition,[],[f579,f531])).
% 0.21/0.52  fof(f531,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.52    inference(resolution,[],[f522,f43])).
% 0.21/0.52  fof(f522,plain,(
% 0.21/0.52    v1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0))) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.52    inference(resolution,[],[f452,f408])).
% 0.21/0.52  fof(f408,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1)) | v1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f402])).
% 0.21/0.52  fof(f402,plain,(
% 0.21/0.52    ( ! [X0] : (v1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0))) | ~r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1)) | v1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 0.21/0.52    inference(resolution,[],[f161,f83])).
% 0.21/0.52  % (30643)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0),X1) | ~r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(resolution,[],[f49,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.52    inference(rectify,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f5])).
% 0.21/0.53  % (30643)Refutation not found, incomplete strategy% (30643)------------------------------
% 0.21/0.53  % (30643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30643)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30643)Memory used [KB]: 10618
% 0.21/0.53  % (30643)Time elapsed: 0.116 s
% 0.21/0.53  % (30643)------------------------------
% 0.21/0.53  % (30643)------------------------------
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK2(k1_relat_1(k7_relat_1(sK1,X0))),k1_relat_1(sK1)) | v1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 0.21/0.53    inference(resolution,[],[f150,f46])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1))) | r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.21/0.53    inference(resolution,[],[f56,f37])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.21/0.53  fof(f452,plain,(
% 0.21/0.53    r1_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.53    inference(resolution,[],[f435,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f435,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X1)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f421])).
% 0.21/0.53  fof(f421,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X1) | ~r1_xboole_0(X1,X0) | r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X1)) )),
% 0.21/0.53    inference(resolution,[],[f138,f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X6,X7,X5] : (~r2_hidden(sK3(X5,X6),X7) | ~r1_xboole_0(X6,X7) | r1_xboole_0(X5,X6)) )),
% 0.21/0.53    inference(resolution,[],[f49,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    ( ! [X2,X1] : (r2_hidden(sK3(k1_relat_1(k7_relat_1(sK1,X1)),X2),X1) | r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X1)),X2)) )),
% 0.21/0.53    inference(resolution,[],[f130,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1))) | r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f55,f37])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f579,plain,(
% 0.21/0.53    ( ! [X1] : (k7_relat_1(sK1,X1) = k7_relat_1(k7_relat_1(sK1,X1),k1_relat_1(k7_relat_1(sK1,X1)))) )),
% 0.21/0.53    inference(superposition,[],[f446,f411])).
% 0.21/0.53  fof(f411,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK1,X0),X1) = k5_relat_1(k6_relat_1(X1),k7_relat_1(sK1,X0))) )),
% 0.21/0.53    inference(resolution,[],[f102,f37])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ( ! [X2,X3,X1] : (~v1_relat_1(X1) | k7_relat_1(k7_relat_1(X1,X2),X3) = k5_relat_1(k6_relat_1(X3),k7_relat_1(X1,X2))) )),
% 0.21/0.53    inference(resolution,[],[f51,f50])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.53  fof(f446,plain,(
% 0.21/0.53    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK1,X0))),k7_relat_1(sK1,X0))) )),
% 0.21/0.53    inference(resolution,[],[f70,f37])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(X0,X1))),k7_relat_1(X0,X1))) )),
% 0.21/0.53    inference(resolution,[],[f44,f50])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    k1_xboole_0 != k7_relat_1(sK1,sK0) | ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f996,plain,(
% 0.21/0.53    r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.53    inference(resolution,[],[f995,f40])).
% 0.21/0.53  fof(f995,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0) | r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f994,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.53  fof(f994,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.53    inference(superposition,[],[f984,f588])).
% 0.21/0.53  fof(f984,plain,(
% 0.21/0.53    ( ! [X9] : (~v1_xboole_0(k1_relat_1(k7_relat_1(sK1,X9))) | r1_xboole_0(k1_relat_1(sK1),X9)) )),
% 0.21/0.53    inference(resolution,[],[f973,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f973,plain,(
% 0.21/0.53    ( ! [X1] : (r2_hidden(sK3(k1_relat_1(sK1),X1),k1_relat_1(k7_relat_1(sK1,X1))) | r1_xboole_0(k1_relat_1(sK1),X1)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f967])).
% 0.21/0.53  fof(f967,plain,(
% 0.21/0.53    ( ! [X1] : (r2_hidden(sK3(k1_relat_1(sK1),X1),k1_relat_1(k7_relat_1(sK1,X1))) | r1_xboole_0(k1_relat_1(sK1),X1) | r1_xboole_0(k1_relat_1(sK1),X1)) )),
% 0.21/0.53    inference(resolution,[],[f208,f48])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~r2_hidden(sK3(k1_relat_1(sK1),X4),X5) | r2_hidden(sK3(k1_relat_1(sK1),X4),k1_relat_1(k7_relat_1(sK1,X5))) | r1_xboole_0(k1_relat_1(sK1),X4)) )),
% 0.21/0.53    inference(resolution,[],[f170,f47])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,X1) | r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))) )),
% 0.21/0.53    inference(resolution,[],[f57,f37])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (30649)------------------------------
% 0.21/0.53  % (30649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30649)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (30649)Memory used [KB]: 1918
% 0.21/0.53  % (30649)Time elapsed: 0.086 s
% 0.21/0.53  % (30649)------------------------------
% 0.21/0.53  % (30649)------------------------------
% 0.21/0.53  % (30639)Success in time 0.163 s
%------------------------------------------------------------------------------
