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
% DateTime   : Thu Dec  3 12:47:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 296 expanded)
%              Number of leaves         :   10 (  78 expanded)
%              Depth                    :   19
%              Number of atoms          :  232 (1932 expanded)
%              Number of equality atoms :    8 (  44 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (6174)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (6153)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (6171)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f301,plain,(
    $false ),
    inference(subsumption_resolution,[],[f300,f227])).

fof(f227,plain,(
    ! [X1] : v1_relat_1(k3_xboole_0(sK1,X1)) ),
    inference(superposition,[],[f214,f153])).

fof(f153,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(k3_xboole_0(X12,X13),X12) ),
    inference(resolution,[],[f148,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f16])).

fof(f16,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f148,plain,(
    ! [X0,X1] : sP0(X0,k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( sP0(X0,k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))
      | sP0(X0,k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f61,f84])).

fof(f84,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK3(X10,X11,X11),X10)
      | sP0(X10,X11,X11) ) ),
    inference(subsumption_resolution,[],[f79,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X0)
              & r2_hidden(sK3(X0,X1,X2),X1) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X0)
            & r2_hidden(sK3(X0,X1,X2),X1) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f79,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK3(X10,X11,X11),X10)
      | ~ r2_hidden(sK3(X10,X11,X11),X11)
      | sP0(X10,X11,X11) ) ),
    inference(duplicate_literal_removal,[],[f76])).

% (6171)Refutation not found, incomplete strategy% (6171)------------------------------
% (6171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6171)Termination reason: Refutation not found, incomplete strategy

% (6171)Memory used [KB]: 1663
% (6171)Time elapsed: 0.115 s
% (6171)------------------------------
% (6171)------------------------------
fof(f76,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK3(X10,X11,X11),X10)
      | ~ r2_hidden(sK3(X10,X11,X11),X11)
      | sP0(X10,X11,X11)
      | sP0(X10,X11,X11) ) ),
    inference(resolution,[],[f42,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X1),X1)
      | sP0(X0,X1,X1) ) ),
    inference(factoring,[],[f40])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X1)
      | sP0(X0,k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f59,f45])).

fof(f45,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ sP0(X11,X10,X9)
      | r2_hidden(sK3(X8,X9,X9),X10)
      | sP0(X8,X9,X9) ) ),
    inference(resolution,[],[f56,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f214,plain,(
    ! [X0] : v1_relat_1(k3_xboole_0(X0,sK1)) ),
    inference(resolution,[],[f197,f27])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f10,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,X1)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,X1)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

fof(f197,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | v1_relat_1(k3_xboole_0(X3,X2)) ) ),
    inference(superposition,[],[f35,f180])).

fof(f180,plain,(
    ! [X12,X13] : k3_xboole_0(X13,X12) = k3_xboole_0(X12,k3_xboole_0(X13,X12)) ),
    inference(resolution,[],[f175,f44])).

fof(f175,plain,(
    ! [X0,X1] : sP0(k3_xboole_0(X0,X1),X1,k3_xboole_0(X0,X1)) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( sP0(k3_xboole_0(X0,X1),X1,k3_xboole_0(X0,X1))
      | sP0(k3_xboole_0(X0,X1),X1,k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f118,f85])).

fof(f85,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(sK3(X12,X13,X12),X13)
      | sP0(X12,X13,X12) ) ),
    inference(subsumption_resolution,[],[f78,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(sK3(X12,X13,X12),X12)
      | ~ r2_hidden(sK3(X12,X13,X12),X13)
      | sP0(X12,X13,X12) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(sK3(X12,X13,X12),X12)
      | ~ r2_hidden(sK3(X12,X13,X12),X13)
      | sP0(X12,X13,X12)
      | sP0(X12,X13,X12) ) ),
    inference(resolution,[],[f42,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | sP0(X0,X1,X0) ) ),
    inference(factoring,[],[f41])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(k3_xboole_0(X0,X1),X2,k3_xboole_0(X0,X1)),X1)
      | sP0(k3_xboole_0(X0,X1),X2,k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f70,f45])).

% (6154)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f70,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ sP0(X6,X7,X4)
      | r2_hidden(sK3(X4,X5,X4),X6)
      | sP0(X4,X5,X4) ) ),
    inference(resolution,[],[f68,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f300,plain,(
    ~ v1_relat_1(k3_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f299,f27])).

fof(f299,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f298,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f298,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f217,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f217,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f209,f215])).

fof(f215,plain,(
    ! [X1] : v1_relat_1(k3_xboole_0(X1,sK2)) ),
    inference(resolution,[],[f197,f28])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f209,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK1))
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f49,f196])).

fof(f196,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f32,f180])).

fof(f49,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK1))
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f48,f28])).

fof(f48,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK1))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f47,f31])).

fof(f47,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK1)) ),
    inference(resolution,[],[f36,f29])).

fof(f29,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK2))) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (6151)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (6150)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (6162)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (6159)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (6170)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (6170)Refutation not found, incomplete strategy% (6170)------------------------------
% 0.20/0.52  % (6170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (6170)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (6170)Memory used [KB]: 10746
% 0.20/0.52  % (6170)Time elapsed: 0.114 s
% 0.20/0.52  % (6170)------------------------------
% 0.20/0.52  % (6170)------------------------------
% 0.20/0.52  % (6164)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (6157)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (6176)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (6156)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (6157)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (6167)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (6152)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (6167)Refutation not found, incomplete strategy% (6167)------------------------------
% 0.20/0.54  % (6167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6167)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6167)Memory used [KB]: 10618
% 0.20/0.54  % (6167)Time elapsed: 0.123 s
% 0.20/0.54  % (6167)------------------------------
% 0.20/0.54  % (6167)------------------------------
% 0.20/0.54  % (6172)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (6152)Refutation not found, incomplete strategy% (6152)------------------------------
% 0.20/0.54  % (6152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6152)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6152)Memory used [KB]: 10618
% 0.20/0.54  % (6152)Time elapsed: 0.122 s
% 0.20/0.54  % (6152)------------------------------
% 0.20/0.54  % (6152)------------------------------
% 1.48/0.54  % SZS output start Proof for theBenchmark
% 1.48/0.55  % (6174)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.48/0.55  % (6153)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.48/0.55  % (6171)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.48/0.55  fof(f301,plain,(
% 1.48/0.55    $false),
% 1.48/0.55    inference(subsumption_resolution,[],[f300,f227])).
% 1.48/0.55  fof(f227,plain,(
% 1.48/0.55    ( ! [X1] : (v1_relat_1(k3_xboole_0(sK1,X1))) )),
% 1.48/0.55    inference(superposition,[],[f214,f153])).
% 1.48/0.55  fof(f153,plain,(
% 1.48/0.55    ( ! [X12,X13] : (k3_xboole_0(X12,X13) = k3_xboole_0(k3_xboole_0(X12,X13),X12)) )),
% 1.48/0.55    inference(resolution,[],[f148,f44])).
% 1.48/0.55  fof(f44,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.48/0.55    inference(cnf_transformation,[],[f26])).
% 1.48/0.55  fof(f26,plain,(
% 1.48/0.55    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.48/0.55    inference(nnf_transformation,[],[f17])).
% 1.48/0.55  fof(f17,plain,(
% 1.48/0.55    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.48/0.55    inference(definition_folding,[],[f1,f16])).
% 1.48/0.55  fof(f16,plain,(
% 1.48/0.55    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.48/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.48/0.55  fof(f1,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.48/0.55  fof(f148,plain,(
% 1.48/0.55    ( ! [X0,X1] : (sP0(X0,k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.48/0.55    inference(duplicate_literal_removal,[],[f142])).
% 1.48/0.55  fof(f142,plain,(
% 1.48/0.55    ( ! [X0,X1] : (sP0(X0,k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) | sP0(X0,k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.48/0.55    inference(resolution,[],[f61,f84])).
% 1.48/0.55  fof(f84,plain,(
% 1.48/0.55    ( ! [X10,X11] : (~r2_hidden(sK3(X10,X11,X11),X10) | sP0(X10,X11,X11)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f79,f40])).
% 1.48/0.55  fof(f40,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f25,plain,(
% 1.48/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.48/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 1.48/0.55  fof(f24,plain,(
% 1.48/0.55    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.48/0.55    introduced(choice_axiom,[])).
% 1.48/0.55  fof(f23,plain,(
% 1.48/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.48/0.55    inference(rectify,[],[f22])).
% 1.48/0.55  fof(f22,plain,(
% 1.48/0.55    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.48/0.55    inference(flattening,[],[f21])).
% 1.48/0.55  fof(f21,plain,(
% 1.48/0.55    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.48/0.55    inference(nnf_transformation,[],[f16])).
% 1.48/0.55  fof(f79,plain,(
% 1.48/0.55    ( ! [X10,X11] : (~r2_hidden(sK3(X10,X11,X11),X10) | ~r2_hidden(sK3(X10,X11,X11),X11) | sP0(X10,X11,X11)) )),
% 1.48/0.55    inference(duplicate_literal_removal,[],[f76])).
% 1.48/0.55  % (6171)Refutation not found, incomplete strategy% (6171)------------------------------
% 1.48/0.55  % (6171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (6171)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (6171)Memory used [KB]: 1663
% 1.48/0.55  % (6171)Time elapsed: 0.115 s
% 1.48/0.55  % (6171)------------------------------
% 1.48/0.55  % (6171)------------------------------
% 1.48/0.55  fof(f76,plain,(
% 1.48/0.55    ( ! [X10,X11] : (~r2_hidden(sK3(X10,X11,X11),X10) | ~r2_hidden(sK3(X10,X11,X11),X11) | sP0(X10,X11,X11) | sP0(X10,X11,X11)) )),
% 1.48/0.55    inference(resolution,[],[f42,f56])).
% 1.48/0.55  fof(f56,plain,(
% 1.48/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X1) | sP0(X0,X1,X1)) )),
% 1.48/0.55    inference(factoring,[],[f40])).
% 1.48/0.55  fof(f42,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f61,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X1) | sP0(X0,k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))) )),
% 1.48/0.55    inference(resolution,[],[f59,f45])).
% 1.48/0.55  fof(f45,plain,(
% 1.48/0.55    ( ! [X0,X1] : (sP0(X1,X0,k3_xboole_0(X0,X1))) )),
% 1.48/0.55    inference(equality_resolution,[],[f43])).
% 1.48/0.55  fof(f43,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.48/0.55    inference(cnf_transformation,[],[f26])).
% 1.48/0.55  fof(f59,plain,(
% 1.48/0.55    ( ! [X10,X8,X11,X9] : (~sP0(X11,X10,X9) | r2_hidden(sK3(X8,X9,X9),X10) | sP0(X8,X9,X9)) )),
% 1.48/0.55    inference(resolution,[],[f56,f37])).
% 1.48/0.55  fof(f37,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~sP0(X0,X1,X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f214,plain,(
% 1.48/0.55    ( ! [X0] : (v1_relat_1(k3_xboole_0(X0,sK1))) )),
% 1.48/0.55    inference(resolution,[],[f197,f27])).
% 1.48/0.55  fof(f27,plain,(
% 1.48/0.55    v1_relat_1(sK1)),
% 1.48/0.55    inference(cnf_transformation,[],[f20])).
% 1.48/0.55  fof(f20,plain,(
% 1.48/0.55    (~r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 1.48/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f10,f19,f18])).
% 1.48/0.55  fof(f18,plain,(
% 1.48/0.55    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK1,X1)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK1))),
% 1.48/0.55    introduced(choice_axiom,[])).
% 1.48/0.55  fof(f19,plain,(
% 1.48/0.55    ? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK1,X1)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK2))) & v1_relat_1(sK2))),
% 1.48/0.55    introduced(choice_axiom,[])).
% 1.48/0.55  fof(f10,plain,(
% 1.48/0.55    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.48/0.55    inference(ennf_transformation,[],[f9])).
% 1.48/0.55  fof(f9,negated_conjecture,(
% 1.48/0.55    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 1.48/0.55    inference(negated_conjecture,[],[f8])).
% 1.48/0.55  fof(f8,conjecture,(
% 1.48/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).
% 1.48/0.55  fof(f197,plain,(
% 1.48/0.55    ( ! [X2,X3] : (~v1_relat_1(X2) | v1_relat_1(k3_xboole_0(X3,X2))) )),
% 1.48/0.55    inference(superposition,[],[f35,f180])).
% 1.48/0.55  fof(f180,plain,(
% 1.48/0.55    ( ! [X12,X13] : (k3_xboole_0(X13,X12) = k3_xboole_0(X12,k3_xboole_0(X13,X12))) )),
% 1.48/0.55    inference(resolution,[],[f175,f44])).
% 1.48/0.55  fof(f175,plain,(
% 1.48/0.55    ( ! [X0,X1] : (sP0(k3_xboole_0(X0,X1),X1,k3_xboole_0(X0,X1))) )),
% 1.48/0.55    inference(duplicate_literal_removal,[],[f168])).
% 1.48/0.55  fof(f168,plain,(
% 1.48/0.55    ( ! [X0,X1] : (sP0(k3_xboole_0(X0,X1),X1,k3_xboole_0(X0,X1)) | sP0(k3_xboole_0(X0,X1),X1,k3_xboole_0(X0,X1))) )),
% 1.48/0.55    inference(resolution,[],[f118,f85])).
% 1.48/0.55  fof(f85,plain,(
% 1.48/0.55    ( ! [X12,X13] : (~r2_hidden(sK3(X12,X13,X12),X13) | sP0(X12,X13,X12)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f78,f41])).
% 1.48/0.55  fof(f41,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f78,plain,(
% 1.48/0.55    ( ! [X12,X13] : (~r2_hidden(sK3(X12,X13,X12),X12) | ~r2_hidden(sK3(X12,X13,X12),X13) | sP0(X12,X13,X12)) )),
% 1.48/0.55    inference(duplicate_literal_removal,[],[f77])).
% 1.48/0.55  fof(f77,plain,(
% 1.48/0.55    ( ! [X12,X13] : (~r2_hidden(sK3(X12,X13,X12),X12) | ~r2_hidden(sK3(X12,X13,X12),X13) | sP0(X12,X13,X12) | sP0(X12,X13,X12)) )),
% 1.48/0.55    inference(resolution,[],[f42,f68])).
% 1.48/0.55  fof(f68,plain,(
% 1.48/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | sP0(X0,X1,X0)) )),
% 1.48/0.55    inference(factoring,[],[f41])).
% 1.48/0.55  fof(f118,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK3(k3_xboole_0(X0,X1),X2,k3_xboole_0(X0,X1)),X1) | sP0(k3_xboole_0(X0,X1),X2,k3_xboole_0(X0,X1))) )),
% 1.48/0.55    inference(resolution,[],[f70,f45])).
% 1.48/0.55  % (6154)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.48/0.55  fof(f70,plain,(
% 1.48/0.55    ( ! [X6,X4,X7,X5] : (~sP0(X6,X7,X4) | r2_hidden(sK3(X4,X5,X4),X6) | sP0(X4,X5,X4)) )),
% 1.48/0.55    inference(resolution,[],[f68,f38])).
% 1.48/0.55  fof(f38,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~sP0(X0,X1,X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f25])).
% 1.48/0.55  fof(f35,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f13])).
% 1.48/0.55  fof(f13,plain,(
% 1.48/0.55    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.48/0.55    inference(ennf_transformation,[],[f6])).
% 1.48/0.55  fof(f6,axiom,(
% 1.48/0.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 1.48/0.55  fof(f300,plain,(
% 1.48/0.55    ~v1_relat_1(k3_xboole_0(sK1,sK2))),
% 1.48/0.55    inference(subsumption_resolution,[],[f299,f27])).
% 1.48/0.55  fof(f299,plain,(
% 1.48/0.55    ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK1,sK2))),
% 1.48/0.55    inference(subsumption_resolution,[],[f298,f32])).
% 1.48/0.55  fof(f32,plain,(
% 1.48/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f2])).
% 1.48/0.55  fof(f2,axiom,(
% 1.48/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.48/0.55  fof(f298,plain,(
% 1.48/0.55    ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK1,sK2))),
% 1.48/0.55    inference(resolution,[],[f217,f31])).
% 1.48/0.55  fof(f31,plain,(
% 1.48/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f12])).
% 1.48/0.55  fof(f12,plain,(
% 1.48/0.55    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.55    inference(flattening,[],[f11])).
% 1.48/0.55  fof(f11,plain,(
% 1.48/0.55    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.48/0.55    inference(ennf_transformation,[],[f7])).
% 1.48/0.55  fof(f7,axiom,(
% 1.48/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.48/0.55  fof(f217,plain,(
% 1.48/0.55    ~r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK1))),
% 1.48/0.55    inference(subsumption_resolution,[],[f209,f215])).
% 1.48/0.55  fof(f215,plain,(
% 1.48/0.55    ( ! [X1] : (v1_relat_1(k3_xboole_0(X1,sK2))) )),
% 1.48/0.55    inference(resolution,[],[f197,f28])).
% 1.48/0.55  fof(f28,plain,(
% 1.48/0.55    v1_relat_1(sK2)),
% 1.48/0.55    inference(cnf_transformation,[],[f20])).
% 1.48/0.55  fof(f209,plain,(
% 1.48/0.55    ~r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK1)) | ~v1_relat_1(k3_xboole_0(sK1,sK2))),
% 1.48/0.55    inference(subsumption_resolution,[],[f49,f196])).
% 1.48/0.55  fof(f196,plain,(
% 1.48/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 1.48/0.55    inference(superposition,[],[f32,f180])).
% 1.48/0.55  fof(f49,plain,(
% 1.48/0.55    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK1)) | ~v1_relat_1(k3_xboole_0(sK1,sK2))),
% 1.48/0.55    inference(subsumption_resolution,[],[f48,f28])).
% 1.48/0.55  fof(f48,plain,(
% 1.48/0.55    ~r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK1)) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k3_xboole_0(sK1,sK2))),
% 1.48/0.55    inference(resolution,[],[f47,f31])).
% 1.48/0.55  fof(f47,plain,(
% 1.48/0.55    ~r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK2)) | ~r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k2_relat_1(sK1))),
% 1.48/0.55    inference(resolution,[],[f36,f29])).
% 1.48/0.55  fof(f29,plain,(
% 1.48/0.55    ~r1_tarski(k2_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(sK2)))),
% 1.48/0.55    inference(cnf_transformation,[],[f20])).
% 1.48/0.55  fof(f36,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f15])).
% 1.48/0.55  fof(f15,plain,(
% 1.48/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.48/0.55    inference(flattening,[],[f14])).
% 1.48/0.55  fof(f14,plain,(
% 1.48/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.48/0.55    inference(ennf_transformation,[],[f3])).
% 1.48/0.55  fof(f3,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.48/0.55  % SZS output end Proof for theBenchmark
% 1.48/0.55  % (6157)------------------------------
% 1.48/0.55  % (6157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (6157)Termination reason: Refutation
% 1.48/0.55  
% 1.48/0.55  % (6157)Memory used [KB]: 6396
% 1.48/0.55  % (6157)Time elapsed: 0.111 s
% 1.48/0.55  % (6157)------------------------------
% 1.48/0.55  % (6157)------------------------------
% 1.48/0.55  % (6149)Success in time 0.195 s
%------------------------------------------------------------------------------
