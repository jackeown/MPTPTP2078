%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 114 expanded)
%              Number of leaves         :    8 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 ( 371 expanded)
%              Number of equality atoms :   30 ( 120 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f20,f144,f33,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ sQ3_eqProxy(k1_xboole_0,k9_relat_1(X1,X0))
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f27,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f33,plain,(
    sQ3_eqProxy(k1_xboole_0,k9_relat_1(sK1,sK0)) ),
    inference(equality_proxy_replacement,[],[f23,f32])).

fof(f23,plain,(
    k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & k1_xboole_0 != sK0
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k9_relat_1(X1,X0)
        & r1_tarski(X0,k1_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k9_relat_1(sK1,sK0)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & k1_xboole_0 != sK0
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
            & r1_tarski(X0,k1_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

fof(f144,plain,(
    ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f129,f128,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
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

fof(f128,plain,(
    r2_hidden(sK2(sK0,k1_relat_1(sK1)),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f122,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f122,plain,(
    ~ r1_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f76,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | sQ3_eqProxy(k4_xboole_0(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f29,f32])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f76,plain,(
    ~ sQ3_eqProxy(k4_xboole_0(sK0,k1_relat_1(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f34,f58,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ3_eqProxy(X1,X2)
      | ~ sQ3_eqProxy(X0,X1)
      | sQ3_eqProxy(X0,X2) ) ),
    inference(equality_proxy_axiom,[],[f32])).

fof(f58,plain,(
    sQ3_eqProxy(k1_xboole_0,k4_xboole_0(sK0,k1_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f57,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ sQ3_eqProxy(X0,X1)
      | sQ3_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f32])).

fof(f57,plain,(
    sQ3_eqProxy(k4_xboole_0(sK0,k1_relat_1(sK1)),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f22,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | sQ3_eqProxy(k4_xboole_0(X0,X1),k1_xboole_0) ) ),
    inference(equality_proxy_replacement,[],[f31,f32])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f22,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    ~ sQ3_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f21,f32])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f129,plain,(
    r2_hidden(sK2(sK0,k1_relat_1(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f122,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:56:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.40  % (31323)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.40  % (31323)Refutation not found, incomplete strategy% (31323)------------------------------
% 0.21/0.40  % (31323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.40  % (31323)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.40  
% 0.21/0.40  % (31323)Memory used [KB]: 1535
% 0.21/0.40  % (31323)Time elapsed: 0.003 s
% 0.21/0.40  % (31323)------------------------------
% 0.21/0.40  % (31323)------------------------------
% 0.21/0.43  % (31324)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.44  % (31324)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f234,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f20,f144,f33,f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~sQ3_eqProxy(k1_xboole_0,k9_relat_1(X1,X0)) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(equality_proxy_replacement,[],[f27,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.44    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(nnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    sQ3_eqProxy(k1_xboole_0,k9_relat_1(sK1,sK0))),
% 0.21/0.44    inference(equality_proxy_replacement,[],[f23,f32])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    k1_xboole_0 = k9_relat_1(sK1,sK0) & r1_tarski(sK0,k1_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k9_relat_1(sK1,sK0) & r1_tarski(sK0,k1_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.44    inference(negated_conjecture,[],[f5])).
% 0.21/0.44  fof(f5,conjecture,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).
% 0.21/0.44  fof(f144,plain,(
% 0.21/0.44    ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f129,f128,f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(rectify,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.44  fof(f128,plain,(
% 0.21/0.44    r2_hidden(sK2(sK0,k1_relat_1(sK1)),k1_relat_1(sK1))),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f122,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    ~r1_xboole_0(sK0,k1_relat_1(sK1))),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f76,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | sQ3_eqProxy(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.44    inference(equality_proxy_replacement,[],[f29,f32])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(nnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    ~sQ3_eqProxy(k4_xboole_0(sK0,k1_relat_1(sK1)),sK0)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f34,f58,f50])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~sQ3_eqProxy(X1,X2) | ~sQ3_eqProxy(X0,X1) | sQ3_eqProxy(X0,X2)) )),
% 0.21/0.44    inference(equality_proxy_axiom,[],[f32])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    sQ3_eqProxy(k1_xboole_0,k4_xboole_0(sK0,k1_relat_1(sK1)))),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f57,f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~sQ3_eqProxy(X0,X1) | sQ3_eqProxy(X1,X0)) )),
% 0.21/0.44    inference(equality_proxy_axiom,[],[f32])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    sQ3_eqProxy(k4_xboole_0(sK0,k1_relat_1(sK1)),k1_xboole_0)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f22,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | sQ3_eqProxy(k4_xboole_0(X0,X1),k1_xboole_0)) )),
% 0.21/0.44    inference(equality_proxy_replacement,[],[f31,f32])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.44    inference(unused_predicate_definition_removal,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ~sQ3_eqProxy(k1_xboole_0,sK0)),
% 0.21/0.44    inference(equality_proxy_replacement,[],[f21,f32])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    k1_xboole_0 != sK0),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f129,plain,(
% 0.21/0.44    r2_hidden(sK2(sK0,k1_relat_1(sK1)),sK0)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f122,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    v1_relat_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (31324)------------------------------
% 0.21/0.44  % (31324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (31324)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (31324)Memory used [KB]: 10618
% 0.21/0.44  % (31324)Time elapsed: 0.007 s
% 0.21/0.44  % (31324)------------------------------
% 0.21/0.44  % (31324)------------------------------
% 0.21/0.44  % (31309)Success in time 0.091 s
%------------------------------------------------------------------------------
