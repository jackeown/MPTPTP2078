%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 393 expanded)
%              Number of leaves         :   10 (  99 expanded)
%              Depth                    :   14
%              Number of atoms          :  164 ( 916 expanded)
%              Number of equality atoms :   85 ( 534 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f248,plain,(
    $false ),
    inference(global_subsumption,[],[f176,f246])).

fof(f246,plain,(
    k1_funct_1(sK1,sK0) = sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(backward_demodulation,[],[f242,f240])).

fof(f240,plain,(
    sK0 = sK4(sK1,sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f229,f123])).

fof(f123,plain,(
    ! [X0] :
      ( sK0 = sK4(sK1,X0)
      | ~ sP3(X0,sK1) ) ),
    inference(resolution,[],[f120,f29])).

fof(f29,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f120,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,k1_relat_1(sK1))
      | sK0 = X9 ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X9] :
      ( sK0 = X9
      | sK0 = X9
      | sK0 = X9
      | ~ r2_hidden(X9,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f44,f74])).

fof(f74,plain,(
    ! [X0] :
      ( sP7(X0,sK0,sK0,sK0)
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f63,f52])).

fof(f52,plain,(
    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f23,f50])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | sP7(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP7(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f46,f40])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP7(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP7(X4,X2,X1,X0)
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f229,plain,(
    sP3(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),sK1) ),
    inference(unit_resulting_resolution,[],[f21,f22,f175,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f175,plain,(
    r2_hidden(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f51,f172,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f172,plain,(
    k1_xboole_0 != k2_relat_1(sK1) ),
    inference(superposition,[],[f88,f164])).

fof(f164,plain,(
    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f157,f68])).

fof(f68,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f21,f26])).

fof(f26,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f157,plain,(
    k9_relat_1(sK1,k1_relat_1(sK1)) = k11_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f21,f91])).

fof(f91,plain,(
    ! [X0] :
      ( k11_relat_1(X0,sK0) = k9_relat_1(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f53,f52])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f27,f50])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

% (24663)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (24666)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f88,plain,(
    k1_xboole_0 != k11_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f21,f82,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f82,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f67,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ sP7(X0,sK0,sK0,sK0)
      | r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f64,f52])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | ~ sP7(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP7(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f45,f40])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP7(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X4,X2,X1] : sP7(X4,X2,X1,X4) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( X0 != X4
      | sP7(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f24,f50])).

fof(f24,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f22,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f242,plain,(
    sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = k1_funct_1(sK1,sK4(sK1,sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)))) ),
    inference(unit_resulting_resolution,[],[f229,f30])).

fof(f30,plain,(
    ! [X2,X0] :
      ( k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f176,plain,(
    k1_funct_1(sK1,sK0) != sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f51,f172,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | sK5(X0,X1) != X1 ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:11:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.53  % (24670)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (24678)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (24679)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (24671)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.56  % (24668)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.56  % (24686)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.56  % (24687)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.57  % (24687)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f248,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(global_subsumption,[],[f176,f246])).
% 0.20/0.58  fof(f246,plain,(
% 0.20/0.58    k1_funct_1(sK1,sK0) = sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0))),
% 0.20/0.58    inference(backward_demodulation,[],[f242,f240])).
% 0.20/0.58  fof(f240,plain,(
% 0.20/0.58    sK0 = sK4(sK1,sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)))),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f229,f123])).
% 0.20/0.58  fof(f123,plain,(
% 0.20/0.58    ( ! [X0] : (sK0 = sK4(sK1,X0) | ~sP3(X0,sK1)) )),
% 0.20/0.58    inference(resolution,[],[f120,f29])).
% 0.20/0.58  fof(f29,plain,(
% 0.20/0.58    ( ! [X2,X0] : (r2_hidden(sK4(X0,X2),k1_relat_1(X0)) | ~sP3(X2,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f17])).
% 0.20/0.58  fof(f17,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.58    inference(flattening,[],[f16])).
% 0.20/0.58  fof(f16,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f9])).
% 0.20/0.58  fof(f9,axiom,(
% 0.20/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.58  fof(f120,plain,(
% 0.20/0.58    ( ! [X9] : (~r2_hidden(X9,k1_relat_1(sK1)) | sK0 = X9) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f119])).
% 0.20/0.58  fof(f119,plain,(
% 0.20/0.58    ( ! [X9] : (sK0 = X9 | sK0 = X9 | sK0 = X9 | ~r2_hidden(X9,k1_relat_1(sK1))) )),
% 0.20/0.58    inference(resolution,[],[f44,f74])).
% 0.20/0.58  fof(f74,plain,(
% 0.20/0.58    ( ! [X0] : (sP7(X0,sK0,sK0,sK0) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.20/0.58    inference(superposition,[],[f63,f52])).
% 0.20/0.58  fof(f52,plain,(
% 0.20/0.58    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.20/0.58    inference(definition_unfolding,[],[f23,f50])).
% 0.20/0.58  fof(f50,plain,(
% 0.20/0.58    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f25,f49])).
% 0.20/0.58  fof(f49,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f35,f40])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.58  fof(f35,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f3])).
% 0.20/0.58  fof(f3,axiom,(
% 0.20/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.58  fof(f25,plain,(
% 0.20/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.58  fof(f23,plain,(
% 0.20/0.58    k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.20/0.58    inference(cnf_transformation,[],[f13])).
% 0.20/0.58  fof(f13,plain,(
% 0.20/0.58    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.58    inference(flattening,[],[f12])).
% 0.20/0.58  fof(f12,plain,(
% 0.20/0.58    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.58    inference(ennf_transformation,[],[f11])).
% 0.20/0.58  fof(f11,negated_conjecture,(
% 0.20/0.58    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.58    inference(negated_conjecture,[],[f10])).
% 0.20/0.58  fof(f10,conjecture,(
% 0.20/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.20/0.58  fof(f63,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | sP7(X4,X2,X1,X0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f58])).
% 0.20/0.58  fof(f58,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (sP7(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.20/0.58    inference(definition_unfolding,[],[f46,f40])).
% 0.20/0.58  fof(f46,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (sP7(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.58    inference(cnf_transformation,[],[f20])).
% 0.20/0.58  fof(f20,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.58    inference(ennf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.20/0.58  fof(f44,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X1] : (~sP7(X4,X2,X1,X0) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.20/0.58    inference(cnf_transformation,[],[f20])).
% 0.20/0.58  fof(f229,plain,(
% 0.20/0.58    sP3(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),sK1)),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f21,f22,f175,f60])).
% 0.20/0.58  fof(f60,plain,(
% 0.20/0.58    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | sP3(X2,X0) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f32])).
% 0.20/0.58  fof(f32,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP3(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.58    inference(cnf_transformation,[],[f17])).
% 0.20/0.58  fof(f175,plain,(
% 0.20/0.58    r2_hidden(sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1))),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f51,f172,f55])).
% 0.20/0.58  fof(f55,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK5(X0,X1),X0)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f38,f50])).
% 0.20/0.58  fof(f38,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK5(X0,X1),X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f19])).
% 0.20/0.58  fof(f19,plain,(
% 0.20/0.58    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.20/0.58    inference(ennf_transformation,[],[f5])).
% 0.20/0.58  fof(f5,axiom,(
% 0.20/0.58    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.20/0.58  fof(f172,plain,(
% 0.20/0.58    k1_xboole_0 != k2_relat_1(sK1)),
% 0.20/0.58    inference(superposition,[],[f88,f164])).
% 0.20/0.58  fof(f164,plain,(
% 0.20/0.58    k2_relat_1(sK1) = k11_relat_1(sK1,sK0)),
% 0.20/0.58    inference(forward_demodulation,[],[f157,f68])).
% 0.20/0.58  fof(f68,plain,(
% 0.20/0.58    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f21,f26])).
% 0.20/0.58  fof(f26,plain,(
% 0.20/0.58    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f14])).
% 0.20/0.58  fof(f14,plain,(
% 0.20/0.58    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f7])).
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.58  fof(f157,plain,(
% 0.20/0.58    k9_relat_1(sK1,k1_relat_1(sK1)) = k11_relat_1(sK1,sK0)),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f21,f91])).
% 0.20/0.58  fof(f91,plain,(
% 0.20/0.58    ( ! [X0] : (k11_relat_1(X0,sK0) = k9_relat_1(X0,k1_relat_1(sK1)) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(superposition,[],[f53,f52])).
% 0.20/0.58  fof(f53,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f27,f50])).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f15])).
% 0.20/0.58  fof(f15,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f6])).
% 0.20/0.58  fof(f6,axiom,(
% 0.20/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.20/0.59  % (24663)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.59  % (24666)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.59  fof(f88,plain,(
% 0.20/0.59    k1_xboole_0 != k11_relat_1(sK1,sK0)),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f21,f82,f37])).
% 0.20/0.59  fof(f37,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f18])).
% 0.20/0.59  fof(f18,plain,(
% 0.20/0.59    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.20/0.59    inference(ennf_transformation,[],[f8])).
% 0.20/0.59  fof(f8,axiom,(
% 0.20/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.20/0.59  fof(f82,plain,(
% 0.20/0.59    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f67,f79])).
% 0.20/0.59  fof(f79,plain,(
% 0.20/0.59    ( ! [X0] : (~sP7(X0,sK0,sK0,sK0) | r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.20/0.59    inference(superposition,[],[f64,f52])).
% 0.20/0.59  fof(f64,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | ~sP7(X4,X2,X1,X0)) )),
% 0.20/0.59    inference(equality_resolution,[],[f59])).
% 0.20/0.59  fof(f59,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X3,X1] : (~sP7(X4,X2,X1,X0) | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.20/0.59    inference(definition_unfolding,[],[f45,f40])).
% 0.20/0.59  fof(f45,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X3,X1] : (~sP7(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.59    inference(cnf_transformation,[],[f20])).
% 0.20/0.59  fof(f67,plain,(
% 0.20/0.59    ( ! [X4,X2,X1] : (sP7(X4,X2,X1,X4)) )),
% 0.20/0.59    inference(equality_resolution,[],[f41])).
% 0.20/0.59  fof(f41,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X1] : (X0 != X4 | sP7(X4,X2,X1,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f20])).
% 0.20/0.59  fof(f51,plain,(
% 0.20/0.59    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.20/0.59    inference(definition_unfolding,[],[f24,f50])).
% 0.20/0.59  fof(f24,plain,(
% 0.20/0.59    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.20/0.59    inference(cnf_transformation,[],[f13])).
% 0.20/0.59  fof(f22,plain,(
% 0.20/0.59    v1_funct_1(sK1)),
% 0.20/0.59    inference(cnf_transformation,[],[f13])).
% 0.20/0.59  fof(f21,plain,(
% 0.20/0.59    v1_relat_1(sK1)),
% 0.20/0.59    inference(cnf_transformation,[],[f13])).
% 0.20/0.59  fof(f242,plain,(
% 0.20/0.59    sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) = k1_funct_1(sK1,sK4(sK1,sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0))))),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f229,f30])).
% 0.20/0.59  fof(f30,plain,(
% 0.20/0.59    ( ! [X2,X0] : (k1_funct_1(X0,sK4(X0,X2)) = X2 | ~sP3(X2,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f17])).
% 0.20/0.59  fof(f176,plain,(
% 0.20/0.59    k1_funct_1(sK1,sK0) != sK5(k2_relat_1(sK1),k1_funct_1(sK1,sK0))),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f51,f172,f54])).
% 0.20/0.59  fof(f54,plain,(
% 0.20/0.59    ( ! [X0,X1] : (sK5(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 0.20/0.59    inference(definition_unfolding,[],[f39,f50])).
% 0.20/0.59  fof(f39,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | sK5(X0,X1) != X1) )),
% 0.20/0.59    inference(cnf_transformation,[],[f19])).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (24687)------------------------------
% 0.20/0.59  % (24687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (24687)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (24687)Memory used [KB]: 6396
% 0.20/0.59  % (24687)Time elapsed: 0.158 s
% 0.20/0.59  % (24687)------------------------------
% 0.20/0.59  % (24687)------------------------------
% 0.20/0.59  % (24665)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.59  % (24684)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.59  % (24683)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.59  % (24676)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.59  % (24662)Success in time 0.236 s
%------------------------------------------------------------------------------
