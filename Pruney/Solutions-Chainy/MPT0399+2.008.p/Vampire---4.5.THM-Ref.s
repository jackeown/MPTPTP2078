%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  38 expanded)
%              Number of leaves         :    9 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 (  81 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f22,f32,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f32,plain,(
    r2_hidden(sK2(k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f20,f31,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),X1)
      | ~ r1_setfam_1(X0,X1)
      | ~ sP3(X0) ) ),
    inference(general_splitting,[],[f25,f26_D])).

fof(f26,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | sP3(X0) ) ),
    inference(cnf_transformation,[],[f26_D])).

fof(f26_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ r2_hidden(X2,X0)
    <=> ~ sP3(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X1),X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(sK2(X1),X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f18])).

fof(f18,plain,(
    ! [X1] :
      ( ? [X3] : r2_hidden(X3,X1)
     => r2_hidden(sK2(X1),X1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] : r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] : ~ r2_hidden(X3,X1)
            & r2_hidden(X2,X0) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f31,plain,(
    sP3(sK0) ),
    inference(unit_resulting_resolution,[],[f29,f26])).

fof(f29,plain,(
    r2_hidden(sK1(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f21,f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 != sK0
    & r1_setfam_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_setfam_1(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK0
      & r1_setfam_1(sK0,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

fof(f20,plain,(
    r1_setfam_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:50:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.43  % (5138)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.44  % (5132)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.45  % (5138)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f22,f32,f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.45    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    r2_hidden(sK2(k1_xboole_0),k1_xboole_0)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f20,f31,f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r2_hidden(sK2(X1),X1) | ~r1_setfam_1(X0,X1) | ~sP3(X0)) )),
% 0.20/0.45    inference(general_splitting,[],[f25,f26_D])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ( ! [X2,X0] : (~r2_hidden(X2,X0) | sP3(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f26_D])).
% 0.20/0.45  fof(f26_D,plain,(
% 0.20/0.45    ( ! [X0] : (( ! [X2] : ~r2_hidden(X2,X0) ) <=> ~sP3(X0)) )),
% 0.20/0.45    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r2_hidden(sK2(X1),X1) | ~r2_hidden(X2,X0) | ~r1_setfam_1(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0,X1] : (! [X2] : (r2_hidden(sK2(X1),X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X1] : (? [X3] : r2_hidden(X3,X1) => r2_hidden(sK2(X1),X1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ! [X0,X1] : (! [X2] : (? [X3] : r2_hidden(X3,X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~r2_hidden(X3,X1) & r2_hidden(X2,X0)))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f7])).
% 0.20/0.45  fof(f7,plain,(
% 0.20/0.45    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.20/0.45    inference(unused_predicate_definition_removal,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    sP3(sK0)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f29,f26])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    r2_hidden(sK1(sK0),sK0)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f21,f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    k1_xboole_0 != sK0),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0)) => (k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,negated_conjecture,(
% 0.20/0.45    ~! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.45    inference(negated_conjecture,[],[f5])).
% 0.20/0.45  fof(f5,conjecture,(
% 0.20/0.45    ! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    r1_setfam_1(sK0,k1_xboole_0)),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    v1_xboole_0(k1_xboole_0)),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    v1_xboole_0(k1_xboole_0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (5138)------------------------------
% 0.20/0.45  % (5138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (5138)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (5138)Memory used [KB]: 10490
% 0.20/0.45  % (5138)Time elapsed: 0.055 s
% 0.20/0.45  % (5138)------------------------------
% 0.20/0.45  % (5138)------------------------------
% 0.20/0.45  % (5126)Success in time 0.094 s
%------------------------------------------------------------------------------
