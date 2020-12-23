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
% DateTime   : Thu Dec  3 12:58:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 170 expanded)
%              Number of leaves         :   13 (  53 expanded)
%              Depth                    :   17
%              Number of atoms          :  153 ( 448 expanded)
%              Number of equality atoms :   57 ( 236 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f54,f157,f166,f173])).

fof(f173,plain,
    ( spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f168,f41])).

fof(f41,plain,
    ( sK3 != k2_mcart_1(sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_2
  <=> sK3 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f168,plain,
    ( sK3 = k2_mcart_1(sK0)
    | ~ spl4_4 ),
    inference(superposition,[],[f21,f152])).

fof(f152,plain,
    ( sK3 = k1_mcart_1(k4_tarski(k2_mcart_1(sK0),sK1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl4_4
  <=> sK3 = k1_mcart_1(k4_tarski(k2_mcart_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f21,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f166,plain,
    ( spl4_3
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f161,f46])).

fof(f46,plain,
    ( sK2 != k2_mcart_1(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl4_3
  <=> sK2 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f161,plain,
    ( sK2 = k2_mcart_1(sK0)
    | ~ spl4_5 ),
    inference(superposition,[],[f21,f156])).

fof(f156,plain,
    ( sK2 = k1_mcart_1(k4_tarski(k2_mcart_1(sK0),sK1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl4_5
  <=> sK2 = k1_mcart_1(k4_tarski(k2_mcart_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f157,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f142,f154,f150])).

fof(f142,plain,
    ( sK2 = k1_mcart_1(k4_tarski(k2_mcart_1(sK0),sK1))
    | sK3 = k1_mcart_1(k4_tarski(k2_mcart_1(sK0),sK1)) ),
    inference(resolution,[],[f139,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
      | k1_mcart_1(X0) = X1
      | k1_mcart_1(X0) = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) )
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

fof(f139,plain,(
    r2_hidden(k4_tarski(k2_mcart_1(sK0),sK1),k2_zfmisc_1(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1))) ),
    inference(resolution,[],[f131,f56])).

fof(f56,plain,(
    r2_hidden(sK1,k2_tarski(sK1,sK1)) ),
    inference(resolution,[],[f55,f30])).

fof(f30,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK1),k2_tarski(sK2,sK3))) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f17,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ( sK3 != k2_mcart_1(sK0)
        & sK2 != k2_mcart_1(sK0) )
      | sK1 != k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ( k2_mcart_1(X0) != X3
            & k2_mcart_1(X0) != X2 )
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) )
   => ( ( ( sK3 != k2_mcart_1(sK0)
          & sK2 != k2_mcart_1(sK0) )
        | sK1 != k1_mcart_1(sK0) )
      & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) != X3
          & k2_mcart_1(X0) != X2 )
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
       => ( ( k2_mcart_1(X0) = X3
            | k2_mcart_1(X0) = X2 )
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK1,X0) ) ),
    inference(superposition,[],[f23,f50])).

fof(f50,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f32,f30])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f25,f20])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(k2_mcart_1(sK0),X0),k2_zfmisc_1(k2_tarski(sK2,sK3),X1)) ) ),
    inference(resolution,[],[f117,f74])).

fof(f74,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) ) ),
    inference(forward_demodulation,[],[f73,f21])).

fof(f73,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1) ) ),
    inference(forward_demodulation,[],[f33,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(k2_mcart_1(k4_tarski(X3,X4)),X2)
      | ~ r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ! [X3,X4] : k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ! [X3,X4] : k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
     => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).

fof(f117,plain,(
    r2_hidden(k2_mcart_1(sK0),k2_tarski(sK2,sK3)) ),
    inference(resolution,[],[f114,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X3,X2))
      | r2_hidden(X1,X2) ) ),
    inference(superposition,[],[f24,f22])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f114,plain,(
    r2_hidden(k4_tarski(sK1,k2_mcart_1(sK0)),k2_zfmisc_1(k2_tarski(sK1,sK1),k2_tarski(sK2,sK3))) ),
    inference(resolution,[],[f84,f30])).

fof(f84,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X5,X4))
      | r2_hidden(k4_tarski(sK1,k2_mcart_1(X3)),k2_zfmisc_1(k2_tarski(sK1,sK1),X4)) ) ),
    inference(resolution,[],[f78,f24])).

fof(f78,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | r2_hidden(k4_tarski(sK1,X12),k2_zfmisc_1(k2_tarski(sK1,sK1),X13)) ) ),
    inference(resolution,[],[f74,f56])).

fof(f54,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f50,f37])).

fof(f37,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl4_1
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f47,plain,
    ( ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f18,f44,f35])).

fof(f18,plain,
    ( sK2 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f19,f39,f35])).

fof(f19,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:20:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (25023)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (25023)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (25042)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (25034)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f174,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f42,f47,f54,f157,f166,f173])).
% 0.21/0.55  fof(f173,plain,(
% 0.21/0.55    spl4_2 | ~spl4_4),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f172])).
% 0.21/0.55  fof(f172,plain,(
% 0.21/0.55    $false | (spl4_2 | ~spl4_4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f168,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    sK3 != k2_mcart_1(sK0) | spl4_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    spl4_2 <=> sK3 = k2_mcart_1(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.55  fof(f168,plain,(
% 0.21/0.55    sK3 = k2_mcart_1(sK0) | ~spl4_4),
% 0.21/0.55    inference(superposition,[],[f21,f152])).
% 0.21/0.55  fof(f152,plain,(
% 0.21/0.55    sK3 = k1_mcart_1(k4_tarski(k2_mcart_1(sK0),sK1)) | ~spl4_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f150])).
% 0.21/0.55  fof(f150,plain,(
% 0.21/0.55    spl4_4 <=> sK3 = k1_mcart_1(k4_tarski(k2_mcart_1(sK0),sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    spl4_3 | ~spl4_5),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f165])).
% 0.21/0.55  fof(f165,plain,(
% 0.21/0.55    $false | (spl4_3 | ~spl4_5)),
% 0.21/0.55    inference(subsumption_resolution,[],[f161,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    sK2 != k2_mcart_1(sK0) | spl4_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    spl4_3 <=> sK2 = k2_mcart_1(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.55  fof(f161,plain,(
% 0.21/0.55    sK2 = k2_mcart_1(sK0) | ~spl4_5),
% 0.21/0.55    inference(superposition,[],[f21,f156])).
% 0.21/0.55  fof(f156,plain,(
% 0.21/0.55    sK2 = k1_mcart_1(k4_tarski(k2_mcart_1(sK0),sK1)) | ~spl4_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f154])).
% 0.21/0.55  fof(f154,plain,(
% 0.21/0.55    spl4_5 <=> sK2 = k1_mcart_1(k4_tarski(k2_mcart_1(sK0),sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.55  fof(f157,plain,(
% 0.21/0.55    spl4_4 | spl4_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f142,f154,f150])).
% 0.21/0.55  fof(f142,plain,(
% 0.21/0.55    sK2 = k1_mcart_1(k4_tarski(k2_mcart_1(sK0),sK1)) | sK3 = k1_mcart_1(k4_tarski(k2_mcart_1(sK0),sK1))),
% 0.21/0.55    inference(resolution,[],[f139,f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) | k1_mcart_1(X0) = X1 | k1_mcart_1(X0) = X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)) | ~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    r2_hidden(k4_tarski(k2_mcart_1(sK0),sK1),k2_zfmisc_1(k2_tarski(sK2,sK3),k2_tarski(sK1,sK1)))),
% 0.21/0.55    inference(resolution,[],[f131,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    r2_hidden(sK1,k2_tarski(sK1,sK1))),
% 0.21/0.55    inference(resolution,[],[f55,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK1),k2_tarski(sK2,sK3)))),
% 0.21/0.55    inference(definition_unfolding,[],[f17,f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ((sK3 != k2_mcart_1(sK0) & sK2 != k2_mcart_1(sK0)) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))) => (((sK3 != k2_mcart_1(sK0) & sK2 != k2_mcart_1(sK0)) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f9,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & k1_mcart_1(X0) = X1))),
% 0.21/0.55    inference(negated_conjecture,[],[f7])).
% 0.21/0.55  fof(f7,conjecture,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & k1_mcart_1(X0) = X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | r2_hidden(sK1,X0)) )),
% 0.21/0.55    inference(superposition,[],[f23,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    sK1 = k1_mcart_1(sK0)),
% 0.21/0.55    inference(resolution,[],[f32,f30])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.21/0.55    inference(definition_unfolding,[],[f25,f20])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(k4_tarski(k2_mcart_1(sK0),X0),k2_zfmisc_1(k2_tarski(sK2,sK3),X1))) )),
% 0.21/0.55    inference(resolution,[],[f117,f74])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X4,X2,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X4,X2) | r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f73,f21])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X4,X2,X3,X1] : (~r2_hidden(X4,X2) | r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f33,f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ( ! [X4,X2,X3,X1] : (r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(k2_mcart_1(k4_tarski(X3,X4)),X2) | ~r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(X3,X4) != X0 | ~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0 | ~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1))),
% 0.21/0.55    inference(flattening,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0) | (~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) => (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    r2_hidden(k2_mcart_1(sK0),k2_tarski(sK2,sK3))),
% 0.21/0.55    inference(resolution,[],[f114,f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X3,X2)) | r2_hidden(X1,X2)) )),
% 0.21/0.55    inference(superposition,[],[f24,f22])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    r2_hidden(k4_tarski(sK1,k2_mcart_1(sK0)),k2_zfmisc_1(k2_tarski(sK1,sK1),k2_tarski(sK2,sK3)))),
% 0.21/0.55    inference(resolution,[],[f84,f30])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    ( ! [X4,X5,X3] : (~r2_hidden(X3,k2_zfmisc_1(X5,X4)) | r2_hidden(k4_tarski(sK1,k2_mcart_1(X3)),k2_zfmisc_1(k2_tarski(sK1,sK1),X4))) )),
% 0.21/0.55    inference(resolution,[],[f78,f24])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    ( ! [X12,X13] : (~r2_hidden(X12,X13) | r2_hidden(k4_tarski(sK1,X12),k2_zfmisc_1(k2_tarski(sK1,sK1),X13))) )),
% 0.21/0.55    inference(resolution,[],[f74,f56])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    spl4_1),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    $false | spl4_1),
% 0.21/0.55    inference(subsumption_resolution,[],[f50,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    sK1 != k1_mcart_1(sK0) | spl4_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    spl4_1 <=> sK1 = k1_mcart_1(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ~spl4_1 | ~spl4_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f18,f44,f35])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    sK2 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ~spl4_1 | ~spl4_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f19,f39,f35])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    sK3 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (25023)------------------------------
% 0.21/0.55  % (25023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (25023)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (25023)Memory used [KB]: 10874
% 0.21/0.55  % (25023)Time elapsed: 0.121 s
% 0.21/0.55  % (25023)------------------------------
% 0.21/0.55  % (25023)------------------------------
% 0.21/0.55  % (25031)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (25019)Success in time 0.191 s
%------------------------------------------------------------------------------
