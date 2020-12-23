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
% DateTime   : Thu Dec  3 12:42:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 119 expanded)
%              Number of leaves         :   11 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :  128 ( 230 expanded)
%              Number of equality atoms :   25 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f44,f65,f69,f76,f87,f90])).

fof(f90,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f36,f85,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(condensation,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X1
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(resolution,[],[f28,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f18,f22])).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f12,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f13,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f13,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f12,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f85,plain,
    ( r2_hidden(sK1,k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl4_1 ),
    inference(resolution,[],[f33,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f33,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl4_1
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f36,plain,
    ( sK1 != sK3
    | spl4_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl4_2
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f87,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl4_1
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f41,f33,f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f41,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl4_3
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f76,plain,
    ( ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f42,f64])).

fof(f64,plain,
    ( ! [X6,X5] : ~ r2_hidden(X5,X6)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_6
  <=> ! [X5,X6] : ~ r2_hidden(X5,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f42,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f69,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f42,f45,f61,f17])).

fof(f61,plain,
    ( ! [X7] : r2_hidden(X7,k2_enumset1(X7,X7,X7,X7))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_5
  <=> ! [X7] : r2_hidden(X7,k2_enumset1(X7,X7,X7,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f45,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK1,sK1,sK1,sK1)))
    | spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f32,f37])).

fof(f37,plain,
    ( sK1 = sK3
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f32,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f65,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f58,f63,f60])).

fof(f58,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,X6)
      | r2_hidden(X7,k2_enumset1(X7,X7,X7,X7)) ) ),
    inference(resolution,[],[f29,f15])).

fof(f29,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
      | ~ r2_hidden(X1,X3) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X2
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) ) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X2
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f44,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f25,f40,f35,f31])).

fof(f25,plain,
    ( ~ r2_hidden(sK0,sK2)
    | sK1 != sK3
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f9,f22])).

fof(f9,plain,
    ( ~ r2_hidden(sK0,sK2)
    | sK1 != sK3
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <~> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      <=> ( X1 = X3
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f43,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f24,f40,f31])).

fof(f24,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f10,f22])).

fof(f10,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f23,f35,f31])).

fof(f23,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f11,f22])).

fof(f11,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (14681)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.51  % (14672)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (14672)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f38,f43,f44,f65,f69,f76,f87,f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ~spl4_1 | spl4_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    $false | (~spl4_1 | spl4_2)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f36,f85,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 0.20/0.51    inference(condensation,[],[f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (X0 = X1 | ~r2_hidden(X2,X3) | ~r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 0.20/0.51    inference(resolution,[],[f28,f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) | X0 = X2) )),
% 0.20/0.51    inference(definition_unfolding,[],[f18,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f12,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f13,f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    r2_hidden(sK1,k2_enumset1(sK3,sK3,sK3,sK3)) | ~spl4_1),
% 0.20/0.51    inference(resolution,[],[f33,f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) | ~spl4_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    spl4_1 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    sK1 != sK3 | spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    spl4_2 <=> sK1 = sK3),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ~spl4_1 | spl4_3),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f84])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    $false | (~spl4_1 | spl4_3)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f41,f33,f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ~r2_hidden(sK0,sK2) | spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    spl4_3 <=> r2_hidden(sK0,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ~spl4_3 | ~spl4_6),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    $false | (~spl4_3 | ~spl4_6)),
% 0.20/0.51    inference(subsumption_resolution,[],[f42,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X6,X5] : (~r2_hidden(X5,X6)) ) | ~spl4_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    spl4_6 <=> ! [X5,X6] : ~r2_hidden(X5,X6)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    r2_hidden(sK0,sK2) | ~spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f40])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f67])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f42,f45,f61,f17])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X7] : (r2_hidden(X7,k2_enumset1(X7,X7,X7,X7))) ) | ~spl4_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    spl4_5 <=> ! [X7] : r2_hidden(X7,k2_enumset1(X7,X7,X7,X7))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK1,sK1,sK1,sK1))) | (spl4_1 | ~spl4_2)),
% 0.20/0.51    inference(forward_demodulation,[],[f32,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    sK1 = sK3 | ~spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f35])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) | spl4_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f31])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    spl4_5 | spl4_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f58,f63,f60])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X6,X7,X5] : (~r2_hidden(X5,X6) | r2_hidden(X7,k2_enumset1(X7,X7,X7,X7))) )),
% 0.20/0.51    inference(resolution,[],[f29,f15])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X2,X3,X1] : (r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) | ~r2_hidden(X1,X3)) )),
% 0.20/0.51    inference(equality_resolution,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (X0 != X2 | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f20,f22])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (X0 != X2 | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f25,f40,f35,f31])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ~r2_hidden(sK0,sK2) | sK1 != sK3 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))),
% 0.20/0.51    inference(definition_unfolding,[],[f9,f22])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ~r2_hidden(sK0,sK2) | sK1 != sK3 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <~> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.20/0.51    inference(negated_conjecture,[],[f6])).
% 0.20/0.51  fof(f6,conjecture,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    spl4_1 | spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f24,f40,f31])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    r2_hidden(sK0,sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))),
% 0.20/0.51    inference(definition_unfolding,[],[f10,f22])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    r2_hidden(sK0,sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    spl4_1 | spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f23,f35,f31])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    sK1 = sK3 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))),
% 0.20/0.51    inference(definition_unfolding,[],[f11,f22])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    sK1 = sK3 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (14672)------------------------------
% 0.20/0.51  % (14672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (14672)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (14672)Memory used [KB]: 6268
% 0.20/0.51  % (14672)Time elapsed: 0.076 s
% 0.20/0.51  % (14672)------------------------------
% 0.20/0.51  % (14672)------------------------------
% 0.20/0.51  % (14662)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (14654)Success in time 0.161 s
%------------------------------------------------------------------------------
