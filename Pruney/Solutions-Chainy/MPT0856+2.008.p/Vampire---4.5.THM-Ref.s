%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:14 EST 2020

% Result     : Theorem 1.09s
% Output     : Refutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :   60 (  98 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  124 ( 194 expanded)
%              Number of equality atoms :   29 (  52 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f77,f83,f85])).

fof(f85,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f84,f65,f80])).

fof(f80,plain,
    ( spl3_6
  <=> r1_tarski(sK1,k1_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f65,plain,
    ( spl3_4
  <=> r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f84,plain,
    ( r1_tarski(sK1,k1_mcart_1(sK0))
    | ~ spl3_4 ),
    inference(resolution,[],[f60,f67])).

fof(f67,plain,
    ( r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_enumset1(X0,X0,X0,X0))
      | r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f28,f42])).

fof(f42,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f32,f39])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f83,plain,
    ( ~ spl3_6
    | spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f78,f74,f46,f80])).

fof(f46,plain,
    ( spl3_1
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f74,plain,
    ( spl3_5
  <=> r1_tarski(k1_mcart_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f78,plain,
    ( sK1 = k1_mcart_1(sK0)
    | ~ r1_tarski(sK1,k1_mcart_1(sK0))
    | ~ spl3_5 ),
    inference(resolution,[],[f76,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f76,plain,
    ( r1_tarski(k1_mcart_1(sK0),sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f77,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f72,f65,f74])).

fof(f72,plain,
    ( r1_tarski(k1_mcart_1(sK0),sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f59,f67])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_enumset1(X0,X0,X0,X0))
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f29,f41])).

fof(f41,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f31,f39])).

fof(f31,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f68,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f61,f55,f65])).

fof(f55,plain,
    ( spl3_3
  <=> r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f61,plain,
    ( r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f26,f57])).

fof(f57,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f63,plain,
    ( spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f62,f55,f50])).

fof(f50,plain,
    ( spl3_2
  <=> r2_hidden(k2_mcart_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f62,plain,
    ( r2_hidden(k2_mcart_1(sK0),sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f27,f57])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f40,f55])).

fof(f40,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(definition_unfolding,[],[f24,f39])).

fof(f24,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
      | sK1 != k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
        | sK1 != k1_mcart_1(sK0) )
      & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
       => ( r2_hidden(k2_mcart_1(X0),X2)
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f53,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f25,f50,f46])).

fof(f25,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:40:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (829882370)
% 0.13/0.37  ipcrm: permission denied for id (829947910)
% 0.13/0.39  ipcrm: permission denied for id (830046227)
% 0.13/0.40  ipcrm: permission denied for id (830111767)
% 0.13/0.40  ipcrm: permission denied for id (830144538)
% 0.13/0.42  ipcrm: permission denied for id (830242855)
% 0.21/0.43  ipcrm: permission denied for id (830308395)
% 0.21/0.44  ipcrm: permission denied for id (830406705)
% 0.21/0.44  ipcrm: permission denied for id (830439475)
% 0.21/0.46  ipcrm: permission denied for id (830537792)
% 0.21/0.48  ipcrm: permission denied for id (830701642)
% 0.21/0.48  ipcrm: permission denied for id (830734411)
% 0.21/0.49  ipcrm: permission denied for id (830832722)
% 0.21/0.49  ipcrm: permission denied for id (830865491)
% 0.21/0.52  ipcrm: permission denied for id (831029351)
% 0.21/0.52  ipcrm: permission denied for id (831062120)
% 0.21/0.52  ipcrm: permission denied for id (831094890)
% 0.21/0.52  ipcrm: permission denied for id (831127660)
% 1.09/0.71  % (732)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.09/0.71  % (724)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.09/0.72  % (732)Refutation found. Thanks to Tanya!
% 1.09/0.72  % SZS status Theorem for theBenchmark
% 1.09/0.72  % SZS output start Proof for theBenchmark
% 1.09/0.72  fof(f86,plain,(
% 1.09/0.72    $false),
% 1.09/0.72    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f77,f83,f85])).
% 1.09/0.72  fof(f85,plain,(
% 1.09/0.72    spl3_6 | ~spl3_4),
% 1.09/0.72    inference(avatar_split_clause,[],[f84,f65,f80])).
% 1.09/0.72  fof(f80,plain,(
% 1.09/0.72    spl3_6 <=> r1_tarski(sK1,k1_mcart_1(sK0))),
% 1.09/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.09/0.72  fof(f65,plain,(
% 1.09/0.72    spl3_4 <=> r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.09/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.09/0.72  fof(f84,plain,(
% 1.09/0.72    r1_tarski(sK1,k1_mcart_1(sK0)) | ~spl3_4),
% 1.09/0.72    inference(resolution,[],[f60,f67])).
% 1.09/0.72  fof(f67,plain,(
% 1.09/0.72    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl3_4),
% 1.09/0.72    inference(avatar_component_clause,[],[f65])).
% 1.09/0.72  fof(f60,plain,(
% 1.09/0.72    ( ! [X0,X1] : (~r2_hidden(X1,k2_enumset1(X0,X0,X0,X0)) | r1_tarski(X0,X1)) )),
% 1.09/0.72    inference(superposition,[],[f28,f42])).
% 1.09/0.72  fof(f42,plain,(
% 1.09/0.72    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.09/0.72    inference(definition_unfolding,[],[f32,f39])).
% 1.09/0.72  fof(f39,plain,(
% 1.09/0.72    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.09/0.72    inference(definition_unfolding,[],[f30,f38])).
% 1.09/0.72  fof(f38,plain,(
% 1.09/0.72    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.09/0.72    inference(definition_unfolding,[],[f36,f37])).
% 1.09/0.72  fof(f37,plain,(
% 1.09/0.72    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.09/0.72    inference(cnf_transformation,[],[f4])).
% 1.09/0.72  fof(f4,axiom,(
% 1.09/0.72    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.09/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.09/0.72  fof(f36,plain,(
% 1.09/0.72    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.09/0.72    inference(cnf_transformation,[],[f3])).
% 1.09/0.72  fof(f3,axiom,(
% 1.09/0.72    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.09/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.09/0.72  fof(f30,plain,(
% 1.09/0.72    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.09/0.72    inference(cnf_transformation,[],[f2])).
% 1.09/0.72  fof(f2,axiom,(
% 1.09/0.72    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.09/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.09/0.72  fof(f32,plain,(
% 1.09/0.72    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.09/0.72    inference(cnf_transformation,[],[f11])).
% 1.09/0.72  fof(f11,axiom,(
% 1.09/0.72    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.09/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.09/0.72  fof(f28,plain,(
% 1.09/0.72    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 1.09/0.72    inference(cnf_transformation,[],[f18])).
% 1.09/0.72  fof(f18,plain,(
% 1.09/0.72    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 1.09/0.72    inference(ennf_transformation,[],[f12])).
% 1.09/0.72  fof(f12,axiom,(
% 1.09/0.72    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.09/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 1.09/0.72  fof(f83,plain,(
% 1.09/0.72    ~spl3_6 | spl3_1 | ~spl3_5),
% 1.09/0.72    inference(avatar_split_clause,[],[f78,f74,f46,f80])).
% 1.09/0.72  fof(f46,plain,(
% 1.09/0.72    spl3_1 <=> sK1 = k1_mcart_1(sK0)),
% 1.09/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.09/0.72  fof(f74,plain,(
% 1.09/0.72    spl3_5 <=> r1_tarski(k1_mcart_1(sK0),sK1)),
% 1.09/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.09/0.72  fof(f78,plain,(
% 1.09/0.72    sK1 = k1_mcart_1(sK0) | ~r1_tarski(sK1,k1_mcart_1(sK0)) | ~spl3_5),
% 1.09/0.72    inference(resolution,[],[f76,f35])).
% 1.09/0.72  fof(f35,plain,(
% 1.09/0.72    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.09/0.72    inference(cnf_transformation,[],[f23])).
% 1.09/0.72  fof(f23,plain,(
% 1.09/0.72    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.09/0.72    inference(flattening,[],[f22])).
% 1.09/0.72  fof(f22,plain,(
% 1.09/0.72    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.09/0.72    inference(nnf_transformation,[],[f1])).
% 1.09/0.72  fof(f1,axiom,(
% 1.09/0.72    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.09/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.09/0.72  fof(f76,plain,(
% 1.09/0.72    r1_tarski(k1_mcart_1(sK0),sK1) | ~spl3_5),
% 1.09/0.72    inference(avatar_component_clause,[],[f74])).
% 1.09/0.72  fof(f77,plain,(
% 1.09/0.72    spl3_5 | ~spl3_4),
% 1.09/0.72    inference(avatar_split_clause,[],[f72,f65,f74])).
% 1.09/0.72  fof(f72,plain,(
% 1.09/0.72    r1_tarski(k1_mcart_1(sK0),sK1) | ~spl3_4),
% 1.09/0.72    inference(resolution,[],[f59,f67])).
% 1.09/0.72  fof(f59,plain,(
% 1.09/0.72    ( ! [X0,X1] : (~r2_hidden(X1,k2_enumset1(X0,X0,X0,X0)) | r1_tarski(X1,X0)) )),
% 1.09/0.72    inference(superposition,[],[f29,f41])).
% 1.09/0.72  fof(f41,plain,(
% 1.09/0.72    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.09/0.72    inference(definition_unfolding,[],[f31,f39])).
% 1.09/0.72  fof(f31,plain,(
% 1.09/0.72    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 1.09/0.72    inference(cnf_transformation,[],[f10])).
% 1.09/0.72  fof(f10,axiom,(
% 1.09/0.72    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 1.09/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 1.09/0.72  fof(f29,plain,(
% 1.09/0.72    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 1.09/0.72    inference(cnf_transformation,[],[f19])).
% 1.09/0.72  fof(f19,plain,(
% 1.09/0.72    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.09/0.72    inference(ennf_transformation,[],[f9])).
% 1.09/0.72  fof(f9,axiom,(
% 1.09/0.72    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.09/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.09/0.72  fof(f68,plain,(
% 1.09/0.72    spl3_4 | ~spl3_3),
% 1.09/0.72    inference(avatar_split_clause,[],[f61,f55,f65])).
% 1.09/0.72  fof(f55,plain,(
% 1.09/0.72    spl3_3 <=> r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))),
% 1.09/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.09/0.72  fof(f61,plain,(
% 1.09/0.72    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl3_3),
% 1.09/0.72    inference(resolution,[],[f26,f57])).
% 1.09/0.72  fof(f57,plain,(
% 1.09/0.72    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) | ~spl3_3),
% 1.09/0.72    inference(avatar_component_clause,[],[f55])).
% 1.09/0.72  fof(f26,plain,(
% 1.09/0.72    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.09/0.72    inference(cnf_transformation,[],[f17])).
% 1.09/0.72  fof(f17,plain,(
% 1.09/0.72    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.09/0.72    inference(ennf_transformation,[],[f13])).
% 1.09/0.72  fof(f13,axiom,(
% 1.09/0.72    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.09/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.09/0.72  fof(f63,plain,(
% 1.09/0.72    spl3_2 | ~spl3_3),
% 1.09/0.72    inference(avatar_split_clause,[],[f62,f55,f50])).
% 1.09/0.72  fof(f50,plain,(
% 1.09/0.72    spl3_2 <=> r2_hidden(k2_mcart_1(sK0),sK2)),
% 1.09/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.09/0.72  fof(f62,plain,(
% 1.09/0.72    r2_hidden(k2_mcart_1(sK0),sK2) | ~spl3_3),
% 1.09/0.72    inference(resolution,[],[f27,f57])).
% 1.09/0.72  fof(f27,plain,(
% 1.09/0.72    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.09/0.72    inference(cnf_transformation,[],[f17])).
% 1.09/0.72  fof(f58,plain,(
% 1.09/0.72    spl3_3),
% 1.09/0.72    inference(avatar_split_clause,[],[f40,f55])).
% 1.09/0.72  fof(f40,plain,(
% 1.09/0.72    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))),
% 1.09/0.72    inference(definition_unfolding,[],[f24,f39])).
% 1.09/0.72  fof(f24,plain,(
% 1.09/0.72    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 1.09/0.72    inference(cnf_transformation,[],[f21])).
% 1.09/0.72  fof(f21,plain,(
% 1.09/0.72    (~r2_hidden(k2_mcart_1(sK0),sK2) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 1.09/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f20])).
% 1.09/0.72  fof(f20,plain,(
% 1.09/0.72    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) => ((~r2_hidden(k2_mcart_1(sK0),sK2) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 1.09/0.72    introduced(choice_axiom,[])).
% 1.09/0.72  fof(f16,plain,(
% 1.09/0.72    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 1.09/0.72    inference(ennf_transformation,[],[f15])).
% 1.09/0.72  fof(f15,negated_conjecture,(
% 1.09/0.72    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.09/0.72    inference(negated_conjecture,[],[f14])).
% 1.09/0.72  fof(f14,conjecture,(
% 1.09/0.72    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.09/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).
% 1.09/0.72  fof(f53,plain,(
% 1.09/0.72    ~spl3_1 | ~spl3_2),
% 1.09/0.72    inference(avatar_split_clause,[],[f25,f50,f46])).
% 1.09/0.72  fof(f25,plain,(
% 1.09/0.72    ~r2_hidden(k2_mcart_1(sK0),sK2) | sK1 != k1_mcart_1(sK0)),
% 1.09/0.72    inference(cnf_transformation,[],[f21])).
% 1.09/0.72  % SZS output end Proof for theBenchmark
% 1.09/0.72  % (732)------------------------------
% 1.09/0.72  % (732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.09/0.72  % (732)Termination reason: Refutation
% 1.09/0.72  
% 1.09/0.72  % (732)Memory used [KB]: 10746
% 1.09/0.72  % (732)Time elapsed: 0.066 s
% 1.09/0.72  % (732)------------------------------
% 1.09/0.72  % (732)------------------------------
% 1.09/0.73  % (522)Success in time 0.363 s
%------------------------------------------------------------------------------
