%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 107 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  183 ( 261 expanded)
%              Number of equality atoms :   76 ( 119 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f61,f73,f80,f84,f92])).

fof(f92,plain,
    ( spl5_1
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | spl5_1
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f51,f51,f79,f47])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f25,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f79,plain,
    ( r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_6
  <=> r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f51,plain,
    ( sK0 != sK1
    | spl5_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f84,plain,
    ( spl5_3
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl5_3
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f71,f60,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f60,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_3
  <=> r1_xboole_0(k2_zfmisc_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f71,plain,
    ( r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl5_5
  <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f80,plain,
    ( spl5_6
    | spl5_5 ),
    inference(avatar_split_clause,[],[f75,f70,f77])).

fof(f75,plain,
    ( r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_5 ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,
    ( r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_5 ),
    inference(resolution,[],[f72,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f33])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f72,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f73,plain,
    ( ~ spl5_5
    | spl5_2 ),
    inference(avatar_split_clause,[],[f63,f54,f70])).

fof(f54,plain,
    ( spl5_2
  <=> r1_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f63,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | spl5_2 ),
    inference(resolution,[],[f56,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f56,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK3))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f61,plain,
    ( ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f35,f58,f54])).

fof(f35,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ r1_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK3)) ),
    inference(definition_unfolding,[],[f20,f34,f34,f34,f34])).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f33])).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1)))
    | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( ~ r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1)))
      | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3)) )
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
          | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) )
        & X0 != X1 )
   => ( ( ~ r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1)))
        | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3)) )
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
        | ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) )
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( X0 != X1
       => ( r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
          & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( X0 != X1
     => ( r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1)))
        & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_zfmisc_1)).

fof(f52,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f19,f49])).

fof(f19,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:45:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (20113)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.51  % (20105)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (20097)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (20113)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f52,f61,f73,f80,f84,f92])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    spl5_1 | ~spl5_6),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f87])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    $false | (spl5_1 | ~spl5_6)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f51,f51,f79,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.22/0.52    inference(equality_resolution,[],[f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.22/0.52    inference(definition_unfolding,[],[f25,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f31,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.52    inference(rectify,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.52    inference(flattening,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f77])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    spl5_6 <=> r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    sK0 != sK1 | spl5_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    spl5_1 <=> sK0 = sK1),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    spl5_3 | ~spl5_5),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    $false | (spl5_3 | ~spl5_5)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f71,f60,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ~r1_xboole_0(k2_zfmisc_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))) | spl5_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    spl5_3 <=> r1_xboole_0(k2_zfmisc_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl5_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    spl5_5 <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    spl5_6 | spl5_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f75,f70,f77])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_5),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_5),
% 0.22/0.52    inference(resolution,[],[f72,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f23,f33])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f70])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ~spl5_5 | spl5_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f63,f54,f70])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    spl5_2 <=> r1_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | spl5_2),
% 0.22/0.52    inference(resolution,[],[f56,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ~r1_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK3)) | spl5_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f54])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ~spl5_2 | ~spl5_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f35,f58,f54])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ~r1_xboole_0(k2_zfmisc_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))) | ~r1_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK3))),
% 0.22/0.52    inference(definition_unfolding,[],[f20,f34,f34,f34,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f24,f33])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ~r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3))),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    (~r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3))) & sK0 != sK1),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : ((~r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))) & X0 != X1) => ((~r1_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK3,k1_tarski(sK1))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK3))) & sK0 != sK1)),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : ((~r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) | ~r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))) & X0 != X1)),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : (X0 != X1 => (r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))))),
% 0.22/0.52    inference(negated_conjecture,[],[f7])).
% 0.22/0.52  fof(f7,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (X0 != X1 => (r1_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X3,k1_tarski(X1))) & r1_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X3))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_zfmisc_1)).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ~spl5_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f19,f49])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    sK0 != sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (20113)------------------------------
% 0.22/0.52  % (20113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20113)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (20113)Memory used [KB]: 10746
% 0.22/0.52  % (20113)Time elapsed: 0.062 s
% 0.22/0.52  % (20113)------------------------------
% 0.22/0.52  % (20113)------------------------------
% 0.22/0.52  % (20089)Success in time 0.154 s
%------------------------------------------------------------------------------
