%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 171 expanded)
%              Number of leaves         :   16 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :  131 ( 257 expanded)
%              Number of equality atoms :   69 ( 186 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f146,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f110,f130,f140,f145])).

fof(f145,plain,
    ( spl5_1
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | spl5_1
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f104,f139,f96])).

fof(f96,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f48,f70])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f139,plain,
    ( r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl5_4
  <=> r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f104,plain,
    ( sK0 != sK1
    | spl5_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f140,plain,
    ( spl5_4
    | spl5_3 ),
    inference(avatar_split_clause,[],[f131,f127,f137])).

fof(f127,plain,
    ( spl5_3
  <=> r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f131,plain,
    ( r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl5_3 ),
    inference(resolution,[],[f129,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f70])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f129,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f130,plain,
    ( ~ spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f123,f107,f127])).

fof(f107,plain,
    ( spl5_2
  <=> k5_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_tarski(k3_enumset1(k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f123,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl5_2 ),
    inference(trivial_inequality_removal,[],[f119])).

fof(f119,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != k5_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | ~ r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl5_2 ),
    inference(superposition,[],[f109,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k3_enumset1(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)),X0))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f69,f45,f45,f69])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f68])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f109,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != k3_tarski(k3_enumset1(k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f110,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f71,f107])).

fof(f71,plain,(
    k5_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != k3_tarski(k3_enumset1(k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f38,f45,f69,f70,f70,f69,f45,f70,f70])).

fof(f38,plain,(
    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
        & X0 != X1 )
   => ( k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( X0 != X1
       => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( X0 != X1
     => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).

fof(f105,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f37,f102])).

fof(f37,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (11244)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (11239)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (11252)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.51  % (11246)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (11246)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f105,f110,f130,f140,f145])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    spl5_1 | ~spl5_4),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f141])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    $false | (spl5_1 | ~spl5_4)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f104,f139,f96])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    ( ! [X0,X3] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X3) )),
% 0.20/0.51    inference(equality_resolution,[],[f80])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 0.20/0.51    inference(definition_unfolding,[],[f48,f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f39,f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f42,f67])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f54,f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.51    inference(rectify,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl5_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f137])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    spl5_4 <=> r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    sK0 != sK1 | spl5_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f102])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    spl5_1 <=> sK0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    spl5_4 | spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f131,f127,f137])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    spl5_3 <=> r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl5_3),
% 0.20/0.51    inference(resolution,[],[f129,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f47,f70])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    ~r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl5_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f127])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    ~spl5_3 | spl5_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f123,f107,f127])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    spl5_2 <=> k5_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_tarski(k3_enumset1(k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    ~r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl5_2),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f119])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    k5_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != k5_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | ~r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl5_2),
% 0.20/0.51    inference(superposition,[],[f109,f84])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_tarski(k3_enumset1(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X2,k3_xboole_0(X2,X0)),X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)),X0)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f56,f69,f45,f45,f69])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f41,f68])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    k5_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != k3_tarski(k3_enumset1(k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl5_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f107])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    ~spl5_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f71,f107])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    k5_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != k3_tarski(k3_enumset1(k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.20/0.51    inference(definition_unfolding,[],[f38,f45,f69,f70,f70,f69,f45,f70,f70])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) & sK0 != sK1),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) & X0 != X1) => (k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) & sK0 != sK1)),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) & X0 != X1)),
% 0.20/0.51    inference(ennf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 0.20/0.51    inference(negated_conjecture,[],[f18])).
% 0.20/0.51  fof(f18,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    ~spl5_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f37,f102])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    sK0 != sK1),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (11246)------------------------------
% 0.20/0.51  % (11246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11246)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (11246)Memory used [KB]: 10746
% 0.20/0.51  % (11246)Time elapsed: 0.091 s
% 0.20/0.51  % (11246)------------------------------
% 0.20/0.51  % (11246)------------------------------
% 0.20/0.51  % (11245)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (11235)Success in time 0.159 s
%------------------------------------------------------------------------------
