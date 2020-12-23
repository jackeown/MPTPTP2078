%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:33 EST 2020

% Result     : Theorem 1.16s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 168 expanded)
%              Number of leaves         :   18 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  173 ( 321 expanded)
%              Number of equality atoms :   84 ( 196 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f93,f123,f125,f150,f155])).

fof(f155,plain,
    ( spl3_1
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl3_1
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f61,f149,f54])).

fof(f54,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f149,plain,
    ( r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl3_8
  <=> r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f61,plain,
    ( sK0 != sK1
    | spl3_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f150,plain,
    ( spl3_8
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f141,f86,f147])).

fof(f86,plain,
    ( spl3_3
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f141,plain,
    ( r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_3 ),
    inference(superposition,[],[f53,f88])).

fof(f88,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f53,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f125,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f26,f122,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f122,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl3_7
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f123,plain,
    ( ~ spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f106,f90,f120])).

fof(f90,plain,
    ( spl3_4
  <=> k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f106,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f57,f92])).

fof(f92,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f57,plain,(
    ! [X1] : ~ r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f37,f42,f42])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f93,plain,
    ( spl3_3
    | spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f68,f64,f90,f86])).

fof(f64,plain,
    ( spl3_2
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f68,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f66,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f34,f42,f42])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f66,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f67,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f43,f64])).

fof(f43,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f24,f42,f42])).

fof(f24,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

fof(f62,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:07:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (19552)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.16/0.52  % (19577)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.16/0.52  % (19560)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.16/0.53  % (19560)Refutation found. Thanks to Tanya!
% 1.16/0.53  % SZS status Theorem for theBenchmark
% 1.16/0.53  % (19577)Refutation not found, incomplete strategy% (19577)------------------------------
% 1.16/0.53  % (19577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.53  % (19577)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.53  
% 1.16/0.53  % (19577)Memory used [KB]: 6140
% 1.16/0.53  % (19577)Time elapsed: 0.118 s
% 1.16/0.53  % (19577)------------------------------
% 1.16/0.53  % (19577)------------------------------
% 1.16/0.53  % SZS output start Proof for theBenchmark
% 1.16/0.53  fof(f156,plain,(
% 1.16/0.53    $false),
% 1.16/0.53    inference(avatar_sat_refutation,[],[f62,f67,f93,f123,f125,f150,f155])).
% 1.16/0.53  fof(f155,plain,(
% 1.16/0.53    spl3_1 | ~spl3_8),
% 1.16/0.53    inference(avatar_contradiction_clause,[],[f151])).
% 1.16/0.53  fof(f151,plain,(
% 1.16/0.53    $false | (spl3_1 | ~spl3_8)),
% 1.16/0.53    inference(unit_resulting_resolution,[],[f61,f149,f54])).
% 1.16/0.53  fof(f54,plain,(
% 1.16/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.16/0.53    inference(equality_resolution,[],[f47])).
% 1.16/0.53  fof(f47,plain,(
% 1.16/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.16/0.53    inference(definition_unfolding,[],[f30,f42])).
% 1.16/0.53  fof(f42,plain,(
% 1.16/0.53    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.16/0.53    inference(definition_unfolding,[],[f27,f41])).
% 1.16/0.53  fof(f41,plain,(
% 1.16/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.16/0.53    inference(definition_unfolding,[],[f28,f40])).
% 1.16/0.53  fof(f40,plain,(
% 1.16/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.16/0.53    inference(definition_unfolding,[],[f38,f39])).
% 1.16/0.53  fof(f39,plain,(
% 1.16/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.16/0.53    inference(cnf_transformation,[],[f7])).
% 1.16/0.53  fof(f7,axiom,(
% 1.16/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.16/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.16/0.53  fof(f38,plain,(
% 1.16/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.16/0.53    inference(cnf_transformation,[],[f6])).
% 1.16/0.53  fof(f6,axiom,(
% 1.16/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.16/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.16/0.53  fof(f28,plain,(
% 1.16/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.16/0.53    inference(cnf_transformation,[],[f5])).
% 1.16/0.53  fof(f5,axiom,(
% 1.16/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.16/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.16/0.53  fof(f27,plain,(
% 1.16/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.16/0.53    inference(cnf_transformation,[],[f4])).
% 1.16/0.53  fof(f4,axiom,(
% 1.16/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.16/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.16/0.53  fof(f30,plain,(
% 1.16/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.16/0.53    inference(cnf_transformation,[],[f21])).
% 1.16/0.53  fof(f21,plain,(
% 1.16/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.16/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).
% 1.16/0.53  fof(f20,plain,(
% 1.16/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.16/0.53    introduced(choice_axiom,[])).
% 1.16/0.53  fof(f19,plain,(
% 1.16/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.16/0.53    inference(rectify,[],[f18])).
% 1.16/0.53  fof(f18,plain,(
% 1.16/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.16/0.53    inference(nnf_transformation,[],[f3])).
% 1.16/0.53  fof(f3,axiom,(
% 1.16/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.16/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.16/0.53  fof(f149,plain,(
% 1.16/0.53    r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl3_8),
% 1.16/0.53    inference(avatar_component_clause,[],[f147])).
% 1.16/0.53  fof(f147,plain,(
% 1.16/0.53    spl3_8 <=> r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.16/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.16/0.53  fof(f61,plain,(
% 1.16/0.53    sK0 != sK1 | spl3_1),
% 1.16/0.53    inference(avatar_component_clause,[],[f59])).
% 1.16/0.53  fof(f59,plain,(
% 1.16/0.53    spl3_1 <=> sK0 = sK1),
% 1.16/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.16/0.53  fof(f150,plain,(
% 1.16/0.53    spl3_8 | ~spl3_3),
% 1.16/0.53    inference(avatar_split_clause,[],[f141,f86,f147])).
% 1.16/0.53  fof(f86,plain,(
% 1.16/0.53    spl3_3 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 1.16/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.16/0.53  fof(f141,plain,(
% 1.16/0.53    r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl3_3),
% 1.16/0.53    inference(superposition,[],[f53,f88])).
% 1.16/0.53  fof(f88,plain,(
% 1.16/0.53    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl3_3),
% 1.16/0.53    inference(avatar_component_clause,[],[f86])).
% 1.16/0.53  fof(f53,plain,(
% 1.16/0.53    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 1.16/0.53    inference(equality_resolution,[],[f52])).
% 1.16/0.53  fof(f52,plain,(
% 1.16/0.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 1.16/0.53    inference(equality_resolution,[],[f46])).
% 1.16/0.53  fof(f46,plain,(
% 1.16/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.16/0.53    inference(definition_unfolding,[],[f31,f42])).
% 1.16/0.53  fof(f31,plain,(
% 1.16/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.16/0.53    inference(cnf_transformation,[],[f21])).
% 1.16/0.53  fof(f125,plain,(
% 1.16/0.53    spl3_7),
% 1.16/0.53    inference(avatar_contradiction_clause,[],[f124])).
% 1.16/0.53  fof(f124,plain,(
% 1.16/0.53    $false | spl3_7),
% 1.16/0.53    inference(unit_resulting_resolution,[],[f26,f122,f29])).
% 1.16/0.53  fof(f29,plain,(
% 1.16/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.16/0.53    inference(cnf_transformation,[],[f14])).
% 1.16/0.53  fof(f14,plain,(
% 1.16/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 1.16/0.53    inference(ennf_transformation,[],[f12])).
% 1.16/0.53  fof(f12,plain,(
% 1.16/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 1.16/0.53    inference(unused_predicate_definition_removal,[],[f2])).
% 1.16/0.53  fof(f2,axiom,(
% 1.16/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.16/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.16/0.53  fof(f122,plain,(
% 1.16/0.53    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | spl3_7),
% 1.16/0.53    inference(avatar_component_clause,[],[f120])).
% 1.16/0.53  fof(f120,plain,(
% 1.16/0.53    spl3_7 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.16/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.16/0.53  fof(f26,plain,(
% 1.16/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.16/0.53    inference(cnf_transformation,[],[f1])).
% 1.16/0.53  fof(f1,axiom,(
% 1.16/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.16/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.16/0.53  fof(f123,plain,(
% 1.16/0.53    ~spl3_7 | ~spl3_4),
% 1.16/0.53    inference(avatar_split_clause,[],[f106,f90,f120])).
% 1.16/0.53  fof(f90,plain,(
% 1.16/0.53    spl3_4 <=> k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.16/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.16/0.53  fof(f106,plain,(
% 1.16/0.53    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_4),
% 1.16/0.53    inference(superposition,[],[f57,f92])).
% 1.16/0.53  fof(f92,plain,(
% 1.16/0.53    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl3_4),
% 1.16/0.53    inference(avatar_component_clause,[],[f90])).
% 1.16/0.53  fof(f57,plain,(
% 1.16/0.53    ( ! [X1] : (~r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1))) )),
% 1.16/0.53    inference(equality_resolution,[],[f51])).
% 1.16/0.53  fof(f51,plain,(
% 1.16/0.53    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) )),
% 1.16/0.53    inference(definition_unfolding,[],[f37,f42,f42])).
% 1.16/0.53  fof(f37,plain,(
% 1.16/0.53    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.16/0.53    inference(cnf_transformation,[],[f15])).
% 1.16/0.53  fof(f15,plain,(
% 1.16/0.53    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.16/0.53    inference(ennf_transformation,[],[f9])).
% 1.16/0.53  fof(f9,axiom,(
% 1.16/0.53    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.16/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 1.16/0.53  fof(f93,plain,(
% 1.16/0.53    spl3_3 | spl3_4 | ~spl3_2),
% 1.16/0.53    inference(avatar_split_clause,[],[f68,f64,f90,f86])).
% 1.16/0.53  fof(f64,plain,(
% 1.16/0.53    spl3_2 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.16/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.16/0.53  fof(f68,plain,(
% 1.16/0.53    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | ~spl3_2),
% 1.16/0.53    inference(resolution,[],[f66,f50])).
% 1.16/0.53  fof(f50,plain,(
% 1.16/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 1.16/0.53    inference(definition_unfolding,[],[f34,f42,f42])).
% 1.16/0.53  fof(f34,plain,(
% 1.16/0.53    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.16/0.53    inference(cnf_transformation,[],[f23])).
% 1.16/0.53  fof(f23,plain,(
% 1.16/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.16/0.53    inference(flattening,[],[f22])).
% 1.16/0.53  fof(f22,plain,(
% 1.16/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.16/0.53    inference(nnf_transformation,[],[f8])).
% 1.16/0.53  fof(f8,axiom,(
% 1.16/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.16/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.16/0.53  fof(f66,plain,(
% 1.16/0.53    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl3_2),
% 1.16/0.53    inference(avatar_component_clause,[],[f64])).
% 1.16/0.53  fof(f67,plain,(
% 1.16/0.53    spl3_2),
% 1.16/0.53    inference(avatar_split_clause,[],[f43,f64])).
% 1.16/0.53  fof(f43,plain,(
% 1.16/0.53    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.16/0.53    inference(definition_unfolding,[],[f24,f42,f42])).
% 1.16/0.53  fof(f24,plain,(
% 1.16/0.53    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 1.16/0.53    inference(cnf_transformation,[],[f17])).
% 1.16/0.53  fof(f17,plain,(
% 1.16/0.53    sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 1.16/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f16])).
% 1.16/0.53  fof(f16,plain,(
% 1.16/0.53    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.16/0.53    introduced(choice_axiom,[])).
% 1.16/0.53  fof(f13,plain,(
% 1.16/0.53    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.16/0.53    inference(ennf_transformation,[],[f11])).
% 1.16/0.53  fof(f11,negated_conjecture,(
% 1.16/0.53    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.16/0.53    inference(negated_conjecture,[],[f10])).
% 1.16/0.53  fof(f10,conjecture,(
% 1.16/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.16/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).
% 1.16/0.53  fof(f62,plain,(
% 1.16/0.53    ~spl3_1),
% 1.16/0.53    inference(avatar_split_clause,[],[f25,f59])).
% 1.16/0.53  fof(f25,plain,(
% 1.16/0.53    sK0 != sK1),
% 1.16/0.53    inference(cnf_transformation,[],[f17])).
% 1.16/0.53  % SZS output end Proof for theBenchmark
% 1.16/0.53  % (19560)------------------------------
% 1.16/0.53  % (19560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.53  % (19560)Termination reason: Refutation
% 1.16/0.53  
% 1.16/0.53  % (19560)Memory used [KB]: 10746
% 1.16/0.53  % (19560)Time elapsed: 0.123 s
% 1.16/0.53  % (19560)------------------------------
% 1.16/0.53  % (19560)------------------------------
% 1.16/0.53  % (19549)Success in time 0.163 s
%------------------------------------------------------------------------------
