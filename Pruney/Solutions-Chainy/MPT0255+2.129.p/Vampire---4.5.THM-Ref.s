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
% DateTime   : Thu Dec  3 12:39:51 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   45 (  61 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  155 ( 247 expanded)
%              Number of equality atoms :   73 ( 133 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f61,f69,f94,f119])).

fof(f119,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f47,f39,f93,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f93,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl5_7
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f39,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f47,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f94,plain,
    ( spl5_7
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f74,f65,f91])).

fof(f65,plain,
    ( spl5_3
  <=> k1_xboole_0 = k2_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f74,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl5_3 ),
    inference(superposition,[],[f47,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f69,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f63,f58,f65])).

fof(f58,plain,
    ( spl5_2
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f63,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | ~ spl5_2 ),
    inference(superposition,[],[f29,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f61,plain,
    ( spl5_2
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f56,f52,f58])).

fof(f52,plain,
    ( spl5_1
  <=> k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f56,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0)
    | ~ spl5_1 ),
    inference(superposition,[],[f28,f54])).

fof(f54,plain,
    ( k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f28,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f55,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f27,f52])).

fof(f27,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:19:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (13254)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (13278)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (13262)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (13270)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.24/0.53  % (13270)Refutation found. Thanks to Tanya!
% 1.24/0.53  % SZS status Theorem for theBenchmark
% 1.24/0.53  % (13250)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.24/0.53  % (13278)Refutation not found, incomplete strategy% (13278)------------------------------
% 1.24/0.53  % (13278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (13278)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (13278)Memory used [KB]: 1663
% 1.24/0.53  % (13278)Time elapsed: 0.002 s
% 1.24/0.53  % (13278)------------------------------
% 1.24/0.53  % (13278)------------------------------
% 1.24/0.53  % (13250)Refutation not found, incomplete strategy% (13250)------------------------------
% 1.24/0.53  % (13250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (13250)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (13250)Memory used [KB]: 1663
% 1.24/0.53  % (13250)Time elapsed: 0.115 s
% 1.24/0.53  % (13250)------------------------------
% 1.24/0.53  % (13250)------------------------------
% 1.24/0.53  % SZS output start Proof for theBenchmark
% 1.24/0.53  fof(f122,plain,(
% 1.24/0.53    $false),
% 1.24/0.53    inference(avatar_sat_refutation,[],[f55,f61,f69,f94,f119])).
% 1.24/0.53  fof(f119,plain,(
% 1.24/0.53    ~spl5_7),
% 1.24/0.53    inference(avatar_contradiction_clause,[],[f111])).
% 1.24/0.53  fof(f111,plain,(
% 1.24/0.53    $false | ~spl5_7),
% 1.24/0.53    inference(unit_resulting_resolution,[],[f47,f39,f93,f43])).
% 1.24/0.53  fof(f43,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f26])).
% 1.24/0.53  fof(f26,plain,(
% 1.24/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f25])).
% 1.24/0.53  fof(f25,plain,(
% 1.24/0.53    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f17,plain,(
% 1.24/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.24/0.53    inference(ennf_transformation,[],[f15])).
% 1.24/0.53  fof(f15,plain,(
% 1.24/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.24/0.53    inference(rectify,[],[f1])).
% 1.24/0.53  fof(f1,axiom,(
% 1.24/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.24/0.53  fof(f93,plain,(
% 1.24/0.53    r2_hidden(sK1,k1_xboole_0) | ~spl5_7),
% 1.24/0.53    inference(avatar_component_clause,[],[f91])).
% 1.24/0.53  fof(f91,plain,(
% 1.24/0.53    spl5_7 <=> r2_hidden(sK1,k1_xboole_0)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.24/0.53  fof(f39,plain,(
% 1.24/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f5])).
% 1.24/0.53  fof(f5,axiom,(
% 1.24/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.24/0.53  fof(f47,plain,(
% 1.24/0.53    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 1.24/0.53    inference(equality_resolution,[],[f46])).
% 1.24/0.53  fof(f46,plain,(
% 1.24/0.53    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 1.24/0.53    inference(equality_resolution,[],[f34])).
% 1.24/0.53  fof(f34,plain,(
% 1.24/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.24/0.53    inference(cnf_transformation,[],[f24])).
% 1.24/0.53  fof(f24,plain,(
% 1.24/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).
% 1.24/0.53  fof(f23,plain,(
% 1.24/0.53    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f22,plain,(
% 1.24/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.24/0.53    inference(rectify,[],[f21])).
% 1.24/0.53  fof(f21,plain,(
% 1.24/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.24/0.53    inference(flattening,[],[f20])).
% 1.24/0.53  fof(f20,plain,(
% 1.24/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.24/0.53    inference(nnf_transformation,[],[f7])).
% 1.24/0.53  fof(f7,axiom,(
% 1.24/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.24/0.53  fof(f94,plain,(
% 1.24/0.53    spl5_7 | ~spl5_3),
% 1.24/0.53    inference(avatar_split_clause,[],[f74,f65,f91])).
% 1.24/0.53  fof(f65,plain,(
% 1.24/0.53    spl5_3 <=> k1_xboole_0 = k2_tarski(sK0,sK1)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.24/0.53  fof(f74,plain,(
% 1.24/0.53    r2_hidden(sK1,k1_xboole_0) | ~spl5_3),
% 1.24/0.53    inference(superposition,[],[f47,f67])).
% 1.24/0.53  fof(f67,plain,(
% 1.24/0.53    k1_xboole_0 = k2_tarski(sK0,sK1) | ~spl5_3),
% 1.24/0.53    inference(avatar_component_clause,[],[f65])).
% 1.24/0.53  fof(f69,plain,(
% 1.24/0.53    spl5_3 | ~spl5_2),
% 1.24/0.53    inference(avatar_split_clause,[],[f63,f58,f65])).
% 1.24/0.53  fof(f58,plain,(
% 1.24/0.53    spl5_2 <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.24/0.53  fof(f63,plain,(
% 1.24/0.53    k1_xboole_0 = k2_tarski(sK0,sK1) | ~spl5_2),
% 1.24/0.53    inference(superposition,[],[f29,f60])).
% 1.24/0.53  fof(f60,plain,(
% 1.24/0.53    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) | ~spl5_2),
% 1.24/0.53    inference(avatar_component_clause,[],[f58])).
% 1.24/0.53  fof(f29,plain,(
% 1.24/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.24/0.53    inference(cnf_transformation,[],[f3])).
% 1.24/0.53  fof(f3,axiom,(
% 1.24/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.24/0.53  fof(f61,plain,(
% 1.24/0.53    spl5_2 | ~spl5_1),
% 1.24/0.53    inference(avatar_split_clause,[],[f56,f52,f58])).
% 1.24/0.53  fof(f52,plain,(
% 1.24/0.53    spl5_1 <=> k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.24/0.53  fof(f56,plain,(
% 1.24/0.53    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) | ~spl5_1),
% 1.24/0.53    inference(superposition,[],[f28,f54])).
% 1.24/0.53  fof(f54,plain,(
% 1.24/0.53    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl5_1),
% 1.24/0.53    inference(avatar_component_clause,[],[f52])).
% 1.24/0.53  fof(f28,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f4])).
% 1.24/0.53  fof(f4,axiom,(
% 1.24/0.53    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.24/0.53  fof(f55,plain,(
% 1.24/0.53    spl5_1),
% 1.24/0.53    inference(avatar_split_clause,[],[f27,f52])).
% 1.24/0.53  fof(f27,plain,(
% 1.24/0.53    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.24/0.53    inference(cnf_transformation,[],[f19])).
% 1.24/0.53  fof(f19,plain,(
% 1.24/0.53    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 1.24/0.53  fof(f18,plain,(
% 1.24/0.53    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f16,plain,(
% 1.24/0.53    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.24/0.53    inference(ennf_transformation,[],[f14])).
% 1.24/0.53  fof(f14,negated_conjecture,(
% 1.24/0.53    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.24/0.53    inference(negated_conjecture,[],[f13])).
% 1.24/0.53  fof(f13,conjecture,(
% 1.24/0.53    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 1.24/0.53  % SZS output end Proof for theBenchmark
% 1.24/0.53  % (13270)------------------------------
% 1.24/0.53  % (13270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (13270)Termination reason: Refutation
% 1.24/0.53  
% 1.24/0.53  % (13270)Memory used [KB]: 6268
% 1.24/0.53  % (13270)Time elapsed: 0.120 s
% 1.24/0.53  % (13270)------------------------------
% 1.24/0.53  % (13270)------------------------------
% 1.24/0.53  % (13248)Success in time 0.164 s
%------------------------------------------------------------------------------
