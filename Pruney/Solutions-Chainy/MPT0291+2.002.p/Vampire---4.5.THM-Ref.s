%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  54 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 161 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (5579)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f111,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f94,f105,f110])).

fof(f110,plain,
    ( spl6_1
    | spl6_8 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl6_1
    | spl6_8 ),
    inference(subsumption_resolution,[],[f107,f25])).

fof(f25,plain,
    ( ~ r1_xboole_0(k3_tarski(sK0),sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl6_1
  <=> r1_xboole_0(k3_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f107,plain,
    ( r1_xboole_0(k3_tarski(sK0),sK1)
    | spl6_8 ),
    inference(resolution,[],[f104,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
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

fof(f104,plain,
    ( ~ r2_hidden(sK2(k3_tarski(sK0),sK1),k3_tarski(sK0))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_8
  <=> r2_hidden(sK2(k3_tarski(sK0),sK1),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f105,plain,
    ( ~ spl6_8
    | spl6_7 ),
    inference(avatar_split_clause,[],[f97,f91,f102])).

fof(f91,plain,
    ( spl6_7
  <=> sP4(sK2(k3_tarski(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f97,plain,
    ( ~ r2_hidden(sK2(k3_tarski(sK0),sK1),k3_tarski(sK0))
    | spl6_7 ),
    inference(resolution,[],[f93,f20])).

fof(f20,plain,(
    ! [X2,X0] :
      ( sP4(X2,X0)
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f93,plain,
    ( ~ sP4(sK2(k3_tarski(sK0),sK1),sK0)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f94,plain,
    ( ~ spl6_7
    | spl6_1 ),
    inference(avatar_split_clause,[],[f71,f23,f91])).

fof(f71,plain,
    ( ~ sP4(sK2(k3_tarski(sK0),sK1),sK0)
    | spl6_1 ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,
    ( ~ sP4(sK2(k3_tarski(sK0),sK1),sK0)
    | ~ sP4(sK2(k3_tarski(sK0),sK1),sK0)
    | spl6_1 ),
    inference(resolution,[],[f43,f15])).

fof(f15,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK5(X0,X2),X0)
      | ~ sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f43,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(X1,sK2(k3_tarski(sK0),sK1)),sK0)
        | ~ sP4(sK2(k3_tarski(sK0),sK1),X1) )
    | spl6_1 ),
    inference(resolution,[],[f39,f14])).

fof(f14,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK5(X0,X2))
      | ~ sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f39,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK2(k3_tarski(sK0),sK1),X3)
        | ~ r2_hidden(X3,sK0) )
    | spl6_1 ),
    inference(resolution,[],[f34,f25])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,sK1)
      | ~ r2_hidden(sK2(X1,sK1),X0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f27,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f8,f10])).

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,plain,(
    ! [X2] :
      ( r1_xboole_0(X2,sK1)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k3_tarski(X0),X1)
      & ! [X2] :
          ( r1_xboole_0(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r1_xboole_0(X2,X1) )
       => r1_xboole_0(k3_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(f26,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f9,f23])).

fof(f9,plain,(
    ~ r1_xboole_0(k3_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (5582)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (5594)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (5582)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (5586)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (5593)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  % (5579)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f26,f94,f105,f110])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    spl6_1 | spl6_8),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f109])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    $false | (spl6_1 | spl6_8)),
% 0.20/0.48    inference(subsumption_resolution,[],[f107,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ~r1_xboole_0(k3_tarski(sK0),sK1) | spl6_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    spl6_1 <=> r1_xboole_0(k3_tarski(sK0),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    r1_xboole_0(k3_tarski(sK0),sK1) | spl6_8),
% 0.20/0.48    inference(resolution,[],[f104,f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,plain,(
% 0.20/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    ~r2_hidden(sK2(k3_tarski(sK0),sK1),k3_tarski(sK0)) | spl6_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f102])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    spl6_8 <=> r2_hidden(sK2(k3_tarski(sK0),sK1),k3_tarski(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    ~spl6_8 | spl6_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f97,f91,f102])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    spl6_7 <=> sP4(sK2(k3_tarski(sK0),sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    ~r2_hidden(sK2(k3_tarski(sK0),sK1),k3_tarski(sK0)) | spl6_7),
% 0.20/0.48    inference(resolution,[],[f93,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X2,X0] : (sP4(X2,X0) | ~r2_hidden(X2,k3_tarski(X0))) )),
% 0.20/0.48    inference(equality_resolution,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (sP4(X2,X0) | ~r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    ~sP4(sK2(k3_tarski(sK0),sK1),sK0) | spl6_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f91])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ~spl6_7 | spl6_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f71,f23,f91])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ~sP4(sK2(k3_tarski(sK0),sK1),sK0) | spl6_1),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ~sP4(sK2(k3_tarski(sK0),sK1),sK0) | ~sP4(sK2(k3_tarski(sK0),sK1),sK0) | spl6_1),
% 0.20/0.48    inference(resolution,[],[f43,f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ( ! [X2,X0] : (r2_hidden(sK5(X0,X2),X0) | ~sP4(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X1] : (~r2_hidden(sK5(X1,sK2(k3_tarski(sK0),sK1)),sK0) | ~sP4(sK2(k3_tarski(sK0),sK1),X1)) ) | spl6_1),
% 0.20/0.48    inference(resolution,[],[f39,f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ( ! [X2,X0] : (r2_hidden(X2,sK5(X0,X2)) | ~sP4(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X3] : (~r2_hidden(sK2(k3_tarski(sK0),sK1),X3) | ~r2_hidden(X3,sK0)) ) | spl6_1),
% 0.20/0.48    inference(resolution,[],[f34,f25])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_xboole_0(X1,sK1) | ~r2_hidden(sK2(X1,sK1),X0) | ~r2_hidden(X0,sK0)) )),
% 0.20/0.48    inference(resolution,[],[f27,f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0) | ~r2_hidden(X1,X0)) )),
% 0.20/0.48    inference(resolution,[],[f8,f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ( ! [X2] : (r1_xboole_0(X2,sK1) | ~r2_hidden(X2,sK0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ? [X0,X1] : (~r1_xboole_0(k3_tarski(X0),X1) & ! [X2] : (r1_xboole_0(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_xboole_0(X2,X1)) => r1_xboole_0(k3_tarski(X0),X1))),
% 0.20/0.48    inference(negated_conjecture,[],[f3])).
% 0.20/0.48  fof(f3,conjecture,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_xboole_0(X2,X1)) => r1_xboole_0(k3_tarski(X0),X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ~spl6_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f9,f23])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ~r1_xboole_0(k3_tarski(sK0),sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (5582)------------------------------
% 0.20/0.48  % (5582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (5582)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (5582)Memory used [KB]: 10618
% 0.20/0.48  % (5582)Time elapsed: 0.057 s
% 0.20/0.48  % (5582)------------------------------
% 0.20/0.48  % (5582)------------------------------
% 0.20/0.48  % (5578)Success in time 0.128 s
%------------------------------------------------------------------------------
