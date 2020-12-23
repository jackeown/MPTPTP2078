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
% DateTime   : Thu Dec  3 12:41:38 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   59 (  90 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  217 ( 348 expanded)
%              Number of equality atoms :   34 (  61 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f143,f148])).

fof(f148,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f144,f61])).

fof(f61,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(X0,sK1),sK0) ),
    inference(superposition,[],[f56,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f56,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(sK1,X0),sK0) ),
    inference(resolution,[],[f53,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f53,plain,(
    ~ r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f27,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ( ~ r1_tarski(X1,X0)
        & ~ r1_tarski(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) )
     => r3_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f27,plain,(
    ~ r3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    & k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ~ r3_xboole_0(X0,X1)
        & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) )
   => ( ~ r3_xboole_0(sK0,sK1)
      & k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))
       => r3_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))
     => r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_zfmisc_1)).

fof(f144,plain,
    ( r1_tarski(k2_xboole_0(sK0,sK1),sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f132,f48])).

fof(f48,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f132,plain,
    ( r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl4_1
  <=> r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f143,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f139,f55])).

fof(f55,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),sK1) ),
    inference(resolution,[],[f52,f34])).

fof(f52,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f27,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f139,plain,
    ( r1_tarski(k2_xboole_0(sK0,sK1),sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f136,f48])).

% (31924)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f136,plain,
    ( r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl4_2
  <=> r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f138,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f126,f134,f130])).

fof(f126,plain,
    ( r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK1))
    | r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f79,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f79,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(sK0,sK1))
      | r2_hidden(X0,k1_zfmisc_1(sK1))
      | r2_hidden(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f54,f47])).

fof(f47,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK0,sK1)))
      | r2_hidden(X0,k1_zfmisc_1(sK0))
      | r2_hidden(X0,k1_zfmisc_1(sK1)) ) ),
    inference(superposition,[],[f51,f26])).

fof(f26,plain,(
    k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:55:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (31933)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.46  % (31927)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (31915)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (31935)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (31936)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (31922)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (31918)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (31919)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (31932)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (31916)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (31937)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (31921)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (31929)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (31925)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (31923)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.31/0.52  % (31921)Refutation found. Thanks to Tanya!
% 1.31/0.52  % SZS status Theorem for theBenchmark
% 1.31/0.52  % SZS output start Proof for theBenchmark
% 1.31/0.52  fof(f149,plain,(
% 1.31/0.52    $false),
% 1.31/0.52    inference(avatar_sat_refutation,[],[f138,f143,f148])).
% 1.31/0.52  fof(f148,plain,(
% 1.31/0.52    ~spl4_1),
% 1.31/0.52    inference(avatar_contradiction_clause,[],[f147])).
% 1.31/0.52  fof(f147,plain,(
% 1.31/0.52    $false | ~spl4_1),
% 1.31/0.52    inference(subsumption_resolution,[],[f144,f61])).
% 1.31/0.52  fof(f61,plain,(
% 1.31/0.52    ( ! [X0] : (~r1_tarski(k2_xboole_0(X0,sK1),sK0)) )),
% 1.31/0.52    inference(superposition,[],[f56,f33])).
% 1.31/0.52  fof(f33,plain,(
% 1.31/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f1])).
% 1.31/0.52  fof(f1,axiom,(
% 1.31/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.31/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.31/0.52  fof(f56,plain,(
% 1.31/0.52    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK1,X0),sK0)) )),
% 1.31/0.52    inference(resolution,[],[f53,f34])).
% 1.31/0.52  fof(f34,plain,(
% 1.31/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f12])).
% 1.31/0.52  fof(f12,plain,(
% 1.31/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.31/0.52    inference(ennf_transformation,[],[f5])).
% 1.31/0.52  fof(f5,axiom,(
% 1.31/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.31/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.31/0.52  fof(f53,plain,(
% 1.31/0.52    ~r1_tarski(sK1,sK0)),
% 1.31/0.52    inference(resolution,[],[f27,f29])).
% 1.31/0.52  fof(f29,plain,(
% 1.31/0.52    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f11])).
% 1.31/0.52  fof(f11,plain,(
% 1.31/0.52    ! [X0,X1] : (r3_xboole_0(X0,X1) | (~r1_tarski(X1,X0) & ~r1_tarski(X0,X1)))),
% 1.31/0.52    inference(ennf_transformation,[],[f9])).
% 1.31/0.52  fof(f9,plain,(
% 1.31/0.52    ! [X0,X1] : ((r1_tarski(X1,X0) | r1_tarski(X0,X1)) => r3_xboole_0(X0,X1))),
% 1.31/0.52    inference(unused_predicate_definition_removal,[],[f4])).
% 1.31/0.52  fof(f4,axiom,(
% 1.31/0.52    ! [X0,X1] : (r3_xboole_0(X0,X1) <=> (r1_tarski(X1,X0) | r1_tarski(X0,X1)))),
% 1.31/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).
% 1.31/0.52  fof(f27,plain,(
% 1.31/0.52    ~r3_xboole_0(sK0,sK1)),
% 1.31/0.52    inference(cnf_transformation,[],[f14])).
% 1.31/0.52  fof(f14,plain,(
% 1.31/0.52    ~r3_xboole_0(sK0,sK1) & k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1))),
% 1.31/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f13])).
% 1.31/0.52  fof(f13,plain,(
% 1.31/0.52    ? [X0,X1] : (~r3_xboole_0(X0,X1) & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))) => (~r3_xboole_0(sK0,sK1) & k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 1.31/0.52    introduced(choice_axiom,[])).
% 1.31/0.52  fof(f10,plain,(
% 1.31/0.52    ? [X0,X1] : (~r3_xboole_0(X0,X1) & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 1.31/0.52    inference(ennf_transformation,[],[f8])).
% 1.31/0.52  fof(f8,negated_conjecture,(
% 1.31/0.52    ~! [X0,X1] : (k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) => r3_xboole_0(X0,X1))),
% 1.31/0.52    inference(negated_conjecture,[],[f7])).
% 1.31/0.52  fof(f7,conjecture,(
% 1.31/0.52    ! [X0,X1] : (k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) => r3_xboole_0(X0,X1))),
% 1.31/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_zfmisc_1)).
% 1.31/0.52  fof(f144,plain,(
% 1.31/0.52    r1_tarski(k2_xboole_0(sK0,sK1),sK0) | ~spl4_1),
% 1.31/0.52    inference(resolution,[],[f132,f48])).
% 1.31/0.52  fof(f48,plain,(
% 1.31/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.31/0.52    inference(equality_resolution,[],[f35])).
% 1.31/0.52  fof(f35,plain,(
% 1.31/0.52    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.31/0.52    inference(cnf_transformation,[],[f20])).
% 1.31/0.52  fof(f20,plain,(
% 1.31/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.31/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 1.31/0.52  fof(f19,plain,(
% 1.31/0.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.31/0.52    introduced(choice_axiom,[])).
% 1.31/0.52  fof(f18,plain,(
% 1.31/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.31/0.52    inference(rectify,[],[f17])).
% 1.31/0.52  fof(f17,plain,(
% 1.31/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.31/0.52    inference(nnf_transformation,[],[f6])).
% 1.31/0.52  fof(f6,axiom,(
% 1.31/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.31/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.31/0.52  fof(f132,plain,(
% 1.31/0.52    r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl4_1),
% 1.31/0.52    inference(avatar_component_clause,[],[f130])).
% 1.31/0.52  fof(f130,plain,(
% 1.31/0.52    spl4_1 <=> r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.31/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.31/0.52  fof(f143,plain,(
% 1.31/0.52    ~spl4_2),
% 1.31/0.52    inference(avatar_contradiction_clause,[],[f142])).
% 1.31/0.52  fof(f142,plain,(
% 1.31/0.52    $false | ~spl4_2),
% 1.31/0.52    inference(subsumption_resolution,[],[f139,f55])).
% 1.31/0.52  fof(f55,plain,(
% 1.31/0.52    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,X0),sK1)) )),
% 1.31/0.52    inference(resolution,[],[f52,f34])).
% 1.31/0.52  fof(f52,plain,(
% 1.31/0.52    ~r1_tarski(sK0,sK1)),
% 1.31/0.52    inference(resolution,[],[f27,f28])).
% 1.31/0.52  fof(f28,plain,(
% 1.31/0.52    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f11])).
% 1.31/0.52  fof(f139,plain,(
% 1.31/0.52    r1_tarski(k2_xboole_0(sK0,sK1),sK1) | ~spl4_2),
% 1.31/0.52    inference(resolution,[],[f136,f48])).
% 1.31/0.52  % (31924)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.31/0.52  fof(f136,plain,(
% 1.31/0.52    r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl4_2),
% 1.31/0.52    inference(avatar_component_clause,[],[f134])).
% 1.31/0.52  fof(f134,plain,(
% 1.31/0.52    spl4_2 <=> r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK1))),
% 1.31/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.31/0.52  fof(f138,plain,(
% 1.31/0.52    spl4_1 | spl4_2),
% 1.31/0.52    inference(avatar_split_clause,[],[f126,f134,f130])).
% 1.31/0.52  fof(f126,plain,(
% 1.31/0.52    r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK1)) | r2_hidden(k2_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.31/0.52    inference(resolution,[],[f79,f45])).
% 1.31/0.52  fof(f45,plain,(
% 1.31/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.31/0.52    inference(equality_resolution,[],[f31])).
% 1.31/0.52  fof(f31,plain,(
% 1.31/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.31/0.52    inference(cnf_transformation,[],[f16])).
% 1.31/0.52  fof(f16,plain,(
% 1.31/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.31/0.52    inference(flattening,[],[f15])).
% 1.31/0.52  fof(f15,plain,(
% 1.31/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.31/0.52    inference(nnf_transformation,[],[f3])).
% 1.31/0.52  fof(f3,axiom,(
% 1.31/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.31/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.31/0.52  fof(f79,plain,(
% 1.31/0.52    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK0,sK1)) | r2_hidden(X0,k1_zfmisc_1(sK1)) | r2_hidden(X0,k1_zfmisc_1(sK0))) )),
% 1.31/0.52    inference(resolution,[],[f54,f47])).
% 1.31/0.52  fof(f47,plain,(
% 1.31/0.52    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.31/0.52    inference(equality_resolution,[],[f36])).
% 1.31/0.52  fof(f36,plain,(
% 1.31/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.31/0.52    inference(cnf_transformation,[],[f20])).
% 1.31/0.52  fof(f54,plain,(
% 1.31/0.52    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK0,sK1))) | r2_hidden(X0,k1_zfmisc_1(sK0)) | r2_hidden(X0,k1_zfmisc_1(sK1))) )),
% 1.31/0.52    inference(superposition,[],[f51,f26])).
% 1.31/0.52  fof(f26,plain,(
% 1.31/0.52    k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) = k1_zfmisc_1(k2_xboole_0(sK0,sK1))),
% 1.31/0.52    inference(cnf_transformation,[],[f14])).
% 1.31/0.52  fof(f51,plain,(
% 1.31/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_xboole_0(X0,X1)) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 1.31/0.52    inference(equality_resolution,[],[f39])).
% 1.31/0.52  fof(f39,plain,(
% 1.31/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.31/0.52    inference(cnf_transformation,[],[f25])).
% 1.31/0.52  fof(f25,plain,(
% 1.31/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.31/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 1.31/0.52  fof(f24,plain,(
% 1.31/0.52    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.31/0.52    introduced(choice_axiom,[])).
% 1.31/0.52  fof(f23,plain,(
% 1.31/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.31/0.52    inference(rectify,[],[f22])).
% 1.31/0.52  fof(f22,plain,(
% 1.31/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.31/0.52    inference(flattening,[],[f21])).
% 1.31/0.52  fof(f21,plain,(
% 1.31/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.31/0.52    inference(nnf_transformation,[],[f2])).
% 1.31/0.52  fof(f2,axiom,(
% 1.31/0.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.31/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.31/0.52  % SZS output end Proof for theBenchmark
% 1.31/0.52  % (31921)------------------------------
% 1.31/0.52  % (31921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.52  % (31921)Termination reason: Refutation
% 1.31/0.52  
% 1.31/0.52  % (31921)Memory used [KB]: 10618
% 1.31/0.52  % (31921)Time elapsed: 0.073 s
% 1.31/0.52  % (31921)------------------------------
% 1.31/0.52  % (31921)------------------------------
% 1.31/0.52  % (31917)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.31/0.52  % (31914)Success in time 0.169 s
%------------------------------------------------------------------------------
