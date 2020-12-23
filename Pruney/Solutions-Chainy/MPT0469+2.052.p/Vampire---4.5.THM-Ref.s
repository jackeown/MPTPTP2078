%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:41 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   60 (  96 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  197 ( 300 expanded)
%              Number of equality atoms :   35 (  48 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f47,f60,f79,f98,f116,f130])).

fof(f130,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f121,f58,f45])).

fof(f45,plain,
    ( spl6_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f58,plain,
    ( spl6_4
  <=> r2_hidden(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f121,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_4 ),
    inference(resolution,[],[f59,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

% (312)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f59,plain,
    ( r2_hidden(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f116,plain,
    ( ~ spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f102,f77,f45])).

fof(f77,plain,
    ( spl6_6
  <=> r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f102,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_6 ),
    inference(resolution,[],[f78,f24])).

fof(f78,plain,
    ( r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f98,plain,
    ( ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f83,f74,f45])).

fof(f74,plain,
    ( spl6_5
  <=> r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,sK3(k1_xboole_0,k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f83,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_5 ),
    inference(resolution,[],[f75,f24])).

fof(f75,plain,
    ( r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,sK3(k1_xboole_0,k1_xboole_0))),k1_xboole_0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f79,plain,
    ( spl6_5
    | spl6_6
    | ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f72,f41,f38,f77,f74])).

fof(f38,plain,
    ( spl6_1
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f41,plain,
    ( spl6_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f72,plain,
    ( r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,sK3(k1_xboole_0,k1_xboole_0))),k1_xboole_0)
    | ~ spl6_1
    | spl6_2 ),
    inference(trivial_inequality_removal,[],[f71])).

fof(f71,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,sK3(k1_xboole_0,k1_xboole_0))),k1_xboole_0)
    | ~ spl6_1
    | spl6_2 ),
    inference(superposition,[],[f42,f66])).

fof(f66,plain,
    ( ! [X5] :
        ( k1_xboole_0 = k2_relat_1(X5)
        | r2_hidden(k4_tarski(sK4(X5,k1_xboole_0),sK3(X5,k1_xboole_0)),X5)
        | r2_hidden(k4_tarski(sK3(X5,k1_xboole_0),sK2(k1_xboole_0,sK3(X5,k1_xboole_0))),k1_xboole_0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f31,f62])).

fof(f62,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | r2_hidden(k4_tarski(X0,sK2(k1_xboole_0,X0)),k1_xboole_0) )
    | ~ spl6_1 ),
    inference(superposition,[],[f34,f61])).

fof(f61,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f34,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14,f13,f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f17,f20,f19,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f42,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f60,plain,
    ( spl6_4
    | spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f56,f45,f38,f58])).

fof(f56,plain,
    ( r2_hidden(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | spl6_1
    | ~ spl6_3 ),
    inference(trivial_inequality_removal,[],[f54])).

fof(f54,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | spl6_1
    | ~ spl6_3 ),
    inference(superposition,[],[f39,f53])).

fof(f53,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relat_1(X0)
        | r2_hidden(k4_tarski(sK0(X0,k1_xboole_0),sK1(X0,k1_xboole_0)),X0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f49,f46])).

fof(f46,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f49,plain,(
    ! [X4,X3] :
      ( ~ v1_xboole_0(X4)
      | k1_relat_1(X3) = X4
      | r2_hidden(k4_tarski(sK0(X3,X4),sK1(X3,X4)),X3) ) ),
    inference(resolution,[],[f27,f24])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f47,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f43,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f22,f41,f38])).

fof(f22,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n016.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:32:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.45  % (306)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.18/0.45  % (32767)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.18/0.45  % (32767)Refutation found. Thanks to Tanya!
% 0.18/0.45  % SZS status Theorem for theBenchmark
% 0.18/0.46  % (307)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.18/0.46  % SZS output start Proof for theBenchmark
% 0.18/0.46  fof(f131,plain,(
% 0.18/0.46    $false),
% 0.18/0.46    inference(avatar_sat_refutation,[],[f43,f47,f60,f79,f98,f116,f130])).
% 0.18/0.46  fof(f130,plain,(
% 0.18/0.46    ~spl6_3 | ~spl6_4),
% 0.18/0.46    inference(avatar_split_clause,[],[f121,f58,f45])).
% 0.18/0.46  fof(f45,plain,(
% 0.18/0.46    spl6_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.18/0.46  fof(f58,plain,(
% 0.18/0.46    spl6_4 <=> r2_hidden(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.18/0.46  fof(f121,plain,(
% 0.18/0.46    ~v1_xboole_0(k1_xboole_0) | ~spl6_4),
% 0.18/0.46    inference(resolution,[],[f59,f24])).
% 0.18/0.46  fof(f24,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f9])).
% 0.18/0.46  fof(f9,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.18/0.46    inference(ennf_transformation,[],[f7])).
% 0.18/0.46  fof(f7,plain,(
% 0.18/0.46    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.18/0.46    inference(unused_predicate_definition_removal,[],[f1])).
% 0.18/0.46  % (312)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.18/0.46  fof(f1,axiom,(
% 0.18/0.46    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.18/0.46  fof(f59,plain,(
% 0.18/0.46    r2_hidden(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~spl6_4),
% 0.18/0.46    inference(avatar_component_clause,[],[f58])).
% 0.18/0.46  fof(f116,plain,(
% 0.18/0.46    ~spl6_3 | ~spl6_6),
% 0.18/0.46    inference(avatar_split_clause,[],[f102,f77,f45])).
% 0.18/0.46  fof(f77,plain,(
% 0.18/0.46    spl6_6 <=> r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.18/0.46  fof(f102,plain,(
% 0.18/0.46    ~v1_xboole_0(k1_xboole_0) | ~spl6_6),
% 0.18/0.46    inference(resolution,[],[f78,f24])).
% 0.18/0.46  fof(f78,plain,(
% 0.18/0.46    r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~spl6_6),
% 0.18/0.46    inference(avatar_component_clause,[],[f77])).
% 0.18/0.46  fof(f98,plain,(
% 0.18/0.46    ~spl6_3 | ~spl6_5),
% 0.18/0.46    inference(avatar_split_clause,[],[f83,f74,f45])).
% 0.18/0.46  fof(f74,plain,(
% 0.18/0.46    spl6_5 <=> r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,sK3(k1_xboole_0,k1_xboole_0))),k1_xboole_0)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.18/0.46  fof(f83,plain,(
% 0.18/0.46    ~v1_xboole_0(k1_xboole_0) | ~spl6_5),
% 0.18/0.46    inference(resolution,[],[f75,f24])).
% 0.18/0.46  fof(f75,plain,(
% 0.18/0.46    r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,sK3(k1_xboole_0,k1_xboole_0))),k1_xboole_0) | ~spl6_5),
% 0.18/0.46    inference(avatar_component_clause,[],[f74])).
% 0.18/0.46  fof(f79,plain,(
% 0.18/0.46    spl6_5 | spl6_6 | ~spl6_1 | spl6_2),
% 0.18/0.46    inference(avatar_split_clause,[],[f72,f41,f38,f77,f74])).
% 0.18/0.46  fof(f38,plain,(
% 0.18/0.46    spl6_1 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.18/0.46  fof(f41,plain,(
% 0.18/0.46    spl6_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.18/0.46  fof(f72,plain,(
% 0.18/0.46    r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,sK3(k1_xboole_0,k1_xboole_0))),k1_xboole_0) | (~spl6_1 | spl6_2)),
% 0.18/0.46    inference(trivial_inequality_removal,[],[f71])).
% 0.18/0.46  fof(f71,plain,(
% 0.18/0.46    k1_xboole_0 != k1_xboole_0 | r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK3(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK3(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,sK3(k1_xboole_0,k1_xboole_0))),k1_xboole_0) | (~spl6_1 | spl6_2)),
% 0.18/0.46    inference(superposition,[],[f42,f66])).
% 0.18/0.46  fof(f66,plain,(
% 0.18/0.46    ( ! [X5] : (k1_xboole_0 = k2_relat_1(X5) | r2_hidden(k4_tarski(sK4(X5,k1_xboole_0),sK3(X5,k1_xboole_0)),X5) | r2_hidden(k4_tarski(sK3(X5,k1_xboole_0),sK2(k1_xboole_0,sK3(X5,k1_xboole_0))),k1_xboole_0)) ) | ~spl6_1),
% 0.18/0.46    inference(resolution,[],[f31,f62])).
% 0.18/0.46  fof(f62,plain,(
% 0.18/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(k4_tarski(X0,sK2(k1_xboole_0,X0)),k1_xboole_0)) ) | ~spl6_1),
% 0.18/0.46    inference(superposition,[],[f34,f61])).
% 0.18/0.46  fof(f61,plain,(
% 0.18/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_1),
% 0.18/0.46    inference(avatar_component_clause,[],[f38])).
% 0.18/0.46  fof(f34,plain,(
% 0.18/0.46    ( ! [X0,X5] : (~r2_hidden(X5,k1_relat_1(X0)) | r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)) )),
% 0.18/0.46    inference(equality_resolution,[],[f25])).
% 0.18/0.46  fof(f25,plain,(
% 0.18/0.46    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.18/0.46    inference(cnf_transformation,[],[f15])).
% 0.18/0.46  fof(f15,plain,(
% 0.18/0.46    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.18/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14,f13,f12])).
% 0.18/0.46  fof(f12,plain,(
% 0.18/0.46    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK0(X0,X1),X3),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 0.18/0.46    introduced(choice_axiom,[])).
% 0.18/0.46  fof(f13,plain,(
% 0.18/0.46    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0))),
% 0.18/0.46    introduced(choice_axiom,[])).
% 0.18/0.46  fof(f14,plain,(
% 0.18/0.46    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0))),
% 0.18/0.46    introduced(choice_axiom,[])).
% 0.18/0.46  fof(f11,plain,(
% 0.18/0.46    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.18/0.46    inference(rectify,[],[f10])).
% 0.18/0.46  fof(f10,plain,(
% 0.18/0.46    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.18/0.46    inference(nnf_transformation,[],[f3])).
% 0.18/0.46  fof(f3,axiom,(
% 0.18/0.46    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.18/0.46  fof(f31,plain,(
% 0.18/0.46    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | k2_relat_1(X0) = X1) )),
% 0.18/0.46    inference(cnf_transformation,[],[f21])).
% 0.18/0.46  fof(f21,plain,(
% 0.18/0.46    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.18/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f17,f20,f19,f18])).
% 0.18/0.46  fof(f18,plain,(
% 0.18/0.46    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.18/0.46    introduced(choice_axiom,[])).
% 0.18/0.46  fof(f19,plain,(
% 0.18/0.46    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 0.18/0.46    introduced(choice_axiom,[])).
% 0.18/0.46  fof(f20,plain,(
% 0.18/0.46    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 0.18/0.46    introduced(choice_axiom,[])).
% 0.18/0.46  fof(f17,plain,(
% 0.18/0.46    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.18/0.46    inference(rectify,[],[f16])).
% 0.18/0.46  fof(f16,plain,(
% 0.18/0.46    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.18/0.46    inference(nnf_transformation,[],[f4])).
% 0.18/0.46  fof(f4,axiom,(
% 0.18/0.46    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.18/0.46  fof(f42,plain,(
% 0.18/0.46    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl6_2),
% 0.18/0.46    inference(avatar_component_clause,[],[f41])).
% 0.18/0.46  fof(f60,plain,(
% 0.18/0.46    spl6_4 | spl6_1 | ~spl6_3),
% 0.18/0.46    inference(avatar_split_clause,[],[f56,f45,f38,f58])).
% 0.18/0.46  fof(f56,plain,(
% 0.18/0.46    r2_hidden(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | (spl6_1 | ~spl6_3)),
% 0.18/0.46    inference(trivial_inequality_removal,[],[f54])).
% 0.18/0.46  fof(f54,plain,(
% 0.18/0.46    k1_xboole_0 != k1_xboole_0 | r2_hidden(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | (spl6_1 | ~spl6_3)),
% 0.18/0.46    inference(superposition,[],[f39,f53])).
% 0.18/0.46  fof(f53,plain,(
% 0.18/0.46    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | r2_hidden(k4_tarski(sK0(X0,k1_xboole_0),sK1(X0,k1_xboole_0)),X0)) ) | ~spl6_3),
% 0.18/0.46    inference(resolution,[],[f49,f46])).
% 0.18/0.46  fof(f46,plain,(
% 0.18/0.46    v1_xboole_0(k1_xboole_0) | ~spl6_3),
% 0.18/0.46    inference(avatar_component_clause,[],[f45])).
% 0.18/0.46  fof(f49,plain,(
% 0.18/0.46    ( ! [X4,X3] : (~v1_xboole_0(X4) | k1_relat_1(X3) = X4 | r2_hidden(k4_tarski(sK0(X3,X4),sK1(X3,X4)),X3)) )),
% 0.18/0.46    inference(resolution,[],[f27,f24])).
% 0.18/0.46  fof(f27,plain,(
% 0.18/0.46    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0) | k1_relat_1(X0) = X1) )),
% 0.18/0.46    inference(cnf_transformation,[],[f15])).
% 0.18/0.46  fof(f39,plain,(
% 0.18/0.46    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl6_1),
% 0.18/0.46    inference(avatar_component_clause,[],[f38])).
% 0.18/0.46  fof(f47,plain,(
% 0.18/0.46    spl6_3),
% 0.18/0.46    inference(avatar_split_clause,[],[f23,f45])).
% 0.18/0.46  fof(f23,plain,(
% 0.18/0.46    v1_xboole_0(k1_xboole_0)),
% 0.18/0.46    inference(cnf_transformation,[],[f2])).
% 0.18/0.46  fof(f2,axiom,(
% 0.18/0.46    v1_xboole_0(k1_xboole_0)),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.18/0.46  fof(f43,plain,(
% 0.18/0.46    ~spl6_1 | ~spl6_2),
% 0.18/0.46    inference(avatar_split_clause,[],[f22,f41,f38])).
% 0.18/0.46  fof(f22,plain,(
% 0.18/0.46    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.18/0.46    inference(cnf_transformation,[],[f8])).
% 0.18/0.46  fof(f8,plain,(
% 0.18/0.46    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.18/0.46    inference(ennf_transformation,[],[f6])).
% 0.18/0.46  fof(f6,negated_conjecture,(
% 0.18/0.46    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.18/0.46    inference(negated_conjecture,[],[f5])).
% 0.18/0.46  fof(f5,conjecture,(
% 0.18/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.18/0.46  % SZS output end Proof for theBenchmark
% 0.18/0.46  % (32767)------------------------------
% 0.18/0.46  % (32767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (32767)Termination reason: Refutation
% 0.18/0.46  
% 0.18/0.46  % (32767)Memory used [KB]: 10618
% 0.18/0.46  % (32767)Time elapsed: 0.056 s
% 0.18/0.46  % (32767)------------------------------
% 0.18/0.46  % (32767)------------------------------
% 0.18/0.46  % (32760)Success in time 0.12 s
%------------------------------------------------------------------------------
