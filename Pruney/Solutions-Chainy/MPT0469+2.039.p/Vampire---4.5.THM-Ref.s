%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:39 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 109 expanded)
%              Number of leaves         :   20 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  166 ( 293 expanded)
%              Number of equality atoms :   32 (  50 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f65,f72,f80,f91,f100])).

fof(f100,plain,
    ( spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f98,f70,f51])).

fof(f51,plain,
    ( spl7_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f70,plain,
    ( spl7_4
  <=> ! [X3] : ~ r2_hidden(X3,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f98,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_4 ),
    inference(resolution,[],[f71,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f71,plain,
    ( ! [X3] : ~ r2_hidden(X3,k2_relat_1(k1_xboole_0))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f91,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | ~ spl7_5 ),
    inference(resolution,[],[f79,f55])).

fof(f55,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f54,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f54,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f39,f33])).

fof(f33,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f79,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl7_5
  <=> r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f80,plain,
    ( spl7_5
    | spl7_3 ),
    inference(avatar_split_clause,[],[f76,f67,f78])).

fof(f67,plain,
    ( spl7_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f76,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | spl7_3 ),
    inference(resolution,[],[f68,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f68,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f72,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f63,f70,f67])).

fof(f63,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f58,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f24])).

fof(f24,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK3(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

fof(f58,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f46,f55])).

fof(f46,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f27,f30,f29,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f65,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f62,f48])).

fof(f48,plain,
    ( spl7_1
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f62,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f58,f37])).

fof(f53,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f32,f51,f48])).

fof(f32,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n002.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 12:14:22 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.17/0.38  % (12417)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.17/0.38  % (12417)Refutation not found, incomplete strategy% (12417)------------------------------
% 0.17/0.38  % (12417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.38  % (12417)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.38  
% 0.17/0.38  % (12417)Memory used [KB]: 1663
% 0.17/0.38  % (12417)Time elapsed: 0.002 s
% 0.17/0.38  % (12417)------------------------------
% 0.17/0.38  % (12417)------------------------------
% 0.17/0.39  % (12418)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.17/0.40  % (12414)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.17/0.40  % (12434)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.17/0.40  % (12414)Refutation not found, incomplete strategy% (12414)------------------------------
% 0.17/0.40  % (12414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.40  % (12414)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.40  
% 0.17/0.40  % (12414)Memory used [KB]: 10490
% 0.17/0.40  % (12414)Time elapsed: 0.025 s
% 0.17/0.40  % (12414)------------------------------
% 0.17/0.40  % (12414)------------------------------
% 0.17/0.40  % (12434)Refutation not found, incomplete strategy% (12434)------------------------------
% 0.17/0.40  % (12434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.40  % (12434)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.40  
% 0.17/0.40  % (12434)Memory used [KB]: 10490
% 0.17/0.40  % (12434)Time elapsed: 0.034 s
% 0.17/0.40  % (12434)------------------------------
% 0.17/0.40  % (12434)------------------------------
% 0.17/0.42  % (12421)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.17/0.43  % (12425)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.17/0.45  % (12419)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.17/0.45  % (12419)Refutation found. Thanks to Tanya!
% 0.17/0.45  % SZS status Theorem for theBenchmark
% 0.17/0.45  % SZS output start Proof for theBenchmark
% 0.17/0.45  fof(f101,plain,(
% 0.17/0.45    $false),
% 0.17/0.45    inference(avatar_sat_refutation,[],[f53,f65,f72,f80,f91,f100])).
% 0.17/0.45  fof(f100,plain,(
% 0.17/0.45    spl7_2 | ~spl7_4),
% 0.17/0.45    inference(avatar_split_clause,[],[f98,f70,f51])).
% 0.17/0.45  fof(f51,plain,(
% 0.17/0.45    spl7_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.17/0.45  fof(f70,plain,(
% 0.17/0.45    spl7_4 <=> ! [X3] : ~r2_hidden(X3,k2_relat_1(k1_xboole_0))),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.17/0.45  fof(f98,plain,(
% 0.17/0.45    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl7_4),
% 0.17/0.45    inference(resolution,[],[f71,f37])).
% 0.17/0.45  fof(f37,plain,(
% 0.17/0.45    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.17/0.45    inference(cnf_transformation,[],[f21])).
% 0.17/0.45  fof(f21,plain,(
% 0.17/0.45    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.17/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f20])).
% 0.17/0.45  fof(f20,plain,(
% 0.17/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.17/0.45    introduced(choice_axiom,[])).
% 0.17/0.45  fof(f14,plain,(
% 0.17/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.17/0.45    inference(ennf_transformation,[],[f2])).
% 0.17/0.45  fof(f2,axiom,(
% 0.17/0.45    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.17/0.45  fof(f71,plain,(
% 0.17/0.45    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(k1_xboole_0))) ) | ~spl7_4),
% 0.17/0.45    inference(avatar_component_clause,[],[f70])).
% 0.17/0.45  fof(f91,plain,(
% 0.17/0.45    ~spl7_5),
% 0.17/0.45    inference(avatar_contradiction_clause,[],[f90])).
% 0.17/0.45  fof(f90,plain,(
% 0.17/0.45    $false | ~spl7_5),
% 0.17/0.45    inference(resolution,[],[f79,f55])).
% 0.17/0.45  fof(f55,plain,(
% 0.17/0.45    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.17/0.45    inference(forward_demodulation,[],[f54,f34])).
% 0.17/0.45  fof(f34,plain,(
% 0.17/0.45    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f3])).
% 0.17/0.45  fof(f3,axiom,(
% 0.17/0.45    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.17/0.45  fof(f54,plain,(
% 0.17/0.45    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 0.17/0.45    inference(resolution,[],[f39,f33])).
% 0.17/0.45  fof(f33,plain,(
% 0.17/0.45    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f4])).
% 0.17/0.45  fof(f4,axiom,(
% 0.17/0.45    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.17/0.45  fof(f39,plain,(
% 0.17/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.17/0.45    inference(cnf_transformation,[],[f23])).
% 0.17/0.45  fof(f23,plain,(
% 0.17/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.17/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f22])).
% 0.17/0.45  fof(f22,plain,(
% 0.17/0.45    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.17/0.45    introduced(choice_axiom,[])).
% 0.17/0.45  fof(f15,plain,(
% 0.17/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.17/0.45    inference(ennf_transformation,[],[f10])).
% 0.17/0.45  fof(f10,plain,(
% 0.17/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.17/0.45    inference(rectify,[],[f1])).
% 0.17/0.45  fof(f1,axiom,(
% 0.17/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.17/0.45  fof(f79,plain,(
% 0.17/0.45    r2_hidden(sK0(k1_xboole_0),k1_xboole_0) | ~spl7_5),
% 0.17/0.45    inference(avatar_component_clause,[],[f78])).
% 0.17/0.45  fof(f78,plain,(
% 0.17/0.45    spl7_5 <=> r2_hidden(sK0(k1_xboole_0),k1_xboole_0)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.17/0.45  fof(f80,plain,(
% 0.17/0.45    spl7_5 | spl7_3),
% 0.17/0.45    inference(avatar_split_clause,[],[f76,f67,f78])).
% 0.17/0.45  fof(f67,plain,(
% 0.17/0.45    spl7_3 <=> v1_relat_1(k1_xboole_0)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.17/0.45  fof(f76,plain,(
% 0.17/0.45    r2_hidden(sK0(k1_xboole_0),k1_xboole_0) | spl7_3),
% 0.17/0.45    inference(resolution,[],[f68,f35])).
% 0.17/0.45  fof(f35,plain,(
% 0.17/0.45    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK0(X0),X0)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f19])).
% 0.17/0.45  fof(f19,plain,(
% 0.17/0.45    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 0.17/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f18])).
% 0.17/0.45  fof(f18,plain,(
% 0.17/0.45    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 0.17/0.45    introduced(choice_axiom,[])).
% 0.17/0.45  fof(f13,plain,(
% 0.17/0.45    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.17/0.45    inference(ennf_transformation,[],[f11])).
% 0.17/0.45  fof(f11,plain,(
% 0.17/0.45    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.17/0.45    inference(unused_predicate_definition_removal,[],[f5])).
% 0.17/0.45  fof(f5,axiom,(
% 0.17/0.45    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.17/0.45  fof(f68,plain,(
% 0.17/0.45    ~v1_relat_1(k1_xboole_0) | spl7_3),
% 0.17/0.45    inference(avatar_component_clause,[],[f67])).
% 0.17/0.45  fof(f72,plain,(
% 0.17/0.45    ~spl7_3 | spl7_4),
% 0.17/0.45    inference(avatar_split_clause,[],[f63,f70,f67])).
% 0.17/0.45  fof(f63,plain,(
% 0.17/0.45    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) )),
% 0.17/0.45    inference(resolution,[],[f58,f40])).
% 0.17/0.45  fof(f40,plain,(
% 0.17/0.45    ( ! [X0,X1] : (r2_hidden(sK3(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.17/0.45    inference(cnf_transformation,[],[f25])).
% 0.17/0.45  fof(f25,plain,(
% 0.17/0.45    ! [X0,X1] : (r2_hidden(sK3(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.17/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f24])).
% 0.17/0.45  fof(f24,plain,(
% 0.17/0.45    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK3(X1),k1_relat_1(X1)))),
% 0.17/0.45    introduced(choice_axiom,[])).
% 0.17/0.45  fof(f17,plain,(
% 0.17/0.45    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.17/0.45    inference(flattening,[],[f16])).
% 0.17/0.45  fof(f16,plain,(
% 0.17/0.45    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.17/0.45    inference(ennf_transformation,[],[f7])).
% 0.17/0.45  fof(f7,axiom,(
% 0.17/0.45    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).
% 0.17/0.45  fof(f58,plain,(
% 0.17/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 0.17/0.45    inference(resolution,[],[f46,f55])).
% 0.17/0.45  fof(f46,plain,(
% 0.17/0.45    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 0.17/0.45    inference(equality_resolution,[],[f41])).
% 0.17/0.45  fof(f41,plain,(
% 0.17/0.45    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.17/0.45    inference(cnf_transformation,[],[f31])).
% 0.17/0.45  fof(f31,plain,(
% 0.17/0.45    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.17/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f27,f30,f29,f28])).
% 0.17/0.45  fof(f28,plain,(
% 0.17/0.45    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.17/0.45    introduced(choice_axiom,[])).
% 0.17/0.45  fof(f29,plain,(
% 0.17/0.45    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))),
% 0.17/0.45    introduced(choice_axiom,[])).
% 0.17/0.45  fof(f30,plain,(
% 0.17/0.45    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0))),
% 0.17/0.45    introduced(choice_axiom,[])).
% 0.17/0.45  fof(f27,plain,(
% 0.17/0.45    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.17/0.45    inference(rectify,[],[f26])).
% 0.17/0.45  fof(f26,plain,(
% 0.17/0.45    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.17/0.45    inference(nnf_transformation,[],[f6])).
% 0.17/0.45  fof(f6,axiom,(
% 0.17/0.45    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.17/0.45  fof(f65,plain,(
% 0.17/0.45    spl7_1),
% 0.17/0.45    inference(avatar_split_clause,[],[f62,f48])).
% 0.17/0.45  fof(f48,plain,(
% 0.17/0.45    spl7_1 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.17/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.17/0.45  fof(f62,plain,(
% 0.17/0.45    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.17/0.45    inference(resolution,[],[f58,f37])).
% 0.17/0.45  fof(f53,plain,(
% 0.17/0.45    ~spl7_1 | ~spl7_2),
% 0.17/0.45    inference(avatar_split_clause,[],[f32,f51,f48])).
% 0.17/0.45  fof(f32,plain,(
% 0.17/0.45    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.17/0.45    inference(cnf_transformation,[],[f12])).
% 0.17/0.45  fof(f12,plain,(
% 0.17/0.45    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.17/0.45    inference(ennf_transformation,[],[f9])).
% 0.17/0.45  fof(f9,negated_conjecture,(
% 0.17/0.45    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.17/0.45    inference(negated_conjecture,[],[f8])).
% 0.17/0.45  fof(f8,conjecture,(
% 0.17/0.45    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.17/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.17/0.45  % SZS output end Proof for theBenchmark
% 0.17/0.45  % (12419)------------------------------
% 0.17/0.45  % (12419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.45  % (12419)Termination reason: Refutation
% 0.17/0.45  
% 0.17/0.45  % (12419)Memory used [KB]: 10618
% 0.17/0.45  % (12419)Time elapsed: 0.062 s
% 0.17/0.45  % (12419)------------------------------
% 0.17/0.45  % (12419)------------------------------
% 0.17/0.45  % (12410)Success in time 0.125 s
%------------------------------------------------------------------------------
