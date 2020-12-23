%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 114 expanded)
%              Number of leaves         :   20 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :  202 ( 338 expanded)
%              Number of equality atoms :   68 ( 143 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f532,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f90,f181,f359,f496,f503,f518,f531])).

fof(f531,plain,
    ( spl5_1
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f530])).

fof(f530,plain,
    ( $false
    | spl5_1
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f528,f84])).

fof(f84,plain,
    ( sK0 != sK1
    | spl5_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f528,plain,
    ( sK0 = sK1
    | ~ spl5_19 ),
    inference(resolution,[],[f517,f80])).

fof(f80,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
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

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f517,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f515])).

fof(f515,plain,
    ( spl5_19
  <=> r2_hidden(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f518,plain,
    ( spl5_19
    | spl5_17 ),
    inference(avatar_split_clause,[],[f513,f500,f515])).

fof(f500,plain,
    ( spl5_17
  <=> r2_hidden(sK1,k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f513,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | spl5_17 ),
    inference(subsumption_resolution,[],[f512,f79])).

fof(f79,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f512,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | spl5_17 ),
    inference(resolution,[],[f502,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f502,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f500])).

fof(f503,plain,
    ( ~ spl5_17
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f497,f493,f341,f500])).

fof(f341,plain,
    ( spl5_13
  <=> ! [X5] :
        ( ~ r1_xboole_0(X5,k1_tarski(sK0))
        | ~ r2_hidden(sK1,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f493,plain,
    ( spl5_16
  <=> k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f497,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(superposition,[],[f407,f495])).

fof(f495,plain,
    ( k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f493])).

fof(f407,plain,
    ( ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(X0,k1_tarski(sK0)))
    | ~ spl5_13 ),
    inference(resolution,[],[f342,f69])).

fof(f69,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f342,plain,
    ( ! [X5] :
        ( ~ r1_xboole_0(X5,k1_tarski(sK0))
        | ~ r2_hidden(sK1,X5) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f341])).

fof(f496,plain,
    ( spl5_16
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f480,f87,f493])).

fof(f87,plain,
    ( spl5_2
  <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f480,plain,
    ( k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | ~ spl5_2 ),
    inference(superposition,[],[f137,f89])).

fof(f89,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f137,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f57,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f359,plain,
    ( spl5_13
    | spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f349,f87,f101,f341])).

fof(f101,plain,
    ( spl5_4
  <=> ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f349,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_tarski(sK0))
        | ~ r1_xboole_0(X0,k1_tarski(sK0))
        | ~ r2_hidden(sK1,X0) )
    | ~ spl5_2 ),
    inference(superposition,[],[f93,f244])).

fof(f244,plain,
    ( ! [X0] :
        ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),X0)
        | ~ r2_hidden(sK1,X0) )
    | ~ spl5_2 ),
    inference(superposition,[],[f240,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f240,plain,
    ( ! [X3] : k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X3))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f231,f89])).

fof(f231,plain,
    ( ! [X3] : k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X3))
    | ~ spl5_2 ),
    inference(superposition,[],[f182,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f182,plain,
    ( ! [X0] : k3_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),X0)) = k3_xboole_0(k1_tarski(sK0),X0)
    | ~ spl5_2 ),
    inference(superposition,[],[f49,f89])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f93,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X2,X1))
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(superposition,[],[f56,f54])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f181,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f79,f102])).

fof(f102,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f90,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f39,f87])).

fof(f39,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f85,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f40,f82])).

fof(f40,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (32162)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (32173)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (32182)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (32181)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.56  % (32158)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.56  % (32166)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.57  % (32169)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.57  % (32181)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f532,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f85,f90,f181,f359,f496,f503,f518,f531])).
% 0.20/0.57  fof(f531,plain,(
% 0.20/0.57    spl5_1 | ~spl5_19),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f530])).
% 0.20/0.57  fof(f530,plain,(
% 0.20/0.57    $false | (spl5_1 | ~spl5_19)),
% 0.20/0.57    inference(subsumption_resolution,[],[f528,f84])).
% 0.20/0.57  fof(f84,plain,(
% 0.20/0.57    sK0 != sK1 | spl5_1),
% 0.20/0.57    inference(avatar_component_clause,[],[f82])).
% 0.20/0.57  fof(f82,plain,(
% 0.20/0.57    spl5_1 <=> sK0 = sK1),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.57  fof(f528,plain,(
% 0.20/0.57    sK0 = sK1 | ~spl5_19),
% 0.20/0.57    inference(resolution,[],[f517,f80])).
% 0.20/0.57  fof(f80,plain,(
% 0.20/0.57    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.20/0.57    inference(equality_resolution,[],[f50])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.57    inference(rectify,[],[f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.57  fof(f517,plain,(
% 0.20/0.57    r2_hidden(sK1,k1_tarski(sK0)) | ~spl5_19),
% 0.20/0.57    inference(avatar_component_clause,[],[f515])).
% 0.20/0.57  fof(f515,plain,(
% 0.20/0.57    spl5_19 <=> r2_hidden(sK1,k1_tarski(sK0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.57  fof(f518,plain,(
% 0.20/0.57    spl5_19 | spl5_17),
% 0.20/0.57    inference(avatar_split_clause,[],[f513,f500,f515])).
% 0.20/0.57  fof(f500,plain,(
% 0.20/0.57    spl5_17 <=> r2_hidden(sK1,k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.57  fof(f513,plain,(
% 0.20/0.57    r2_hidden(sK1,k1_tarski(sK0)) | spl5_17),
% 0.20/0.57    inference(subsumption_resolution,[],[f512,f79])).
% 0.20/0.57  fof(f79,plain,(
% 0.20/0.57    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.20/0.57    inference(equality_resolution,[],[f78])).
% 0.20/0.57  fof(f78,plain,(
% 0.20/0.57    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.20/0.57    inference(equality_resolution,[],[f51])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f512,plain,(
% 0.20/0.57    r2_hidden(sK1,k1_tarski(sK0)) | ~r2_hidden(sK1,k1_tarski(sK1)) | spl5_17),
% 0.20/0.57    inference(resolution,[],[f502,f63])).
% 0.20/0.57  fof(f63,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.20/0.57    inference(nnf_transformation,[],[f23])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.20/0.57  fof(f502,plain,(
% 0.20/0.57    ~r2_hidden(sK1,k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) | spl5_17),
% 0.20/0.57    inference(avatar_component_clause,[],[f500])).
% 0.20/0.57  fof(f503,plain,(
% 0.20/0.57    ~spl5_17 | ~spl5_13 | ~spl5_16),
% 0.20/0.57    inference(avatar_split_clause,[],[f497,f493,f341,f500])).
% 0.20/0.57  fof(f341,plain,(
% 0.20/0.57    spl5_13 <=> ! [X5] : (~r1_xboole_0(X5,k1_tarski(sK0)) | ~r2_hidden(sK1,X5))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.57  fof(f493,plain,(
% 0.20/0.57    spl5_16 <=> k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.57  fof(f497,plain,(
% 0.20/0.57    ~r2_hidden(sK1,k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) | (~spl5_13 | ~spl5_16)),
% 0.20/0.57    inference(superposition,[],[f407,f495])).
% 0.20/0.57  fof(f495,plain,(
% 0.20/0.57    k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | ~spl5_16),
% 0.20/0.57    inference(avatar_component_clause,[],[f493])).
% 0.20/0.57  fof(f407,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(X0,k1_tarski(sK0)))) ) | ~spl5_13),
% 0.20/0.57    inference(resolution,[],[f342,f69])).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.57  fof(f342,plain,(
% 0.20/0.57    ( ! [X5] : (~r1_xboole_0(X5,k1_tarski(sK0)) | ~r2_hidden(sK1,X5)) ) | ~spl5_13),
% 0.20/0.57    inference(avatar_component_clause,[],[f341])).
% 0.20/0.57  fof(f496,plain,(
% 0.20/0.57    spl5_16 | ~spl5_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f480,f87,f493])).
% 0.20/0.57  fof(f87,plain,(
% 0.20/0.57    spl5_2 <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.57  fof(f480,plain,(
% 0.20/0.57    k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | ~spl5_2),
% 0.20/0.57    inference(superposition,[],[f137,f89])).
% 0.20/0.57  fof(f89,plain,(
% 0.20/0.57    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl5_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f87])).
% 0.20/0.57  fof(f137,plain,(
% 0.20/0.57    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))) )),
% 0.20/0.57    inference(superposition,[],[f57,f54])).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.57  fof(f359,plain,(
% 0.20/0.57    spl5_13 | spl5_4 | ~spl5_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f349,f87,f101,f341])).
% 0.20/0.57  fof(f101,plain,(
% 0.20/0.57    spl5_4 <=> ! [X0] : ~r2_hidden(X0,k1_tarski(sK0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.57  fof(f349,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(sK0)) | ~r1_xboole_0(X0,k1_tarski(sK0)) | ~r2_hidden(sK1,X0)) ) | ~spl5_2),
% 0.20/0.57    inference(superposition,[],[f93,f244])).
% 0.20/0.57  fof(f244,plain,(
% 0.20/0.57    ( ! [X0] : (k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),X0) | ~r2_hidden(sK1,X0)) ) | ~spl5_2),
% 0.20/0.57    inference(superposition,[],[f240,f59])).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,axiom,(
% 0.20/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.20/0.57  fof(f240,plain,(
% 0.20/0.57    ( ! [X3] : (k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X3))) ) | ~spl5_2),
% 0.20/0.57    inference(forward_demodulation,[],[f231,f89])).
% 0.20/0.57  fof(f231,plain,(
% 0.20/0.57    ( ! [X3] : (k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X3))) ) | ~spl5_2),
% 0.20/0.57    inference(superposition,[],[f182,f58])).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.20/0.57  fof(f182,plain,(
% 0.20/0.57    ( ! [X0] : (k3_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),X0)) = k3_xboole_0(k1_tarski(sK0),X0)) ) | ~spl5_2),
% 0.20/0.57    inference(superposition,[],[f49,f89])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.20/0.57  fof(f93,plain,(
% 0.20/0.57    ( ! [X2,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X2,X1)) | ~r1_xboole_0(X1,X2)) )),
% 0.20/0.57    inference(superposition,[],[f56,f54])).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f18])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(rectify,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.57  fof(f181,plain,(
% 0.20/0.57    ~spl5_4),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f178])).
% 0.20/0.57  fof(f178,plain,(
% 0.20/0.57    $false | ~spl5_4),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f79,f102])).
% 0.20/0.57  fof(f102,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0))) ) | ~spl5_4),
% 0.20/0.57    inference(avatar_component_clause,[],[f101])).
% 0.20/0.57  fof(f90,plain,(
% 0.20/0.57    spl5_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f39,f87])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.57    inference(cnf_transformation,[],[f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f17])).
% 0.20/0.57  fof(f17,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.57    inference(negated_conjecture,[],[f16])).
% 0.20/0.57  fof(f16,conjecture,(
% 0.20/0.57    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 0.20/0.57  fof(f85,plain,(
% 0.20/0.57    ~spl5_1),
% 0.20/0.57    inference(avatar_split_clause,[],[f40,f82])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    sK0 != sK1),
% 0.20/0.57    inference(cnf_transformation,[],[f25])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (32181)------------------------------
% 0.20/0.57  % (32181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (32181)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (32181)Memory used [KB]: 6524
% 0.20/0.57  % (32181)Time elapsed: 0.174 s
% 0.20/0.57  % (32181)------------------------------
% 0.20/0.57  % (32181)------------------------------
% 0.20/0.57  % (32168)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.57  % (32167)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.57  % (32160)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.58  % (32189)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.58  % (32176)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.58  % (32189)Refutation not found, incomplete strategy% (32189)------------------------------
% 0.20/0.58  % (32189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (32189)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (32189)Memory used [KB]: 1663
% 0.20/0.58  % (32189)Time elapsed: 0.177 s
% 0.20/0.58  % (32189)------------------------------
% 0.20/0.58  % (32189)------------------------------
% 0.20/0.58  % (32175)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.58  % (32175)Refutation not found, incomplete strategy% (32175)------------------------------
% 0.20/0.58  % (32175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (32180)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.58  % (32175)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (32175)Memory used [KB]: 10618
% 0.20/0.58  % (32175)Time elapsed: 0.148 s
% 0.20/0.58  % (32175)------------------------------
% 0.20/0.58  % (32175)------------------------------
% 1.59/0.59  % (32154)Success in time 0.229 s
%------------------------------------------------------------------------------
