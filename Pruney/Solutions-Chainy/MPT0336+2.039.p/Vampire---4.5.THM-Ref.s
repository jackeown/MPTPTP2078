%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 133 expanded)
%              Number of leaves         :   16 (  37 expanded)
%              Depth                    :   16
%              Number of atoms          :  211 ( 396 expanded)
%              Number of equality atoms :   66 (  88 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f691,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f146,f298,f690])).

fof(f690,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f689])).

fof(f689,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f687,f53])).

fof(f53,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f687,plain,
    ( ~ r1_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(resolution,[],[f662,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f662,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK0)
    | ~ spl6_2 ),
    inference(trivial_inequality_removal,[],[f661])).

fof(f661,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,sK0)
    | ~ spl6_2 ),
    inference(superposition,[],[f652,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f652,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl6_2 ),
    inference(superposition,[],[f118,f432])).

fof(f432,plain,
    ( k3_xboole_0(k1_tarski(sK3),sK2) = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f422,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f422,plain,
    ( k3_xboole_0(k1_tarski(sK3),sK2) = k3_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(superposition,[],[f310,f65])).

fof(f65,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f63,f51])).

fof(f63,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f35,f38])).

fof(f35,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f310,plain,
    ( ! [X0] : k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(k1_tarski(sK3),X0)
    | ~ spl6_2 ),
    inference(superposition,[],[f49,f92])).

fof(f92,plain,
    ( k3_xboole_0(sK0,sK1) = k1_tarski(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_2
  <=> k3_xboole_0(sK0,sK1) = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f118,plain,(
    k1_xboole_0 != k3_xboole_0(k1_tarski(sK3),sK2) ),
    inference(resolution,[],[f106,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f106,plain,(
    ~ r1_xboole_0(k1_tarski(sK3),sK2) ),
    inference(resolution,[],[f60,f55])).

fof(f55,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f60,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3,X1)
      | ~ r1_xboole_0(X1,sK2) ) ),
    inference(resolution,[],[f34,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f34,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f298,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f296,f267])).

fof(f267,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f133,f38])).

fof(f133,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl6_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f296,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f293,f65])).

fof(f293,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f95,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f95,plain,(
    k1_xboole_0 != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f72,f52])).

fof(f72,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f36,f38])).

fof(f36,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f146,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f142,f132,f86])).

fof(f86,plain,
    ( spl6_1
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f142,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl6_3 ),
    inference(resolution,[],[f134,f52])).

fof(f134,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f93,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f80,f90,f86])).

fof(f80,plain,
    ( k3_xboole_0(sK0,sK1) = k1_tarski(sK3)
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f33,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f33,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:40:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.46  % (21230)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.49  % (21238)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.49  % (21219)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.49  % (21237)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.50  % (21222)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.51  % (21218)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.51  % (21220)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.51  % (21235)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.51  % (21240)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.51  % (21221)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.51  % (21223)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.51  % (21232)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.52  % (21230)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f691,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(avatar_sat_refutation,[],[f93,f146,f298,f690])).
% 0.19/0.52  fof(f690,plain,(
% 0.19/0.52    ~spl6_2),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f689])).
% 0.19/0.52  fof(f689,plain,(
% 0.19/0.52    $false | ~spl6_2),
% 0.19/0.52    inference(subsumption_resolution,[],[f687,f53])).
% 0.19/0.52  fof(f53,plain,(
% 0.19/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f6])).
% 0.19/0.52  fof(f6,axiom,(
% 0.19/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.19/0.52  fof(f687,plain,(
% 0.19/0.52    ~r1_xboole_0(sK0,k1_xboole_0) | ~spl6_2),
% 0.19/0.52    inference(resolution,[],[f662,f38])).
% 0.19/0.52  fof(f38,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f20])).
% 0.19/0.52  fof(f20,plain,(
% 0.19/0.52    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f3])).
% 0.19/0.52  fof(f3,axiom,(
% 0.19/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.19/0.52  fof(f662,plain,(
% 0.19/0.52    ~r1_xboole_0(k1_xboole_0,sK0) | ~spl6_2),
% 0.19/0.52    inference(trivial_inequality_removal,[],[f661])).
% 0.19/0.52  fof(f661,plain,(
% 0.19/0.52    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_xboole_0,sK0) | ~spl6_2),
% 0.19/0.52    inference(superposition,[],[f652,f51])).
% 0.19/0.52  fof(f51,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f32])).
% 0.19/0.52  fof(f32,plain,(
% 0.19/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.19/0.52    inference(nnf_transformation,[],[f2])).
% 0.19/0.52  fof(f2,axiom,(
% 0.19/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.19/0.52  fof(f652,plain,(
% 0.19/0.52    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK0) | ~spl6_2),
% 0.19/0.52    inference(superposition,[],[f118,f432])).
% 0.19/0.52  fof(f432,plain,(
% 0.19/0.52    k3_xboole_0(k1_tarski(sK3),sK2) = k3_xboole_0(k1_xboole_0,sK0) | ~spl6_2),
% 0.19/0.52    inference(forward_demodulation,[],[f422,f50])).
% 0.19/0.52  fof(f50,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f1])).
% 0.19/0.52  fof(f1,axiom,(
% 0.19/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.52  fof(f422,plain,(
% 0.19/0.52    k3_xboole_0(k1_tarski(sK3),sK2) = k3_xboole_0(sK0,k1_xboole_0) | ~spl6_2),
% 0.19/0.52    inference(superposition,[],[f310,f65])).
% 0.19/0.52  fof(f65,plain,(
% 0.19/0.52    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.19/0.52    inference(resolution,[],[f63,f51])).
% 0.19/0.52  fof(f63,plain,(
% 0.19/0.52    r1_xboole_0(sK1,sK2)),
% 0.19/0.52    inference(resolution,[],[f35,f38])).
% 0.19/0.52  fof(f35,plain,(
% 0.19/0.52    r1_xboole_0(sK2,sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f23])).
% 0.19/0.52  fof(f23,plain,(
% 0.19/0.52    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f22])).
% 0.19/0.52  fof(f22,plain,(
% 0.19/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f18,plain,(
% 0.19/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.19/0.52    inference(flattening,[],[f17])).
% 0.19/0.52  fof(f17,plain,(
% 0.19/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.19/0.52    inference(ennf_transformation,[],[f15])).
% 0.19/0.52  fof(f15,negated_conjecture,(
% 0.19/0.52    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.19/0.52    inference(negated_conjecture,[],[f14])).
% 0.19/0.52  fof(f14,conjecture,(
% 0.19/0.52    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.19/0.52  fof(f310,plain,(
% 0.19/0.52    ( ! [X0] : (k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(k1_tarski(sK3),X0)) ) | ~spl6_2),
% 0.19/0.52    inference(superposition,[],[f49,f92])).
% 0.19/0.52  fof(f92,plain,(
% 0.19/0.52    k3_xboole_0(sK0,sK1) = k1_tarski(sK3) | ~spl6_2),
% 0.19/0.52    inference(avatar_component_clause,[],[f90])).
% 0.19/0.52  fof(f90,plain,(
% 0.19/0.52    spl6_2 <=> k3_xboole_0(sK0,sK1) = k1_tarski(sK3)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.19/0.52  fof(f49,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f5])).
% 0.19/0.52  fof(f5,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.19/0.52  fof(f118,plain,(
% 0.19/0.52    k1_xboole_0 != k3_xboole_0(k1_tarski(sK3),sK2)),
% 0.19/0.52    inference(resolution,[],[f106,f52])).
% 0.19/0.52  fof(f52,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f32])).
% 0.19/0.52  fof(f106,plain,(
% 0.19/0.52    ~r1_xboole_0(k1_tarski(sK3),sK2)),
% 0.19/0.52    inference(resolution,[],[f60,f55])).
% 0.19/0.52  fof(f55,plain,(
% 0.19/0.52    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.19/0.52    inference(equality_resolution,[],[f54])).
% 0.19/0.52  fof(f54,plain,(
% 0.19/0.52    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.19/0.52    inference(equality_resolution,[],[f40])).
% 0.19/0.52  fof(f40,plain,(
% 0.19/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.19/0.52    inference(cnf_transformation,[],[f27])).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).
% 0.19/0.52  fof(f26,plain,(
% 0.19/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f25,plain,(
% 0.19/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.19/0.52    inference(rectify,[],[f24])).
% 0.19/0.52  fof(f24,plain,(
% 0.19/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.19/0.52    inference(nnf_transformation,[],[f8])).
% 0.19/0.52  fof(f8,axiom,(
% 0.19/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.19/0.52  fof(f60,plain,(
% 0.19/0.52    ( ! [X1] : (~r2_hidden(sK3,X1) | ~r1_xboole_0(X1,sK2)) )),
% 0.19/0.52    inference(resolution,[],[f34,f45])).
% 0.19/0.52  fof(f45,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f29])).
% 0.19/0.52  fof(f29,plain,(
% 0.19/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f28])).
% 0.19/0.52  fof(f28,plain,(
% 0.19/0.52    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f21,plain,(
% 0.19/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.19/0.52    inference(ennf_transformation,[],[f16])).
% 0.19/0.52  fof(f16,plain,(
% 0.19/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.52    inference(rectify,[],[f4])).
% 0.19/0.52  fof(f4,axiom,(
% 0.19/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.19/0.52  fof(f34,plain,(
% 0.19/0.52    r2_hidden(sK3,sK2)),
% 0.19/0.52    inference(cnf_transformation,[],[f23])).
% 0.19/0.52  fof(f298,plain,(
% 0.19/0.52    ~spl6_3),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f297])).
% 0.19/0.52  fof(f297,plain,(
% 0.19/0.52    $false | ~spl6_3),
% 0.19/0.52    inference(subsumption_resolution,[],[f296,f267])).
% 0.19/0.52  fof(f267,plain,(
% 0.19/0.52    r1_xboole_0(sK1,sK0) | ~spl6_3),
% 0.19/0.52    inference(resolution,[],[f133,f38])).
% 0.19/0.52  fof(f133,plain,(
% 0.19/0.52    r1_xboole_0(sK0,sK1) | ~spl6_3),
% 0.19/0.52    inference(avatar_component_clause,[],[f132])).
% 0.19/0.52  fof(f132,plain,(
% 0.19/0.52    spl6_3 <=> r1_xboole_0(sK0,sK1)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.19/0.52  fof(f296,plain,(
% 0.19/0.52    ~r1_xboole_0(sK1,sK0)),
% 0.19/0.52    inference(subsumption_resolution,[],[f293,f65])).
% 0.19/0.52  fof(f293,plain,(
% 0.19/0.52    k1_xboole_0 != k3_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0)),
% 0.19/0.52    inference(superposition,[],[f95,f37])).
% 0.19/0.52  fof(f37,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f19])).
% 0.19/0.52  fof(f19,plain,(
% 0.19/0.52    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f7])).
% 0.19/0.52  fof(f7,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.19/0.52  fof(f95,plain,(
% 0.19/0.52    k1_xboole_0 != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.19/0.52    inference(resolution,[],[f72,f52])).
% 0.19/0.52  fof(f72,plain,(
% 0.19/0.52    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.19/0.52    inference(resolution,[],[f36,f38])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f23])).
% 0.19/0.52  fof(f146,plain,(
% 0.19/0.52    ~spl6_1 | spl6_3),
% 0.19/0.52    inference(avatar_split_clause,[],[f142,f132,f86])).
% 0.19/0.52  fof(f86,plain,(
% 0.19/0.52    spl6_1 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.19/0.52  fof(f142,plain,(
% 0.19/0.52    k1_xboole_0 != k3_xboole_0(sK0,sK1) | spl6_3),
% 0.19/0.52    inference(resolution,[],[f134,f52])).
% 0.19/0.52  fof(f134,plain,(
% 0.19/0.52    ~r1_xboole_0(sK0,sK1) | spl6_3),
% 0.19/0.52    inference(avatar_component_clause,[],[f132])).
% 0.19/0.52  fof(f93,plain,(
% 0.19/0.52    spl6_1 | spl6_2),
% 0.19/0.52    inference(avatar_split_clause,[],[f80,f90,f86])).
% 0.19/0.52  fof(f80,plain,(
% 0.19/0.52    k3_xboole_0(sK0,sK1) = k1_tarski(sK3) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.19/0.52    inference(resolution,[],[f33,f46])).
% 0.19/0.52  fof(f46,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f31])).
% 0.19/0.52  fof(f31,plain,(
% 0.19/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.19/0.52    inference(flattening,[],[f30])).
% 0.19/0.52  fof(f30,plain,(
% 0.19/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.19/0.52    inference(nnf_transformation,[],[f12])).
% 0.19/0.52  fof(f12,axiom,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.19/0.52  fof(f33,plain,(
% 0.19/0.52    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.19/0.52    inference(cnf_transformation,[],[f23])).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (21230)------------------------------
% 0.19/0.52  % (21230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (21230)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (21230)Memory used [KB]: 11001
% 0.19/0.52  % (21230)Time elapsed: 0.117 s
% 0.19/0.52  % (21230)------------------------------
% 0.19/0.52  % (21230)------------------------------
% 0.19/0.52  % (21229)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.52  % (21217)Success in time 0.173 s
%------------------------------------------------------------------------------
