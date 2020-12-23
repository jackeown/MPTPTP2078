%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:24 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 112 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  206 ( 375 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1518,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1416,f1435,f1476])).

fof(f1476,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f1471])).

fof(f1471,plain,
    ( $false
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f133,f1415,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f1415,plain,
    ( ! [X1] : ~ r2_hidden(X1,k3_xboole_0(sK1,sK0))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f1414])).

fof(f1414,plain,
    ( spl6_2
  <=> ! [X1] : ~ r2_hidden(X1,k3_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f133,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f62,f73,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f73,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f57,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f57,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK0),sK1) ),
    inference(forward_demodulation,[],[f36,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f36,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f24])).

fof(f24,plain,
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

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f62,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f35,f42])).

fof(f35,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f1435,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f1431])).

fof(f1431,plain,
    ( $false
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f184,f1412,f42])).

fof(f1412,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f1410])).

fof(f1410,plain,
    ( spl6_1
  <=> r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f184,plain,(
    ! [X0] : r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f140,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f140,plain,(
    r1_xboole_0(k1_tarski(sK3),sK1) ),
    inference(unit_resulting_resolution,[],[f124,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f124,plain,(
    ~ r2_hidden(sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f34,f66,f54])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f66,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f61,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f61,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f35,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f34,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f1416,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f176,f1414,f1410])).

fof(f176,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_xboole_0(sK1,sK0))
      | ~ r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3)) ) ),
    inference(superposition,[],[f50,f89])).

fof(f89,plain,(
    k3_xboole_0(sK1,sK0) = k3_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3)) ),
    inference(unit_resulting_resolution,[],[f58,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f58,plain,(
    r1_tarski(k3_xboole_0(sK1,sK0),k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f33,f53])).

fof(f33,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:45:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (29808)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (29812)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (29802)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (29821)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (29825)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (29820)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (29806)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (29807)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (29804)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (29804)Refutation not found, incomplete strategy% (29804)------------------------------
% 0.21/0.52  % (29804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29804)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29804)Memory used [KB]: 10746
% 0.21/0.52  % (29804)Time elapsed: 0.111 s
% 0.21/0.52  % (29804)------------------------------
% 0.21/0.52  % (29804)------------------------------
% 0.21/0.52  % (29816)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (29813)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (29817)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (29811)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (29828)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (29810)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (29803)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (29826)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (29822)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (29819)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (29805)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (29825)Refutation not found, incomplete strategy% (29825)------------------------------
% 0.21/0.54  % (29825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29825)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29825)Memory used [KB]: 10746
% 0.21/0.54  % (29825)Time elapsed: 0.129 s
% 0.21/0.54  % (29825)------------------------------
% 0.21/0.54  % (29825)------------------------------
% 0.21/0.54  % (29832)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (29809)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (29831)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (29814)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.55  % (29830)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.44/0.55  % (29823)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.44/0.55  % (29829)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.44/0.55  % (29824)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.44/0.55  % (29827)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.44/0.56  % (29815)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.44/0.56  % (29812)Refutation found. Thanks to Tanya!
% 1.44/0.56  % SZS status Theorem for theBenchmark
% 1.44/0.56  % (29810)Refutation not found, incomplete strategy% (29810)------------------------------
% 1.44/0.56  % (29810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % SZS output start Proof for theBenchmark
% 1.44/0.56  fof(f1518,plain,(
% 1.44/0.56    $false),
% 1.44/0.56    inference(avatar_sat_refutation,[],[f1416,f1435,f1476])).
% 1.44/0.56  fof(f1476,plain,(
% 1.44/0.56    ~spl6_2),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f1471])).
% 1.44/0.56  fof(f1471,plain,(
% 1.44/0.56    $false | ~spl6_2),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f133,f1415,f49])).
% 1.44/0.56  fof(f49,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f32])).
% 1.44/0.56  fof(f32,plain,(
% 1.44/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f31])).
% 1.44/0.56  fof(f31,plain,(
% 1.44/0.56    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f21,plain,(
% 1.44/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.44/0.56    inference(ennf_transformation,[],[f15])).
% 1.44/0.56  fof(f15,plain,(
% 1.44/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.44/0.56    inference(rectify,[],[f5])).
% 1.44/0.56  fof(f5,axiom,(
% 1.44/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.44/0.56  fof(f1415,plain,(
% 1.44/0.56    ( ! [X1] : (~r2_hidden(X1,k3_xboole_0(sK1,sK0))) ) | ~spl6_2),
% 1.44/0.56    inference(avatar_component_clause,[],[f1414])).
% 1.44/0.56  fof(f1414,plain,(
% 1.44/0.56    spl6_2 <=> ! [X1] : ~r2_hidden(X1,k3_xboole_0(sK1,sK0))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.44/0.56  fof(f133,plain,(
% 1.44/0.56    ~r1_xboole_0(sK1,sK0)),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f62,f73,f37])).
% 1.44/0.56  fof(f37,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f18])).
% 1.44/0.56  fof(f18,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.44/0.56    inference(ennf_transformation,[],[f7])).
% 1.44/0.56  fof(f7,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.44/0.56  fof(f73,plain,(
% 1.44/0.56    ~r1_xboole_0(sK1,k2_xboole_0(sK2,sK0))),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f57,f42])).
% 1.44/0.56  fof(f42,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f20])).
% 1.44/0.56  fof(f20,plain,(
% 1.44/0.56    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.44/0.56    inference(ennf_transformation,[],[f4])).
% 1.44/0.56  fof(f4,axiom,(
% 1.44/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.44/0.56  fof(f57,plain,(
% 1.44/0.56    ~r1_xboole_0(k2_xboole_0(sK2,sK0),sK1)),
% 1.44/0.56    inference(forward_demodulation,[],[f36,f40])).
% 1.44/0.56  fof(f40,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f1])).
% 1.44/0.56  fof(f1,axiom,(
% 1.44/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.44/0.56  fof(f36,plain,(
% 1.44/0.56    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.44/0.56    inference(cnf_transformation,[],[f25])).
% 1.44/0.56  fof(f25,plain,(
% 1.44/0.56    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f24])).
% 1.44/0.56  fof(f24,plain,(
% 1.44/0.56    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f17,plain,(
% 1.44/0.56    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.44/0.56    inference(flattening,[],[f16])).
% 1.44/0.56  fof(f16,plain,(
% 1.44/0.56    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.44/0.56    inference(ennf_transformation,[],[f14])).
% 1.44/0.56  fof(f14,negated_conjecture,(
% 1.44/0.56    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.44/0.56    inference(negated_conjecture,[],[f13])).
% 1.44/0.56  fof(f13,conjecture,(
% 1.44/0.56    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.44/0.56  fof(f62,plain,(
% 1.44/0.56    r1_xboole_0(sK1,sK2)),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f35,f42])).
% 1.44/0.56  fof(f35,plain,(
% 1.44/0.56    r1_xboole_0(sK2,sK1)),
% 1.44/0.56    inference(cnf_transformation,[],[f25])).
% 1.44/0.56  fof(f1435,plain,(
% 1.44/0.56    spl6_1),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f1431])).
% 1.44/0.56  fof(f1431,plain,(
% 1.44/0.56    $false | spl6_1),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f184,f1412,f42])).
% 1.44/0.56  fof(f1412,plain,(
% 1.44/0.56    ~r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3)) | spl6_1),
% 1.44/0.56    inference(avatar_component_clause,[],[f1410])).
% 1.44/0.56  fof(f1410,plain,(
% 1.44/0.56    spl6_1 <=> r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.44/0.56  fof(f184,plain,(
% 1.44/0.56    ( ! [X0] : (r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,X0))) )),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f140,f41])).
% 1.44/0.56  fof(f41,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f19])).
% 1.44/0.56  fof(f19,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.44/0.56    inference(ennf_transformation,[],[f8])).
% 1.44/0.56  fof(f8,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).
% 1.44/0.56  fof(f140,plain,(
% 1.44/0.56    r1_xboole_0(k1_tarski(sK3),sK1)),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f124,f52])).
% 1.44/0.56  fof(f52,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f23])).
% 1.44/0.56  fof(f23,plain,(
% 1.44/0.56    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.44/0.56    inference(ennf_transformation,[],[f12])).
% 1.44/0.56  fof(f12,axiom,(
% 1.44/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.44/0.56  fof(f124,plain,(
% 1.44/0.56    ~r2_hidden(sK3,sK1)),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f34,f66,f54])).
% 1.44/0.56  fof(f54,plain,(
% 1.44/0.56    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.44/0.56    inference(equality_resolution,[],[f45])).
% 1.44/0.56  fof(f45,plain,(
% 1.44/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 1.44/0.56    inference(cnf_transformation,[],[f30])).
% 1.44/0.56  fof(f30,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.44/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 1.44/0.56  fof(f29,plain,(
% 1.44/0.56    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.44/0.56    introduced(choice_axiom,[])).
% 1.44/0.56  fof(f28,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.44/0.56    inference(rectify,[],[f27])).
% 1.44/0.56  fof(f27,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.44/0.56    inference(flattening,[],[f26])).
% 1.44/0.56  fof(f26,plain,(
% 1.44/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.44/0.56    inference(nnf_transformation,[],[f3])).
% 1.44/0.56  fof(f3,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.44/0.56  fof(f66,plain,(
% 1.44/0.56    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,sK2))) )),
% 1.44/0.56    inference(forward_demodulation,[],[f61,f53])).
% 1.44/0.56  fof(f53,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f2])).
% 1.44/0.56  fof(f2,axiom,(
% 1.44/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.44/0.56  fof(f61,plain,(
% 1.44/0.56    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK2,sK1))) )),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f35,f50])).
% 1.44/0.56  fof(f50,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f32])).
% 1.44/0.56  fof(f34,plain,(
% 1.44/0.56    r2_hidden(sK3,sK2)),
% 1.44/0.56    inference(cnf_transformation,[],[f25])).
% 1.44/0.56  fof(f1416,plain,(
% 1.44/0.56    ~spl6_1 | spl6_2),
% 1.44/0.56    inference(avatar_split_clause,[],[f176,f1414,f1410])).
% 1.44/0.56  fof(f176,plain,(
% 1.44/0.56    ( ! [X1] : (~r2_hidden(X1,k3_xboole_0(sK1,sK0)) | ~r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3))) )),
% 1.44/0.56    inference(superposition,[],[f50,f89])).
% 1.44/0.56  fof(f89,plain,(
% 1.44/0.56    k3_xboole_0(sK1,sK0) = k3_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3))),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f58,f51])).
% 1.44/0.56  fof(f51,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.44/0.56    inference(cnf_transformation,[],[f22])).
% 1.44/0.56  fof(f22,plain,(
% 1.44/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.44/0.56    inference(ennf_transformation,[],[f6])).
% 1.44/0.56  fof(f6,axiom,(
% 1.44/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.44/0.56  fof(f58,plain,(
% 1.44/0.56    r1_tarski(k3_xboole_0(sK1,sK0),k1_tarski(sK3))),
% 1.44/0.56    inference(forward_demodulation,[],[f33,f53])).
% 1.44/0.56  fof(f33,plain,(
% 1.44/0.56    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.44/0.56    inference(cnf_transformation,[],[f25])).
% 1.44/0.56  % SZS output end Proof for theBenchmark
% 1.44/0.56  % (29812)------------------------------
% 1.44/0.56  % (29812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (29812)Termination reason: Refutation
% 1.44/0.56  
% 1.44/0.56  % (29812)Memory used [KB]: 11513
% 1.44/0.56  % (29812)Time elapsed: 0.157 s
% 1.44/0.56  % (29812)------------------------------
% 1.44/0.56  % (29812)------------------------------
% 1.56/0.57  % (29798)Success in time 0.206 s
%------------------------------------------------------------------------------
