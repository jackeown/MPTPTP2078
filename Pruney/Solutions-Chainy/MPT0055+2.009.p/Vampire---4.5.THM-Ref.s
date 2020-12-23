%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:05 EST 2020

% Result     : Theorem 2.93s
% Output     : Refutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 118 expanded)
%              Number of leaves         :   13 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  207 ( 545 expanded)
%              Number of equality atoms :   29 (  81 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3028,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f526,f546,f561,f698,f3027])).

fof(f3027,plain,
    ( ~ spl6_5
    | spl6_6 ),
    inference(avatar_contradiction_clause,[],[f3026])).

fof(f3026,plain,
    ( $false
    | ~ spl6_5
    | spl6_6 ),
    inference(subsumption_resolution,[],[f3022,f127])).

fof(f127,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_6
  <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f3022,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl6_5 ),
    inference(superposition,[],[f765,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f765,plain,
    ( ! [X1] : r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(X1,k3_xboole_0(sK0,sK1)))
    | ~ spl6_5 ),
    inference(superposition,[],[f550,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f550,plain,
    ( ! [X0] : r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k3_xboole_0(sK0,sK1),X0))
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f49,f124,f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f124,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl6_5
  <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f698,plain,
    ( ~ spl6_28
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f688,f122,f523])).

fof(f523,plain,
    ( spl6_28
  <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f688,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl6_5 ),
    inference(superposition,[],[f549,f55])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f549,plain,
    ( ! [X0] : ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f124,f79])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f561,plain,
    ( spl6_28
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f547,f126,f122,f523])).

fof(f547,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f45,f128,f124,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f128,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f45,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f29])).

fof(f29,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f546,plain,
    ( spl6_5
    | ~ spl6_6
    | spl6_28 ),
    inference(avatar_contradiction_clause,[],[f545])).

fof(f545,plain,
    ( $false
    | spl6_5
    | ~ spl6_6
    | spl6_28 ),
    inference(subsumption_resolution,[],[f544,f525])).

fof(f525,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f523])).

fof(f544,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl6_5
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f538,f55])).

fof(f538,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | spl6_5
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f128,f123,f78])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f123,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f526,plain,
    ( spl6_5
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f130,f523,f122])).

fof(f130,plain,
    ( ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X1] :
      ( k3_xboole_0(sK0,sK1) != X1
      | ~ r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1))
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f45,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f129,plain,
    ( spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f120,f126,f122])).

fof(f120,plain,
    ( r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f45,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:00:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (16015)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.50  % (15998)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (16013)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (16005)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (16013)Refutation not found, incomplete strategy% (16013)------------------------------
% 0.21/0.51  % (16013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15996)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (16013)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16013)Memory used [KB]: 10746
% 0.21/0.51  % (16013)Time elapsed: 0.053 s
% 0.21/0.51  % (16013)------------------------------
% 0.21/0.51  % (16013)------------------------------
% 1.23/0.53  % (15994)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.23/0.54  % (15993)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.54  % (15997)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.23/0.54  % (15991)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.23/0.54  % (15991)Refutation not found, incomplete strategy% (15991)------------------------------
% 1.23/0.54  % (15991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (15991)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (15995)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.23/0.54  % (15991)Memory used [KB]: 1663
% 1.23/0.54  % (15991)Time elapsed: 0.123 s
% 1.23/0.54  % (15991)------------------------------
% 1.23/0.54  % (15991)------------------------------
% 1.35/0.54  % (15995)Refutation not found, incomplete strategy% (15995)------------------------------
% 1.35/0.54  % (15995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (15995)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (15995)Memory used [KB]: 6140
% 1.35/0.54  % (15995)Time elapsed: 0.124 s
% 1.35/0.54  % (15995)------------------------------
% 1.35/0.54  % (15995)------------------------------
% 1.35/0.54  % (15992)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.54  % (16016)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.54  % (16020)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.54  % (16012)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.54  % (16008)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.54  % (16000)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.54  % (16019)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.54  % (16000)Refutation not found, incomplete strategy% (16000)------------------------------
% 1.35/0.54  % (16000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (16000)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (16000)Memory used [KB]: 10618
% 1.35/0.54  % (16000)Time elapsed: 0.124 s
% 1.35/0.54  % (16000)------------------------------
% 1.35/0.54  % (16000)------------------------------
% 1.35/0.54  % (16012)Refutation not found, incomplete strategy% (16012)------------------------------
% 1.35/0.54  % (16012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (16012)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (16012)Memory used [KB]: 1663
% 1.35/0.54  % (16012)Time elapsed: 0.130 s
% 1.35/0.54  % (16012)------------------------------
% 1.35/0.54  % (16012)------------------------------
% 1.35/0.54  % (15999)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.55  % (15999)Refutation not found, incomplete strategy% (15999)------------------------------
% 1.35/0.55  % (15999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (16008)Refutation not found, incomplete strategy% (16008)------------------------------
% 1.35/0.55  % (16008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (16014)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.55  % (16017)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.55  % (16016)Refutation not found, incomplete strategy% (16016)------------------------------
% 1.35/0.55  % (16016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (16008)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (16008)Memory used [KB]: 10618
% 1.35/0.55  % (16008)Time elapsed: 0.140 s
% 1.35/0.55  % (16008)------------------------------
% 1.35/0.55  % (16008)------------------------------
% 1.35/0.55  % (16016)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (16016)Memory used [KB]: 6268
% 1.35/0.55  % (16016)Time elapsed: 0.139 s
% 1.35/0.55  % (16016)------------------------------
% 1.35/0.55  % (16016)------------------------------
% 1.35/0.55  % (16011)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.55  % (16006)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.55  % (16003)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.55  % (15999)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (15999)Memory used [KB]: 10618
% 1.35/0.55  % (15999)Time elapsed: 0.131 s
% 1.35/0.55  % (15999)------------------------------
% 1.35/0.55  % (15999)------------------------------
% 1.35/0.55  % (16009)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.55  % (16001)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.55  % (16011)Refutation not found, incomplete strategy% (16011)------------------------------
% 1.35/0.55  % (16011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (16006)Refutation not found, incomplete strategy% (16006)------------------------------
% 1.35/0.55  % (16006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (16006)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (16006)Memory used [KB]: 6140
% 1.35/0.55  % (16006)Time elapsed: 0.002 s
% 1.35/0.55  % (16006)------------------------------
% 1.35/0.55  % (16006)------------------------------
% 1.35/0.55  % (16001)Refutation not found, incomplete strategy% (16001)------------------------------
% 1.35/0.55  % (16001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (16004)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.55  % (16010)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.56  % (15993)Refutation not found, incomplete strategy% (15993)------------------------------
% 1.35/0.56  % (15993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (15993)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (15993)Memory used [KB]: 10618
% 1.35/0.56  % (15993)Time elapsed: 0.138 s
% 1.35/0.56  % (15993)------------------------------
% 1.35/0.56  % (15993)------------------------------
% 1.35/0.56  % (16011)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (16011)Memory used [KB]: 10746
% 1.35/0.56  % (16011)Time elapsed: 0.140 s
% 1.35/0.56  % (16011)------------------------------
% 1.35/0.56  % (16011)------------------------------
% 1.35/0.56  % (16001)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (16001)Memory used [KB]: 10618
% 1.35/0.56  % (16001)Time elapsed: 0.140 s
% 1.35/0.56  % (16001)------------------------------
% 1.35/0.56  % (16001)------------------------------
% 1.35/0.56  % (16018)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.56  % (16007)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.56  % (16002)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.93/0.63  % (16039)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.93/0.66  % (16040)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.93/0.66  % (16041)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.93/0.66  % (16042)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 1.93/0.67  % (16044)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 1.93/0.68  % (16045)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.17/0.68  % (16043)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.17/0.69  % (16046)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.17/0.69  % (16047)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.17/0.69  % (16048)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.17/0.69  % (16049)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.17/0.70  % (16050)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.17/0.71  % (16047)Refutation not found, incomplete strategy% (16047)------------------------------
% 2.17/0.71  % (16047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.71  % (16047)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.71  
% 2.17/0.71  % (16047)Memory used [KB]: 1791
% 2.17/0.71  % (16047)Time elapsed: 0.122 s
% 2.17/0.71  % (16047)------------------------------
% 2.17/0.71  % (16047)------------------------------
% 2.80/0.82  % (16062)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.93/0.85  % (16017)Refutation found. Thanks to Tanya!
% 2.93/0.85  % SZS status Theorem for theBenchmark
% 2.93/0.85  % SZS output start Proof for theBenchmark
% 2.93/0.85  fof(f3028,plain,(
% 2.93/0.85    $false),
% 2.93/0.85    inference(avatar_sat_refutation,[],[f129,f526,f546,f561,f698,f3027])).
% 2.93/0.85  fof(f3027,plain,(
% 2.93/0.85    ~spl6_5 | spl6_6),
% 2.93/0.85    inference(avatar_contradiction_clause,[],[f3026])).
% 2.93/0.85  fof(f3026,plain,(
% 2.93/0.85    $false | (~spl6_5 | spl6_6)),
% 2.93/0.85    inference(subsumption_resolution,[],[f3022,f127])).
% 2.93/0.85  fof(f127,plain,(
% 2.93/0.85    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | spl6_6),
% 2.93/0.85    inference(avatar_component_clause,[],[f126])).
% 2.93/0.85  fof(f126,plain,(
% 2.93/0.85    spl6_6 <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 2.93/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.93/0.85  fof(f3022,plain,(
% 2.93/0.85    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl6_5),
% 2.93/0.85    inference(superposition,[],[f765,f52])).
% 2.93/0.85  fof(f52,plain,(
% 2.93/0.85    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.93/0.85    inference(cnf_transformation,[],[f14])).
% 2.93/0.85  fof(f14,axiom,(
% 2.93/0.85    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.93/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 2.93/0.85  fof(f765,plain,(
% 2.93/0.85    ( ! [X1] : (r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(X1,k3_xboole_0(sK0,sK1)))) ) | ~spl6_5),
% 2.93/0.85    inference(superposition,[],[f550,f50])).
% 2.93/0.85  fof(f50,plain,(
% 2.93/0.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.93/0.85    inference(cnf_transformation,[],[f1])).
% 2.93/0.85  fof(f1,axiom,(
% 2.93/0.85    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.93/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.93/0.85  fof(f550,plain,(
% 2.93/0.85    ( ! [X0] : (r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k3_xboole_0(sK0,sK1),X0))) ) | ~spl6_5),
% 2.93/0.85    inference(unit_resulting_resolution,[],[f49,f124,f62])).
% 2.93/0.85  fof(f62,plain,(
% 2.93/0.85    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.93/0.85    inference(cnf_transformation,[],[f38])).
% 2.93/0.85  fof(f38,plain,(
% 2.93/0.85    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.93/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 2.93/0.85  fof(f37,plain,(
% 2.93/0.85    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.93/0.85    introduced(choice_axiom,[])).
% 2.93/0.85  fof(f36,plain,(
% 2.93/0.85    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.93/0.85    inference(rectify,[],[f35])).
% 2.93/0.85  fof(f35,plain,(
% 2.93/0.85    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.93/0.85    inference(nnf_transformation,[],[f28])).
% 2.93/0.85  fof(f28,plain,(
% 2.93/0.85    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.93/0.85    inference(ennf_transformation,[],[f4])).
% 2.93/0.85  fof(f4,axiom,(
% 2.93/0.85    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.93/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.93/0.85  fof(f124,plain,(
% 2.93/0.85    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~spl6_5),
% 2.93/0.85    inference(avatar_component_clause,[],[f122])).
% 2.93/0.85  fof(f122,plain,(
% 2.93/0.85    spl6_5 <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.93/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.93/0.85  fof(f49,plain,(
% 2.93/0.85    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.93/0.85    inference(cnf_transformation,[],[f18])).
% 2.93/0.85  fof(f18,axiom,(
% 2.93/0.85    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.93/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.93/0.85  fof(f698,plain,(
% 2.93/0.85    ~spl6_28 | ~spl6_5),
% 2.93/0.85    inference(avatar_split_clause,[],[f688,f122,f523])).
% 2.93/0.85  fof(f523,plain,(
% 2.93/0.85    spl6_28 <=> r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 2.93/0.85    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 2.93/0.85  fof(f688,plain,(
% 2.93/0.85    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl6_5),
% 2.93/0.85    inference(superposition,[],[f549,f55])).
% 2.93/0.85  fof(f55,plain,(
% 2.93/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.93/0.85    inference(cnf_transformation,[],[f17])).
% 2.93/0.85  fof(f17,axiom,(
% 2.93/0.85    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.93/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.93/0.85  fof(f549,plain,(
% 2.93/0.85    ( ! [X0] : (~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))) ) | ~spl6_5),
% 2.93/0.85    inference(unit_resulting_resolution,[],[f124,f79])).
% 2.93/0.85  fof(f79,plain,(
% 2.93/0.85    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.93/0.85    inference(equality_resolution,[],[f70])).
% 2.93/0.85  fof(f70,plain,(
% 2.93/0.85    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.93/0.85    inference(cnf_transformation,[],[f44])).
% 2.93/0.85  fof(f44,plain,(
% 2.93/0.85    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.93/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).
% 2.93/0.85  fof(f43,plain,(
% 2.93/0.85    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 2.93/0.85    introduced(choice_axiom,[])).
% 2.93/0.85  fof(f42,plain,(
% 2.93/0.85    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.93/0.85    inference(rectify,[],[f41])).
% 2.93/0.85  fof(f41,plain,(
% 2.93/0.85    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.93/0.85    inference(flattening,[],[f40])).
% 2.93/0.85  fof(f40,plain,(
% 2.93/0.85    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.93/0.85    inference(nnf_transformation,[],[f5])).
% 2.93/0.85  fof(f5,axiom,(
% 2.93/0.85    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.93/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.93/0.85  fof(f561,plain,(
% 2.93/0.85    spl6_28 | ~spl6_5 | ~spl6_6),
% 2.93/0.85    inference(avatar_split_clause,[],[f547,f126,f122,f523])).
% 2.93/0.85  fof(f547,plain,(
% 2.93/0.85    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | (~spl6_5 | ~spl6_6)),
% 2.93/0.85    inference(unit_resulting_resolution,[],[f45,f128,f124,f74])).
% 2.93/0.85  fof(f74,plain,(
% 2.93/0.85    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.93/0.85    inference(cnf_transformation,[],[f44])).
% 2.93/0.85  fof(f128,plain,(
% 2.93/0.85    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~spl6_6),
% 2.93/0.85    inference(avatar_component_clause,[],[f126])).
% 2.93/0.85  fof(f45,plain,(
% 2.93/0.85    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.93/0.85    inference(cnf_transformation,[],[f30])).
% 2.93/0.85  fof(f30,plain,(
% 2.93/0.85    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.93/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f29])).
% 2.93/0.85  fof(f29,plain,(
% 2.93/0.85    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.93/0.85    introduced(choice_axiom,[])).
% 2.93/0.85  fof(f24,plain,(
% 2.93/0.85    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.93/0.85    inference(ennf_transformation,[],[f20])).
% 2.93/0.85  fof(f20,negated_conjecture,(
% 2.93/0.85    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.93/0.85    inference(negated_conjecture,[],[f19])).
% 2.93/0.85  fof(f19,conjecture,(
% 2.93/0.85    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.93/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.93/0.85  fof(f546,plain,(
% 2.93/0.85    spl6_5 | ~spl6_6 | spl6_28),
% 2.93/0.85    inference(avatar_contradiction_clause,[],[f545])).
% 2.93/0.85  fof(f545,plain,(
% 2.93/0.85    $false | (spl6_5 | ~spl6_6 | spl6_28)),
% 2.93/0.85    inference(subsumption_resolution,[],[f544,f525])).
% 2.93/0.85  fof(f525,plain,(
% 2.93/0.85    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl6_28),
% 2.93/0.85    inference(avatar_component_clause,[],[f523])).
% 2.93/0.85  fof(f544,plain,(
% 2.93/0.85    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | (spl6_5 | ~spl6_6)),
% 2.93/0.85    inference(forward_demodulation,[],[f538,f55])).
% 2.93/0.85  fof(f538,plain,(
% 2.93/0.85    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | (spl6_5 | ~spl6_6)),
% 2.93/0.85    inference(unit_resulting_resolution,[],[f128,f123,f78])).
% 2.93/0.85  fof(f78,plain,(
% 2.93/0.85    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.93/0.85    inference(equality_resolution,[],[f71])).
% 2.93/0.85  fof(f71,plain,(
% 2.93/0.85    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.93/0.85    inference(cnf_transformation,[],[f44])).
% 2.93/0.85  fof(f123,plain,(
% 2.93/0.85    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | spl6_5),
% 2.93/0.85    inference(avatar_component_clause,[],[f122])).
% 2.93/0.85  fof(f526,plain,(
% 2.93/0.85    spl6_5 | ~spl6_28),
% 2.93/0.85    inference(avatar_split_clause,[],[f130,f523,f122])).
% 2.93/0.85  fof(f130,plain,(
% 2.93/0.85    ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.93/0.85    inference(equality_resolution,[],[f86])).
% 2.93/0.85  fof(f86,plain,(
% 2.93/0.85    ( ! [X1] : (k3_xboole_0(sK0,sK1) != X1 | ~r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1)) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X1),X1)) )),
% 2.93/0.85    inference(superposition,[],[f45,f73])).
% 2.93/0.85  fof(f73,plain,(
% 2.93/0.85    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.93/0.85    inference(cnf_transformation,[],[f44])).
% 2.93/0.85  fof(f129,plain,(
% 2.93/0.85    spl6_5 | spl6_6),
% 2.93/0.85    inference(avatar_split_clause,[],[f120,f126,f122])).
% 2.93/0.85  fof(f120,plain,(
% 2.93/0.85    r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 2.93/0.85    inference(equality_resolution,[],[f85])).
% 2.93/0.85  fof(f85,plain,(
% 2.93/0.85    ( ! [X0] : (k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK5(sK0,k4_xboole_0(sK0,sK1),X0),X0)) )),
% 2.93/0.85    inference(superposition,[],[f45,f72])).
% 2.93/0.85  fof(f72,plain,(
% 2.93/0.85    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 2.93/0.85    inference(cnf_transformation,[],[f44])).
% 2.93/0.85  % SZS output end Proof for theBenchmark
% 2.93/0.85  % (16017)------------------------------
% 2.93/0.85  % (16017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.93/0.85  % (16017)Termination reason: Refutation
% 2.93/0.85  
% 2.93/0.85  % (16017)Memory used [KB]: 12665
% 2.93/0.85  % (16017)Time elapsed: 0.427 s
% 2.93/0.85  % (16017)------------------------------
% 2.93/0.85  % (16017)------------------------------
% 2.93/0.86  % (15985)Success in time 0.485 s
%------------------------------------------------------------------------------
