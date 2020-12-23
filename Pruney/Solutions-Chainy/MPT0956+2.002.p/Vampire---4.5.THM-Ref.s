%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 (  80 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  246 ( 303 expanded)
%              Number of equality atoms :   26 (  26 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f65,f88,f90,f93,f97])).

fof(f97,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl5_7 ),
    inference(resolution,[],[f87,f29])).

fof(f29,plain,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord2)).

fof(f87,plain,
    ( ~ v1_relat_2(k1_wellord2(sK0))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_7
  <=> v1_relat_2(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f93,plain,
    ( ~ spl5_5
    | spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f91,f71,f52,f78])).

fof(f78,plain,
    ( spl5_5
  <=> v1_relat_1(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f52,plain,
    ( spl5_1
  <=> r1_relat_2(k1_wellord2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f71,plain,
    ( spl5_3
  <=> r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f91,plain,
    ( r1_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl5_3 ),
    inference(resolution,[],[f72,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK2(X0,X1)),X0)
              & r2_hidden(sK2(X0,X1),X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK2(X0,X1)),X0)
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2] :
                ( r2_hidden(k4_tarski(X2,X2),X0)
                | ~ r2_hidden(X2,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

fof(f72,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f90,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | spl5_5 ),
    inference(resolution,[],[f79,f30])).

fof(f30,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f79,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f88,plain,
    ( ~ spl5_5
    | ~ spl5_7
    | ~ spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f84,f63,f71,f86,f78])).

fof(f63,plain,
    ( spl5_2
  <=> r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK2(k1_wellord2(sK0),sK0)),k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f84,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0)
    | ~ v1_relat_2(k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl5_2 ),
    inference(forward_demodulation,[],[f68,f57])).

fof(f57,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f30,f50])).

fof(f50,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & r2_hidden(sK4(X0,X1),X0)
            & r2_hidden(sK3(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f68,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),k3_relat_1(k1_wellord2(sK0)))
    | ~ v1_relat_2(k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl5_2 ),
    inference(resolution,[],[f64,f31])).

fof(f31,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,X2),X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK1(X0),sK1(X0)),X0)
            & r2_hidden(sK1(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0),sK1(X0)),X0)
        & r2_hidden(sK1(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1] :
              ( r2_hidden(k4_tarski(X1,X1),X0)
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

fof(f64,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK2(k1_wellord2(sK0),sK0)),k1_wellord2(sK0))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f65,plain,
    ( ~ spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f61,f52,f63])).

% (29338)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f61,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK2(k1_wellord2(sK0),sK0)),k1_wellord2(sK0))
    | spl5_1 ),
    inference(resolution,[],[f58,f53])).

fof(f53,plain,
    ( ~ r1_relat_2(k1_wellord2(sK0),sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_relat_2(k1_wellord2(X0),X1)
      | ~ r2_hidden(k4_tarski(sK2(k1_wellord2(X0),X1),sK2(k1_wellord2(X0),X1)),k1_wellord2(X0)) ) ),
    inference(resolution,[],[f36,f30])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK2(X0,X1)),X0)
      | r1_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f28,f52])).

fof(f28,plain,(
    ~ r1_relat_2(k1_wellord2(sK0),sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ~ r1_relat_2(k1_wellord2(sK0),sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f13])).

fof(f13,plain,
    ( ? [X0] : ~ r1_relat_2(k1_wellord2(X0),X0)
   => ~ r1_relat_2(k1_wellord2(sK0),sK0) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : ~ r1_relat_2(k1_wellord2(X0),X0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : r1_relat_2(k1_wellord2(X0),X0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : r1_relat_2(k1_wellord2(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 12:00:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.49  % (29330)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (29339)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (29331)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (29331)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f54,f65,f88,f90,f93,f97])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    spl5_7),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f94])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    $false | spl5_7),
% 0.22/0.50    inference(resolution,[],[f87,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_2(k1_wellord2(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : v1_relat_2(k1_wellord2(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord2)).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ~v1_relat_2(k1_wellord2(sK0)) | spl5_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f86])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    spl5_7 <=> v1_relat_2(k1_wellord2(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ~spl5_5 | spl5_1 | spl5_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f91,f71,f52,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    spl5_5 <=> v1_relat_1(k1_wellord2(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    spl5_1 <=> r1_relat_2(k1_wellord2(sK0),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    spl5_3 <=> r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    r1_relat_2(k1_wellord2(sK0),sK0) | ~v1_relat_1(k1_wellord2(sK0)) | spl5_3),
% 0.22/0.50    inference(resolution,[],[f72,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r1_relat_2(X0,X1) | (~r2_hidden(k4_tarski(sK2(X0,X1),sK2(X0,X1)),X0) & r2_hidden(sK2(X0,X1),X1))) & (! [X3] : (r2_hidden(k4_tarski(X3,X3),X0) | ~r2_hidden(X3,X1)) | ~r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : (~r2_hidden(k4_tarski(X2,X2),X0) & r2_hidden(X2,X1)) => (~r2_hidden(k4_tarski(sK2(X0,X1),sK2(X0,X1)),X0) & r2_hidden(sK2(X0,X1),X1)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r1_relat_2(X0,X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X0) & r2_hidden(X2,X1))) & (! [X3] : (r2_hidden(k4_tarski(X3,X3),X0) | ~r2_hidden(X3,X1)) | ~r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(rectify,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r1_relat_2(X0,X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X0) & r2_hidden(X2,X1))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,X1)) | ~r1_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_relat_2(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) => r2_hidden(k4_tarski(X2,X2),X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ~r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0) | spl5_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f71])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    spl5_5),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f89])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    $false | spl5_5),
% 0.22/0.50    inference(resolution,[],[f79,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ~v1_relat_1(k1_wellord2(sK0)) | spl5_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f78])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ~spl5_5 | ~spl5_7 | ~spl5_3 | spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f84,f63,f71,f86,f78])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl5_2 <=> r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK2(k1_wellord2(sK0),sK0)),k1_wellord2(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ~r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0) | ~v1_relat_2(k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK0)) | spl5_2),
% 0.22/0.50    inference(forward_demodulation,[],[f68,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.22/0.50    inference(global_subsumption,[],[f30,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.50    inference(equality_resolution,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f25,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(rectify,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ~r2_hidden(sK2(k1_wellord2(sK0),sK0),k3_relat_1(k1_wellord2(sK0))) | ~v1_relat_2(k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK0)) | spl5_2),
% 0.22/0.50    inference(resolution,[],[f64,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0)) | ~v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (((v1_relat_2(X0) | (~r2_hidden(k4_tarski(sK1(X0),sK1(X0)),X0) & r2_hidden(sK1(X0),k3_relat_1(X0)))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK1(X0),sK1(X0)),X0) & r2_hidden(sK1(X0),k3_relat_1(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (((v1_relat_2(X0) | ? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X2] : (r2_hidden(k4_tarski(X2,X2),X0) | ~r2_hidden(X2,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(rectify,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (((v1_relat_2(X0) | ? [X1] : (~r2_hidden(k4_tarski(X1,X1),X0) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ! [X0] : ((v1_relat_2(X0) <=> ! [X1] : (r2_hidden(k4_tarski(X1,X1),X0) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => (v1_relat_2(X0) <=> ! [X1] : (r2_hidden(X1,k3_relat_1(X0)) => r2_hidden(k4_tarski(X1,X1),X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ~r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK2(k1_wellord2(sK0),sK0)),k1_wellord2(sK0)) | spl5_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f63])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ~spl5_2 | spl5_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f61,f52,f63])).
% 0.22/0.50  % (29338)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ~r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK2(k1_wellord2(sK0),sK0)),k1_wellord2(sK0)) | spl5_1),
% 0.22/0.50    inference(resolution,[],[f58,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ~r1_relat_2(k1_wellord2(sK0),sK0) | spl5_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f52])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_relat_2(k1_wellord2(X0),X1) | ~r2_hidden(k4_tarski(sK2(k1_wellord2(X0),X1),sK2(k1_wellord2(X0),X1)),k1_wellord2(X0))) )),
% 0.22/0.50    inference(resolution,[],[f36,f30])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK2(X0,X1)),X0) | r1_relat_2(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ~spl5_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f52])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ~r1_relat_2(k1_wellord2(sK0),sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ~r1_relat_2(k1_wellord2(sK0),sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0] : ~r1_relat_2(k1_wellord2(X0),X0) => ~r1_relat_2(k1_wellord2(sK0),sK0)),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ? [X0] : ~r1_relat_2(k1_wellord2(X0),X0)),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,negated_conjecture,(
% 0.22/0.50    ~! [X0] : r1_relat_2(k1_wellord2(X0),X0)),
% 0.22/0.50    inference(negated_conjecture,[],[f6])).
% 0.22/0.50  fof(f6,conjecture,(
% 0.22/0.50    ! [X0] : r1_relat_2(k1_wellord2(X0),X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord2)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (29331)------------------------------
% 0.22/0.50  % (29331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (29331)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (29331)Memory used [KB]: 10618
% 0.22/0.50  % (29331)Time elapsed: 0.010 s
% 0.22/0.50  % (29331)------------------------------
% 0.22/0.50  % (29331)------------------------------
% 0.22/0.50  % (29328)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (29321)Success in time 0.127 s
%------------------------------------------------------------------------------
