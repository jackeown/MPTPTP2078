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
% DateTime   : Thu Dec  3 12:47:30 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 179 expanded)
%              Number of leaves         :   15 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  258 ( 821 expanded)
%              Number of equality atoms :   26 (  82 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f409,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f66,f78,f81,f408])).

fof(f408,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | spl4_4 ),
    inference(resolution,[],[f387,f77])).

fof(f77,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_4
  <=> r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f387,plain,(
    ! [X31,X32] : r1_tarski(k4_xboole_0(X32,k4_xboole_0(X32,X31)),X31) ),
    inference(superposition,[],[f29,f367])).

% (10295)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (10312)Refutation not found, incomplete strategy% (10312)------------------------------
% (10312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10312)Termination reason: Refutation not found, incomplete strategy

% (10312)Memory used [KB]: 10618
% (10312)Time elapsed: 0.159 s
% (10312)------------------------------
% (10312)------------------------------
% (10321)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (10311)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (10316)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (10316)Refutation not found, incomplete strategy% (10316)------------------------------
% (10316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10316)Termination reason: Refutation not found, incomplete strategy

% (10316)Memory used [KB]: 1663
% (10316)Time elapsed: 0.167 s
% (10316)------------------------------
% (10316)------------------------------
fof(f367,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(duplicate_literal_removal,[],[f353])).

fof(f353,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) ),
    inference(resolution,[],[f87,f111])).

fof(f111,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK3(X2,X3,X3),X2)
      | k4_xboole_0(X2,k4_xboole_0(X2,X3)) = X3 ) ),
    inference(subsumption_resolution,[],[f108,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X1),X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1 ) ),
    inference(factoring,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f37,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f108,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK3(X2,X3,X3),X3)
      | ~ r2_hidden(sK3(X2,X3,X3),X2)
      | k4_xboole_0(X2,k4_xboole_0(X2,X3)) = X3 ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK3(X2,X3,X3),X3)
      | ~ r2_hidden(sK3(X2,X3,X3),X2)
      | k4_xboole_0(X2,k4_xboole_0(X2,X3)) = X3
      | k4_xboole_0(X2,k4_xboole_0(X2,X3)) = X3 ) ),
    inference(resolution,[],[f41,f85])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f38,f30])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f87,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK3(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X4,k4_xboole_0(X4,X5))),X5)
      | k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) ) ),
    inference(resolution,[],[f85,f48])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f34,f30])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f81,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f79,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(f79,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_3 ),
    inference(resolution,[],[f73,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f73,plain,
    ( ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_3
  <=> v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f78,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f69,f56,f75,f71])).

fof(f56,plain,
    ( spl4_2
  <=> r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f69,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
    | ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f68,f26])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f67,f24])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl4_2 ),
    inference(resolution,[],[f58,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(f58,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f66,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f64,f25])).

fof(f64,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(resolution,[],[f63,f31])).

fof(f63,plain,
    ( ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f62,f25])).

fof(f62,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f61,f24])).

fof(f61,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f60,f29])).

fof(f60,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl4_1 ),
    inference(resolution,[],[f28,f54])).

fof(f54,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl4_1
  <=> r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f59,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f50,f56,f52])).

fof(f50,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK2))
    | ~ r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f40,f39])).

fof(f39,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k5_relat_1(sK0,sK1),k4_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    inference(definition_unfolding,[],[f27,f30,f30])).

fof(f27,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (10298)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (10304)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (10296)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (10299)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (10323)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (10297)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (10317)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (10315)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (10307)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (10301)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (10313)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.54  % (10312)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.54  % (10303)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.54  % (10300)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.43/0.54  % (10314)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.54  % (10303)Refutation not found, incomplete strategy% (10303)------------------------------
% 1.43/0.54  % (10303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (10303)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.54  
% 1.43/0.54  % (10303)Memory used [KB]: 10618
% 1.43/0.54  % (10303)Time elapsed: 0.132 s
% 1.43/0.54  % (10303)------------------------------
% 1.43/0.54  % (10303)------------------------------
% 1.43/0.54  % (10309)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.43/0.54  % (10318)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.43/0.54  % (10310)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.43/0.54  % (10297)Refutation not found, incomplete strategy% (10297)------------------------------
% 1.43/0.54  % (10297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (10297)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.54  
% 1.43/0.54  % (10297)Memory used [KB]: 10618
% 1.43/0.54  % (10297)Time elapsed: 0.119 s
% 1.43/0.54  % (10297)------------------------------
% 1.43/0.54  % (10297)------------------------------
% 1.43/0.55  % (10308)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.43/0.55  % (10322)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.43/0.55  % (10306)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.43/0.55  % (10317)Refutation not found, incomplete strategy% (10317)------------------------------
% 1.43/0.55  % (10317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (10317)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (10317)Memory used [KB]: 10746
% 1.43/0.55  % (10317)Time elapsed: 0.129 s
% 1.43/0.55  % (10317)------------------------------
% 1.43/0.55  % (10317)------------------------------
% 1.43/0.55  % (10305)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.55  % (10320)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.43/0.55  % (10302)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.43/0.55  % (10319)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.57/0.56  % (10298)Refutation found. Thanks to Tanya!
% 1.57/0.56  % SZS status Theorem for theBenchmark
% 1.57/0.56  % SZS output start Proof for theBenchmark
% 1.57/0.56  fof(f409,plain,(
% 1.57/0.56    $false),
% 1.57/0.56    inference(avatar_sat_refutation,[],[f59,f66,f78,f81,f408])).
% 1.57/0.56  fof(f408,plain,(
% 1.57/0.56    spl4_4),
% 1.57/0.56    inference(avatar_contradiction_clause,[],[f399])).
% 1.57/0.56  fof(f399,plain,(
% 1.57/0.56    $false | spl4_4),
% 1.57/0.56    inference(resolution,[],[f387,f77])).
% 1.57/0.56  fof(f77,plain,(
% 1.57/0.56    ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) | spl4_4),
% 1.57/0.56    inference(avatar_component_clause,[],[f75])).
% 1.57/0.56  fof(f75,plain,(
% 1.57/0.56    spl4_4 <=> r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)),
% 1.57/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.57/0.56  fof(f387,plain,(
% 1.57/0.56    ( ! [X31,X32] : (r1_tarski(k4_xboole_0(X32,k4_xboole_0(X32,X31)),X31)) )),
% 1.57/0.56    inference(superposition,[],[f29,f367])).
% 1.57/0.56  % (10295)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.57/0.56  % (10312)Refutation not found, incomplete strategy% (10312)------------------------------
% 1.57/0.56  % (10312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (10312)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (10312)Memory used [KB]: 10618
% 1.57/0.56  % (10312)Time elapsed: 0.159 s
% 1.57/0.56  % (10312)------------------------------
% 1.57/0.56  % (10312)------------------------------
% 1.57/0.56  % (10321)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.57/0.56  % (10311)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.57/0.56  % (10316)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.57/0.56  % (10316)Refutation not found, incomplete strategy% (10316)------------------------------
% 1.57/0.56  % (10316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (10316)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (10316)Memory used [KB]: 1663
% 1.57/0.56  % (10316)Time elapsed: 0.167 s
% 1.57/0.56  % (10316)------------------------------
% 1.57/0.56  % (10316)------------------------------
% 1.57/0.57  fof(f367,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) )),
% 1.57/0.57    inference(duplicate_literal_removal,[],[f353])).
% 1.57/0.57  fof(f353,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) )),
% 1.57/0.57    inference(resolution,[],[f87,f111])).
% 1.57/0.57  fof(f111,plain,(
% 1.57/0.57    ( ! [X2,X3] : (~r2_hidden(sK3(X2,X3,X3),X2) | k4_xboole_0(X2,k4_xboole_0(X2,X3)) = X3) )),
% 1.57/0.57    inference(subsumption_resolution,[],[f108,f85])).
% 1.57/0.57  fof(f85,plain,(
% 1.57/0.57    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1) )),
% 1.57/0.57    inference(factoring,[],[f42])).
% 1.57/0.57  fof(f42,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 1.57/0.57    inference(definition_unfolding,[],[f37,f30])).
% 1.57/0.57  fof(f30,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f4])).
% 1.57/0.57  fof(f4,axiom,(
% 1.57/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.57/0.57  fof(f37,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f23])).
% 1.57/0.57  fof(f23,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 1.57/0.57  fof(f22,plain,(
% 1.57/0.57    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f21,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.57/0.57    inference(rectify,[],[f20])).
% 1.57/0.57  fof(f20,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.57/0.57    inference(flattening,[],[f19])).
% 1.57/0.57  fof(f19,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.57/0.57    inference(nnf_transformation,[],[f1])).
% 1.57/0.57  fof(f1,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.57/0.57  fof(f108,plain,(
% 1.57/0.57    ( ! [X2,X3] : (~r2_hidden(sK3(X2,X3,X3),X3) | ~r2_hidden(sK3(X2,X3,X3),X2) | k4_xboole_0(X2,k4_xboole_0(X2,X3)) = X3) )),
% 1.57/0.57    inference(duplicate_literal_removal,[],[f103])).
% 1.57/0.57  fof(f103,plain,(
% 1.57/0.57    ( ! [X2,X3] : (~r2_hidden(sK3(X2,X3,X3),X3) | ~r2_hidden(sK3(X2,X3,X3),X2) | k4_xboole_0(X2,k4_xboole_0(X2,X3)) = X3 | k4_xboole_0(X2,k4_xboole_0(X2,X3)) = X3) )),
% 1.57/0.57    inference(resolution,[],[f41,f85])).
% 1.57/0.57  fof(f41,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 1.57/0.57    inference(definition_unfolding,[],[f38,f30])).
% 1.57/0.57  fof(f38,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f23])).
% 1.57/0.57  fof(f87,plain,(
% 1.57/0.57    ( ! [X4,X5,X3] : (r2_hidden(sK3(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X4,k4_xboole_0(X4,X5))),X5) | k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5))))) )),
% 1.57/0.57    inference(resolution,[],[f85,f48])).
% 1.57/0.57  fof(f48,plain,(
% 1.57/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X4,X1)) )),
% 1.57/0.57    inference(equality_resolution,[],[f45])).
% 1.57/0.57  fof(f45,plain,(
% 1.57/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 1.57/0.57    inference(definition_unfolding,[],[f34,f30])).
% 1.57/0.57  fof(f34,plain,(
% 1.57/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.57/0.57    inference(cnf_transformation,[],[f23])).
% 1.57/0.57  fof(f29,plain,(
% 1.57/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f3])).
% 1.57/0.57  fof(f3,axiom,(
% 1.57/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.57/0.57  fof(f81,plain,(
% 1.57/0.57    spl4_3),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f80])).
% 1.57/0.57  fof(f80,plain,(
% 1.57/0.57    $false | spl4_3),
% 1.57/0.57    inference(subsumption_resolution,[],[f79,f25])).
% 1.57/0.57  fof(f25,plain,(
% 1.57/0.57    v1_relat_1(sK1)),
% 1.57/0.57    inference(cnf_transformation,[],[f18])).
% 1.57/0.57  fof(f18,plain,(
% 1.57/0.57    ((~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16,f15])).
% 1.57/0.57  fof(f15,plain,(
% 1.57/0.57    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f16,plain,(
% 1.57/0.57    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f17,plain,(
% 1.57/0.57    ? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f9,plain,(
% 1.57/0.57    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f8])).
% 1.57/0.57  fof(f8,negated_conjecture,(
% 1.57/0.57    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.57/0.57    inference(negated_conjecture,[],[f7])).
% 1.57/0.57  fof(f7,conjecture,(
% 1.57/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).
% 1.57/0.57  fof(f79,plain,(
% 1.57/0.57    ~v1_relat_1(sK1) | spl4_3),
% 1.57/0.57    inference(resolution,[],[f73,f31])).
% 1.57/0.57  fof(f31,plain,(
% 1.57/0.57    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f12])).
% 1.57/0.57  fof(f12,plain,(
% 1.57/0.57    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f5])).
% 1.57/0.57  fof(f5,axiom,(
% 1.57/0.57    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).
% 1.57/0.57  fof(f73,plain,(
% 1.57/0.57    ~v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl4_3),
% 1.57/0.57    inference(avatar_component_clause,[],[f71])).
% 1.57/0.57  fof(f71,plain,(
% 1.57/0.57    spl4_3 <=> v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.57/0.57  fof(f78,plain,(
% 1.57/0.57    ~spl4_3 | ~spl4_4 | spl4_2),
% 1.57/0.57    inference(avatar_split_clause,[],[f69,f56,f75,f71])).
% 1.57/0.57  fof(f56,plain,(
% 1.57/0.57    spl4_2 <=> r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.57/0.57  fof(f69,plain,(
% 1.57/0.57    ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) | ~v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl4_2),
% 1.57/0.57    inference(subsumption_resolution,[],[f68,f26])).
% 1.57/0.57  fof(f26,plain,(
% 1.57/0.57    v1_relat_1(sK2)),
% 1.57/0.57    inference(cnf_transformation,[],[f18])).
% 1.57/0.57  fof(f68,plain,(
% 1.57/0.57    ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl4_2),
% 1.57/0.57    inference(subsumption_resolution,[],[f67,f24])).
% 1.57/0.57  fof(f24,plain,(
% 1.57/0.57    v1_relat_1(sK0)),
% 1.57/0.57    inference(cnf_transformation,[],[f18])).
% 1.57/0.57  fof(f67,plain,(
% 1.57/0.57    ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) | ~v1_relat_1(sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl4_2),
% 1.57/0.57    inference(resolution,[],[f58,f28])).
% 1.57/0.57  fof(f28,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f11])).
% 1.57/0.57  fof(f11,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(flattening,[],[f10])).
% 1.57/0.57  fof(f10,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f6])).
% 1.57/0.57  fof(f6,axiom,(
% 1.57/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).
% 1.57/0.57  fof(f58,plain,(
% 1.57/0.57    ~r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK2)) | spl4_2),
% 1.57/0.57    inference(avatar_component_clause,[],[f56])).
% 1.57/0.57  fof(f66,plain,(
% 1.57/0.57    spl4_1),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f65])).
% 1.57/0.57  fof(f65,plain,(
% 1.57/0.57    $false | spl4_1),
% 1.57/0.57    inference(subsumption_resolution,[],[f64,f25])).
% 1.57/0.57  fof(f64,plain,(
% 1.57/0.57    ~v1_relat_1(sK1) | spl4_1),
% 1.57/0.57    inference(resolution,[],[f63,f31])).
% 1.57/0.57  fof(f63,plain,(
% 1.57/0.57    ~v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl4_1),
% 1.57/0.57    inference(subsumption_resolution,[],[f62,f25])).
% 1.57/0.57  fof(f62,plain,(
% 1.57/0.57    ~v1_relat_1(sK1) | ~v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl4_1),
% 1.57/0.57    inference(subsumption_resolution,[],[f61,f24])).
% 1.57/0.57  fof(f61,plain,(
% 1.57/0.57    ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl4_1),
% 1.57/0.57    inference(subsumption_resolution,[],[f60,f29])).
% 1.57/0.57  fof(f60,plain,(
% 1.57/0.57    ~r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl4_1),
% 1.57/0.57    inference(resolution,[],[f28,f54])).
% 1.57/0.57  fof(f54,plain,(
% 1.57/0.57    ~r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK1)) | spl4_1),
% 1.57/0.57    inference(avatar_component_clause,[],[f52])).
% 1.57/0.57  fof(f52,plain,(
% 1.57/0.57    spl4_1 <=> r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.57/0.57  fof(f59,plain,(
% 1.57/0.57    ~spl4_1 | ~spl4_2),
% 1.57/0.57    inference(avatar_split_clause,[],[f50,f56,f52])).
% 1.57/0.57  fof(f50,plain,(
% 1.57/0.57    ~r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK2)) | ~r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k5_relat_1(sK0,sK1))),
% 1.57/0.57    inference(resolution,[],[f40,f39])).
% 1.57/0.57  fof(f39,plain,(
% 1.57/0.57    ~r1_tarski(k5_relat_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k5_relat_1(sK0,sK1),k4_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))),
% 1.57/0.57    inference(definition_unfolding,[],[f27,f30,f30])).
% 1.57/0.57  fof(f27,plain,(
% 1.57/0.57    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 1.57/0.57    inference(cnf_transformation,[],[f18])).
% 1.57/0.57  fof(f40,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.57/0.57    inference(definition_unfolding,[],[f32,f30])).
% 1.57/0.57  fof(f32,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f14])).
% 1.57/0.57  fof(f14,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.57/0.57    inference(flattening,[],[f13])).
% 1.57/0.57  fof(f13,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.57/0.57    inference(ennf_transformation,[],[f2])).
% 1.57/0.57  fof(f2,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.57/0.57  % SZS output end Proof for theBenchmark
% 1.57/0.57  % (10298)------------------------------
% 1.57/0.57  % (10298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (10298)Termination reason: Refutation
% 1.57/0.57  
% 1.57/0.57  % (10298)Memory used [KB]: 11129
% 1.57/0.57  % (10298)Time elapsed: 0.158 s
% 1.57/0.57  % (10298)------------------------------
% 1.57/0.57  % (10298)------------------------------
% 1.57/0.57  % (10324)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.57/0.57  % (10294)Success in time 0.213 s
%------------------------------------------------------------------------------
