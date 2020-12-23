%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:05 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 227 expanded)
%              Number of leaves         :   10 (  57 expanded)
%              Depth                    :   15
%              Number of atoms          :  292 (1471 expanded)
%              Number of equality atoms :   48 ( 168 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f209,f217,f227])).

fof(f227,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f225,f30])).

fof(f30,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    & ! [X3] :
        ( ( sK1 != X3
          & r2_hidden(k4_tarski(X3,sK1),sK2) )
        | ~ r2_hidden(X3,k1_wellord1(sK2,sK0)) )
    & r2_hidden(sK1,k3_relat_1(sK2))
    & r2_hidden(sK0,k3_relat_1(sK2))
    & v2_wellord1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k4_tarski(X0,X1),X2)
        & ! [X3] :
            ( ( X1 != X3
              & r2_hidden(k4_tarski(X3,X1),X2) )
            | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
      & ! [X3] :
          ( ( sK1 != X3
            & r2_hidden(k4_tarski(X3,sK1),sK2) )
          | ~ r2_hidden(X3,k1_wellord1(sK2,sK0)) )
      & r2_hidden(sK1,k3_relat_1(sK2))
      & r2_hidden(sK0,k3_relat_1(sK2))
      & v2_wellord1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      & ! [X3] :
          ( ( X1 != X3
            & r2_hidden(k4_tarski(X3,X1),X2) )
          | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      & ! [X3] :
          ( ( X1 != X3
            & r2_hidden(k4_tarski(X3,X1),X2) )
          | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( ! [X3] :
                ( r2_hidden(X3,k1_wellord1(X2,X0))
               => ( X1 != X3
                  & r2_hidden(k4_tarski(X3,X1),X2) ) )
            & r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => r2_hidden(k4_tarski(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( ! [X3] :
              ( r2_hidden(X3,k1_wellord1(X2,X0))
             => ( X1 != X3
                & r2_hidden(k4_tarski(X3,X1),X2) ) )
          & r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => r2_hidden(k4_tarski(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_wellord1)).

fof(f225,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f223,f26])).

fof(f26,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f223,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl5_6 ),
    inference(resolution,[],[f222,f158])).

fof(f158,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_wellord1(sK2,X1),k1_wellord1(sK2,sK1))
      | ~ r2_hidden(X1,k3_relat_1(sK2))
      | r2_hidden(k4_tarski(X1,sK1),sK2) ) ),
    inference(resolution,[],[f156,f27])).

fof(f27,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(sK2))
      | ~ r1_tarski(k1_wellord1(sK2,X0),k1_wellord1(sK2,X1))
      | ~ r2_hidden(X0,k3_relat_1(sK2))
      | r2_hidden(k4_tarski(X0,X1),sK2) ) ),
    inference(subsumption_resolution,[],[f155,f24])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_wellord1(sK2,X0),k1_wellord1(sK2,X1))
      | ~ r2_hidden(X1,k3_relat_1(sK2))
      | ~ r2_hidden(X0,k3_relat_1(sK2))
      | r2_hidden(k4_tarski(X0,X1),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f41,f25])).

fof(f25,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_wellord1(X2)
      | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

% (20477)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

fof(f222,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl5_6 ),
    inference(resolution,[],[f84,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

% (20469)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f84,plain,
    ( r2_hidden(sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_6
  <=> r2_hidden(sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f217,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f215,f42])).

fof(f42,plain,(
    ~ r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X3] :
      ( sK1 != X3
      | ~ r2_hidden(X3,k1_wellord1(sK2,sK0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f215,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f207,f75])).

fof(f75,plain,
    ( sK1 = sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl5_4
  <=> sK1 = sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f207,plain,(
    r2_hidden(sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f204,f26])).

fof(f204,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | r2_hidden(sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) ),
    inference(resolution,[],[f197,f30])).

fof(f197,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(X1,sK1),sK2)
      | ~ r2_hidden(X1,k3_relat_1(sK2))
      | r2_hidden(sK4(k1_wellord1(sK2,X1),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,X1)) ) ),
    inference(resolution,[],[f158,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f209,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl5_5 ),
    inference(subsumption_resolution,[],[f207,f80])).

fof(f80,plain,
    ( ~ r2_hidden(sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl5_5
  <=> r2_hidden(sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f85,plain,
    ( ~ spl5_5
    | spl5_4
    | spl5_6 ),
    inference(avatar_split_clause,[],[f67,f82,f73,f78])).

fof(f67,plain,
    ( r2_hidden(sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))
    | sK1 = sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ r2_hidden(sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) ),
    inference(factoring,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k1_wellord1(sK2,sK0),X0),k1_wellord1(sK2,sK1))
      | sK1 = sK4(k1_wellord1(sK2,sK0),X0)
      | ~ r2_hidden(X1,k1_wellord1(sK2,sK0))
      | r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f63,f49])).

fof(f49,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(sK4(k1_wellord1(sK2,sK0),X3),sK1),sK2)
      | ~ r2_hidden(X2,k1_wellord1(sK2,sK0))
      | r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f47,f28])).

fof(f28,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_wellord1(sK2,sK0))
      | r2_hidden(k4_tarski(X3,sK1),sK2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X1,X2),X1)
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f37,f38])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | X0 = X1
      | r2_hidden(X0,k1_wellord1(sK2,X1)) ) ),
    inference(resolution,[],[f43,f24])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | r2_hidden(X4,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
                | sK3(X0,X1,X2) = X1
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
                  & sK3(X0,X1,X2) != X1 )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
          | sK3(X0,X1,X2) = X1
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
            & sK3(X0,X1,X2) != X1 )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:35:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.43  % (20471)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.47  % (20475)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.47  % (20491)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.47  % (20483)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.48  % (20471)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f228,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(avatar_sat_refutation,[],[f85,f209,f217,f227])).
% 0.19/0.49  fof(f227,plain,(
% 0.19/0.49    ~spl5_6),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f226])).
% 0.19/0.49  fof(f226,plain,(
% 0.19/0.49    $false | ~spl5_6),
% 0.19/0.49    inference(subsumption_resolution,[],[f225,f30])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ~r2_hidden(k4_tarski(sK0,sK1),sK2) & ! [X3] : ((sK1 != X3 & r2_hidden(k4_tarski(X3,sK1),sK2)) | ~r2_hidden(X3,k1_wellord1(sK2,sK0))) & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2)),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12])).
% 0.19/0.49  fof(f12,plain,(
% 0.19/0.49    ? [X0,X1,X2] : (~r2_hidden(k4_tarski(X0,X1),X2) & ! [X3] : ((X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2)) | ~r2_hidden(X3,k1_wellord1(X2,X0))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2)) => (~r2_hidden(k4_tarski(sK0,sK1),sK2) & ! [X3] : ((sK1 != X3 & r2_hidden(k4_tarski(X3,sK1),sK2)) | ~r2_hidden(X3,k1_wellord1(sK2,sK0))) & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f7,plain,(
% 0.19/0.49    ? [X0,X1,X2] : (~r2_hidden(k4_tarski(X0,X1),X2) & ! [X3] : ((X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2)) | ~r2_hidden(X3,k1_wellord1(X2,X0))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 0.19/0.49    inference(flattening,[],[f6])).
% 0.19/0.49  fof(f6,plain,(
% 0.19/0.49    ? [X0,X1,X2] : ((~r2_hidden(k4_tarski(X0,X1),X2) & (! [X3] : ((X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2)) | ~r2_hidden(X3,k1_wellord1(X2,X0))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 0.19/0.49    inference(ennf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((! [X3] : (r2_hidden(X3,k1_wellord1(X2,X0)) => (X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => r2_hidden(k4_tarski(X0,X1),X2)))),
% 0.19/0.49    inference(negated_conjecture,[],[f4])).
% 0.19/0.49  fof(f4,conjecture,(
% 0.19/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((! [X3] : (r2_hidden(X3,k1_wellord1(X2,X0)) => (X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => r2_hidden(k4_tarski(X0,X1),X2)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_wellord1)).
% 0.19/0.49  fof(f225,plain,(
% 0.19/0.49    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl5_6),
% 0.19/0.49    inference(subsumption_resolution,[],[f223,f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    r2_hidden(sK0,k3_relat_1(sK2))),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f223,plain,(
% 0.19/0.49    ~r2_hidden(sK0,k3_relat_1(sK2)) | r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl5_6),
% 0.19/0.49    inference(resolution,[],[f222,f158])).
% 0.19/0.49  fof(f158,plain,(
% 0.19/0.49    ( ! [X1] : (~r1_tarski(k1_wellord1(sK2,X1),k1_wellord1(sK2,sK1)) | ~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X1,sK1),sK2)) )),
% 0.19/0.49    inference(resolution,[],[f156,f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    r2_hidden(sK1,k3_relat_1(sK2))),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f156,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k3_relat_1(sK2)) | ~r1_tarski(k1_wellord1(sK2,X0),k1_wellord1(sK2,X1)) | ~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X0,X1),sK2)) )),
% 0.19/0.49    inference(subsumption_resolution,[],[f155,f24])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    v1_relat_1(sK2)),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f155,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r1_tarski(k1_wellord1(sK2,X0),k1_wellord1(sK2,X1)) | ~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X0,X1),sK2) | ~v1_relat_1(sK2)) )),
% 0.19/0.49    inference(resolution,[],[f41,f25])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    v2_wellord1(sK2)),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f41,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~v2_wellord1(X2) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 0.19/0.49    inference(nnf_transformation,[],[f11])).
% 0.19/0.49  fof(f11,plain,(
% 0.19/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 0.19/0.49    inference(flattening,[],[f10])).
% 0.19/0.49  % (20477)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.49  fof(f10,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) | (~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2))) | ~v1_relat_1(X2))),
% 0.19/0.49    inference(ennf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).
% 0.19/0.49  fof(f222,plain,(
% 0.19/0.49    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl5_6),
% 0.19/0.49    inference(resolution,[],[f84,f39])).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.49    inference(rectify,[],[f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.49    inference(nnf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,plain,(
% 0.19/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f1])).
% 0.19/0.49  % (20469)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.49  fof(f84,plain,(
% 0.19/0.49    r2_hidden(sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1)) | ~spl5_6),
% 0.19/0.49    inference(avatar_component_clause,[],[f82])).
% 0.19/0.49  fof(f82,plain,(
% 0.19/0.49    spl5_6 <=> r2_hidden(sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.19/0.49  fof(f217,plain,(
% 0.19/0.49    ~spl5_4),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f216])).
% 0.19/0.49  fof(f216,plain,(
% 0.19/0.49    $false | ~spl5_4),
% 0.19/0.49    inference(subsumption_resolution,[],[f215,f42])).
% 0.19/0.49  fof(f42,plain,(
% 0.19/0.49    ~r2_hidden(sK1,k1_wellord1(sK2,sK0))),
% 0.19/0.49    inference(equality_resolution,[],[f29])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ( ! [X3] : (sK1 != X3 | ~r2_hidden(X3,k1_wellord1(sK2,sK0))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f215,plain,(
% 0.19/0.49    r2_hidden(sK1,k1_wellord1(sK2,sK0)) | ~spl5_4),
% 0.19/0.49    inference(forward_demodulation,[],[f207,f75])).
% 0.19/0.49  fof(f75,plain,(
% 0.19/0.49    sK1 = sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl5_4),
% 0.19/0.49    inference(avatar_component_clause,[],[f73])).
% 0.19/0.49  fof(f73,plain,(
% 0.19/0.49    spl5_4 <=> sK1 = sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.49  fof(f207,plain,(
% 0.19/0.49    r2_hidden(sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))),
% 0.19/0.49    inference(subsumption_resolution,[],[f204,f26])).
% 0.19/0.49  fof(f204,plain,(
% 0.19/0.49    ~r2_hidden(sK0,k3_relat_1(sK2)) | r2_hidden(sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))),
% 0.19/0.49    inference(resolution,[],[f197,f30])).
% 0.19/0.49  fof(f197,plain,(
% 0.19/0.49    ( ! [X1] : (r2_hidden(k4_tarski(X1,sK1),sK2) | ~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(sK4(k1_wellord1(sK2,X1),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,X1))) )),
% 0.19/0.49    inference(resolution,[],[f158,f38])).
% 0.19/0.49  fof(f38,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f209,plain,(
% 0.19/0.49    spl5_5),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f208])).
% 0.19/0.49  fof(f208,plain,(
% 0.19/0.49    $false | spl5_5),
% 0.19/0.49    inference(subsumption_resolution,[],[f207,f80])).
% 0.19/0.49  fof(f80,plain,(
% 0.19/0.49    ~r2_hidden(sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) | spl5_5),
% 0.19/0.49    inference(avatar_component_clause,[],[f78])).
% 0.19/0.49  fof(f78,plain,(
% 0.19/0.49    spl5_5 <=> r2_hidden(sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.49  fof(f85,plain,(
% 0.19/0.49    ~spl5_5 | spl5_4 | spl5_6),
% 0.19/0.49    inference(avatar_split_clause,[],[f67,f82,f73,f78])).
% 0.19/0.49  fof(f67,plain,(
% 0.19/0.49    r2_hidden(sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1)) | sK1 = sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(sK4(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))),
% 0.19/0.49    inference(factoring,[],[f64])).
% 0.19/0.49  fof(f64,plain,(
% 0.19/0.49    ( ! [X0,X1] : (r2_hidden(sK4(k1_wellord1(sK2,sK0),X0),k1_wellord1(sK2,sK1)) | sK1 = sK4(k1_wellord1(sK2,sK0),X0) | ~r2_hidden(X1,k1_wellord1(sK2,sK0)) | r2_hidden(X1,X0)) )),
% 0.19/0.49    inference(resolution,[],[f63,f49])).
% 0.19/0.49  fof(f49,plain,(
% 0.19/0.49    ( ! [X2,X3] : (r2_hidden(k4_tarski(sK4(k1_wellord1(sK2,sK0),X3),sK1),sK2) | ~r2_hidden(X2,k1_wellord1(sK2,sK0)) | r2_hidden(X2,X3)) )),
% 0.19/0.49    inference(resolution,[],[f47,f28])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    ( ! [X3] : (~r2_hidden(X3,k1_wellord1(sK2,sK0)) | r2_hidden(k4_tarski(X3,sK1),sK2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f47,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK4(X1,X2),X1) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.19/0.49    inference(resolution,[],[f37,f38])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f22])).
% 0.19/0.49  fof(f63,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | r2_hidden(X0,k1_wellord1(sK2,X1))) )),
% 0.19/0.49    inference(resolution,[],[f43,f24])).
% 0.19/0.49  fof(f43,plain,(
% 0.19/0.49    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | r2_hidden(X4,k1_wellord1(X0,X1))) )),
% 0.19/0.49    inference(equality_resolution,[],[f33])).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0) | sK3(X0,X1,X2) = X1 | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0) & sK3(X0,X1,X2) != X1) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0) | sK3(X0,X1,X2) = X1 | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0) & sK3(X0,X1,X2) != X1) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(rectify,[],[f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(flattening,[],[f14])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(nnf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,plain,(
% 0.19/0.49    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (20471)------------------------------
% 0.19/0.49  % (20471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (20471)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (20471)Memory used [KB]: 10874
% 0.19/0.49  % (20471)Time elapsed: 0.098 s
% 0.19/0.49  % (20471)------------------------------
% 0.19/0.49  % (20471)------------------------------
% 0.19/0.50  % (20467)Success in time 0.154 s
%------------------------------------------------------------------------------
