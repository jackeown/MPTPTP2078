%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 258 expanded)
%              Number of leaves         :   18 (  73 expanded)
%              Depth                    :   15
%              Number of atoms          :  514 (1490 expanded)
%              Number of equality atoms :   28 (  95 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f134,f154,f241,f247,f257,f274,f298,f307])).

fof(f307,plain,
    ( spl7_3
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f299,f126])).

fof(f126,plain,
    ( ~ r8_relat_2(k1_wellord2(sK0),sK0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl7_3
  <=> r8_relat_2(k1_wellord2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f299,plain,
    ( r8_relat_2(k1_wellord2(sK0),sK0)
    | ~ spl7_6 ),
    inference(resolution,[],[f147,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(k1_wellord2(X0),X1),sK3(k1_wellord2(X0),X1)),k1_wellord2(X0))
      | r8_relat_2(k1_wellord2(X0),X1) ) ),
    inference(resolution,[],[f41,f32])).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0)
      | r8_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
              & r2_hidden(sK3(X0,X1),X1)
              & r2_hidden(sK2(X0,X1),X1)
              & r2_hidden(sK1(X0,X1),X1) ) )
          & ( ! [X5,X6,X7] :
                ( r2_hidden(k4_tarski(X5,X7),X0)
                | ~ r2_hidden(k4_tarski(X6,X7),X0)
                | ~ r2_hidden(k4_tarski(X5,X6),X0)
                | ~ r2_hidden(X7,X1)
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2,X3,X4] :
          ( ~ r2_hidden(k4_tarski(X2,X4),X0)
          & r2_hidden(k4_tarski(X3,X4),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X4,X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
        & r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ? [X2,X3,X4] :
                ( ~ r2_hidden(k4_tarski(X2,X4),X0)
                & r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X5,X6,X7] :
                ( r2_hidden(k4_tarski(X5,X7),X0)
                | ~ r2_hidden(k4_tarski(X6,X7),X0)
                | ~ r2_hidden(k4_tarski(X5,X6),X0)
                | ~ r2_hidden(X7,X1)
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ? [X2,X3,X4] :
                ( ~ r2_hidden(k4_tarski(X2,X4),X0)
                & r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3,X4] :
                ( r2_hidden(k4_tarski(X2,X4),X0)
                | ~ r2_hidden(k4_tarski(X3,X4),X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( r2_hidden(k4_tarski(X2,X4),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( r2_hidden(k4_tarski(X2,X4),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( ( r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => r2_hidden(k4_tarski(X2,X4),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_2)).

fof(f147,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(sK0))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl7_6
  <=> r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f298,plain,
    ( ~ spl7_1
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f284,f78])).

fof(f78,plain,
    ( r1_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl7_1
  <=> r1_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f284,plain,
    ( ~ r1_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0))
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f283,f143])).

fof(f143,plain,
    ( r2_hidden(sK3(k1_wellord2(sK0),sK0),sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl7_5
  <=> r2_hidden(sK3(k1_wellord2(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f283,plain,
    ( ~ r1_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0))
    | ~ r2_hidden(sK3(k1_wellord2(sK0),sK0),sK0)
    | spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f155,f226])).

fof(f226,plain,
    ( r2_hidden(sK1(k1_wellord2(sK0),sK0),sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl7_7
  <=> r2_hidden(sK1(k1_wellord2(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f155,plain,
    ( ~ r1_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0))
    | ~ r2_hidden(sK1(k1_wellord2(sK0),sK0),sK0)
    | ~ r2_hidden(sK3(k1_wellord2(sK0),sK0),sK0)
    | spl7_6 ),
    inference(resolution,[],[f148,f59])).

fof(f59,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X0) ) ),
    inference(global_subsumption,[],[f32,f56])).

fof(f56,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
              | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
            & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
              | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
            & r2_hidden(sK5(X0,X1),X0)
            & r2_hidden(sK4(X0,X1),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f23])).

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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f148,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(sK0))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f146])).

fof(f274,plain,
    ( spl7_3
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | spl7_3
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f272,f32])).

fof(f272,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | spl7_3
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f271,f126])).

fof(f271,plain,
    ( r8_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f270,f239])).

fof(f239,plain,
    ( r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl7_10
  <=> r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f270,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0)
    | r8_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f259,f143])).

fof(f259,plain,
    ( ~ r2_hidden(sK3(k1_wellord2(sK0),sK0),sK0)
    | ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0)
    | r8_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl7_9 ),
    inference(resolution,[],[f236,f40])).

% (8749)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f236,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(X2))
        | ~ r2_hidden(sK3(k1_wellord2(sK0),sK0),X2)
        | ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),X2) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl7_9
  <=> ! [X2] :
        ( ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),X2)
        | ~ r2_hidden(sK3(k1_wellord2(sK0),sK0),X2)
        | ~ r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f257,plain,
    ( spl7_3
    | spl7_10 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl7_3
    | spl7_10 ),
    inference(subsumption_resolution,[],[f255,f32])).

fof(f255,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | spl7_3
    | spl7_10 ),
    inference(subsumption_resolution,[],[f253,f126])).

fof(f253,plain,
    ( r8_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl7_10 ),
    inference(resolution,[],[f240,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f240,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f238])).

fof(f247,plain,
    ( spl7_3
    | spl7_7 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl7_3
    | spl7_7 ),
    inference(subsumption_resolution,[],[f245,f32])).

fof(f245,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | spl7_3
    | spl7_7 ),
    inference(subsumption_resolution,[],[f243,f126])).

fof(f243,plain,
    ( r8_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl7_7 ),
    inference(resolution,[],[f227,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f227,plain,
    ( ~ r2_hidden(sK1(k1_wellord2(sK0),sK0),sK0)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f225])).

fof(f241,plain,
    ( spl7_9
    | ~ spl7_10
    | spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f233,f129,f125,f238,f235])).

fof(f129,plain,
    ( spl7_4
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK3(k1_wellord2(sK0),sK0))
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f233,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0)
        | ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),X2)
        | ~ r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(X2))
        | ~ r2_hidden(sK3(k1_wellord2(sK0),sK0),X2) )
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f232,f32])).

fof(f232,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0)
        | ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),X2)
        | ~ r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(X2))
        | ~ r2_hidden(sK3(k1_wellord2(sK0),sK0),X2)
        | ~ v1_relat_1(k1_wellord2(sK0)) )
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f221,f126])).

fof(f221,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0)
        | ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),X2)
        | ~ r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(X2))
        | ~ r2_hidden(sK3(k1_wellord2(sK0),sK0),X2)
        | r8_relat_2(k1_wellord2(sK0),sK0)
        | ~ v1_relat_1(k1_wellord2(sK0)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f136,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0))
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(k4_tarski(X0,sK3(k1_wellord2(sK0),sK0)),k1_wellord2(X1))
        | ~ r2_hidden(sK3(k1_wellord2(sK0),sK0),X1) )
    | ~ spl7_4 ),
    inference(resolution,[],[f130,f60])).

fof(f60,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0) ) ),
    inference(global_subsumption,[],[f32,f57])).

fof(f57,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK3(k1_wellord2(sK0),sK0))
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0)) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f154,plain,
    ( spl7_3
    | spl7_5 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl7_3
    | spl7_5 ),
    inference(subsumption_resolution,[],[f152,f32])).

fof(f152,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | spl7_3
    | spl7_5 ),
    inference(subsumption_resolution,[],[f150,f126])).

fof(f150,plain,
    ( r8_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl7_5 ),
    inference(resolution,[],[f144,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f144,plain,
    ( ~ r2_hidden(sK3(k1_wellord2(sK0),sK0),sK0)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f142])).

fof(f134,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f132,f31])).

fof(f31,plain,(
    ~ v8_relat_2(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ~ v8_relat_2(k1_wellord2(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f15])).

fof(f15,plain,
    ( ? [X0] : ~ v8_relat_2(k1_wellord2(X0))
   => ~ v8_relat_2(k1_wellord2(sK0)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : ~ v8_relat_2(k1_wellord2(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_wellord2)).

fof(f132,plain,
    ( v8_relat_2(k1_wellord2(sK0))
    | ~ spl7_3 ),
    inference(resolution,[],[f127,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r8_relat_2(k1_wellord2(X0),X0)
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f62,f32])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r8_relat_2(k1_wellord2(X0),X0)
      | v8_relat_2(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f34,f61])).

fof(f61,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f32,f58])).

fof(f58,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f34,plain,(
    ! [X0] :
      ( ~ r8_relat_2(X0,k3_relat_1(X0))
      | v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ~ r8_relat_2(X0,k3_relat_1(X0)) )
        & ( r8_relat_2(X0,k3_relat_1(X0))
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_2)).

fof(f127,plain,
    ( r8_relat_2(k1_wellord2(sK0),sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f131,plain,
    ( spl7_3
    | spl7_4
    | spl7_1 ),
    inference(avatar_split_clause,[],[f123,f77,f129,f125])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK3(k1_wellord2(sK0),sK0))
        | ~ r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0))
        | ~ r2_hidden(X0,sK0)
        | r8_relat_2(k1_wellord2(sK0),sK0) )
    | spl7_1 ),
    inference(subsumption_resolution,[],[f121,f32])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK3(k1_wellord2(sK0),sK0))
        | ~ r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0))
        | ~ r2_hidden(X0,sK0)
        | r8_relat_2(k1_wellord2(sK0),sK0)
        | ~ v1_relat_1(k1_wellord2(sK0)) )
    | spl7_1 ),
    inference(resolution,[],[f99,f36])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK1(k1_wellord2(sK0),sK0),X1)
        | ~ r1_tarski(X0,sK3(k1_wellord2(sK0),sK0))
        | ~ r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(X1))
        | ~ r2_hidden(X0,X1) )
    | spl7_1 ),
    inference(resolution,[],[f98,f60])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1(k1_wellord2(sK0),sK0),X0)
        | ~ r1_tarski(X0,sK3(k1_wellord2(sK0),sK0)) )
    | spl7_1 ),
    inference(subsumption_resolution,[],[f96,f79])).

fof(f79,plain,
    ( ~ r1_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK3(k1_wellord2(sK0),sK0))
        | ~ r1_tarski(sK1(k1_wellord2(sK0),sK0),X0)
        | r1_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)) )
    | spl7_1 ),
    inference(resolution,[],[f90,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK6(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),X1)
        | ~ r1_tarski(X0,sK3(k1_wellord2(sK0),sK0))
        | ~ r1_tarski(X1,X0) )
    | spl7_1 ),
    inference(resolution,[],[f86,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),X0)
        | ~ r1_tarski(X0,sK3(k1_wellord2(sK0),sK0)) )
    | spl7_1 ),
    inference(resolution,[],[f85,f49])).

fof(f85,plain,
    ( ~ r2_hidden(sK6(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),sK3(k1_wellord2(sK0),sK0))
    | spl7_1 ),
    inference(resolution,[],[f79,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:08:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (8748)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.48  % (8773)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.49  % (8764)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.49  % (8748)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (8756)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (8756)Refutation not found, incomplete strategy% (8756)------------------------------
% 0.20/0.50  % (8756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (8756)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (8756)Memory used [KB]: 10618
% 0.20/0.50  % (8756)Time elapsed: 0.113 s
% 0.20/0.50  % (8756)------------------------------
% 0.20/0.50  % (8756)------------------------------
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f308,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f131,f134,f154,f241,f247,f257,f274,f298,f307])).
% 0.20/0.50  fof(f307,plain,(
% 0.20/0.50    spl7_3 | ~spl7_6),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f306])).
% 0.20/0.50  fof(f306,plain,(
% 0.20/0.50    $false | (spl7_3 | ~spl7_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f299,f126])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    ~r8_relat_2(k1_wellord2(sK0),sK0) | spl7_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f125])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    spl7_3 <=> r8_relat_2(k1_wellord2(sK0),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.50  fof(f299,plain,(
% 0.20/0.50    r8_relat_2(k1_wellord2(sK0),sK0) | ~spl7_6),
% 0.20/0.50    inference(resolution,[],[f147,f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK1(k1_wellord2(X0),X1),sK3(k1_wellord2(X0),X1)),k1_wellord2(X0)) | r8_relat_2(k1_wellord2(X0),X1)) )),
% 0.20/0.50    inference(resolution,[],[f41,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0) | r8_relat_2(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((r8_relat_2(X0,X1) | (~r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0) & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) & r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK1(X0,X1),X1))) & (! [X5,X6,X7] : (r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X7,X1) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X1)) | ~r8_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2,X3,X4] : (~r2_hidden(k4_tarski(X2,X4),X0) & r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (~r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0) & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) & r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK1(X0,X1),X1)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((r8_relat_2(X0,X1) | ? [X2,X3,X4] : (~r2_hidden(k4_tarski(X2,X4),X0) & r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X5,X6,X7] : (r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X7,X1) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X1)) | ~r8_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(rectify,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((r8_relat_2(X0,X1) | ? [X2,X3,X4] : (~r2_hidden(k4_tarski(X2,X4),X0) & r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X2,X3,X4] : (r2_hidden(k4_tarski(X2,X4),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) | ~r8_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (r8_relat_2(X0,X1) <=> ! [X2,X3,X4] : (r2_hidden(k4_tarski(X2,X4),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (r8_relat_2(X0,X1) <=> ! [X2,X3,X4] : (r2_hidden(k4_tarski(X2,X4),X0) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r8_relat_2(X0,X1) <=> ! [X2,X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => r2_hidden(k4_tarski(X2,X4),X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_2)).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(sK0)) | ~spl7_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f146])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    spl7_6 <=> r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.50  fof(f298,plain,(
% 0.20/0.50    ~spl7_1 | ~spl7_5 | spl7_6 | ~spl7_7),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f297])).
% 0.20/0.50  fof(f297,plain,(
% 0.20/0.50    $false | (~spl7_1 | ~spl7_5 | spl7_6 | ~spl7_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f284,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    r1_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)) | ~spl7_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    spl7_1 <=> r1_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.50  fof(f284,plain,(
% 0.20/0.50    ~r1_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)) | (~spl7_5 | spl7_6 | ~spl7_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f283,f143])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    r2_hidden(sK3(k1_wellord2(sK0),sK0),sK0) | ~spl7_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f142])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    spl7_5 <=> r2_hidden(sK3(k1_wellord2(sK0),sK0),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.50  fof(f283,plain,(
% 0.20/0.50    ~r1_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)) | ~r2_hidden(sK3(k1_wellord2(sK0),sK0),sK0) | (spl7_6 | ~spl7_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f155,f226])).
% 0.20/0.50  fof(f226,plain,(
% 0.20/0.50    r2_hidden(sK1(k1_wellord2(sK0),sK0),sK0) | ~spl7_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f225])).
% 0.20/0.50  fof(f225,plain,(
% 0.20/0.50    spl7_7 <=> r2_hidden(sK1(k1_wellord2(sK0),sK0),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    ~r1_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)) | ~r2_hidden(sK1(k1_wellord2(sK0),sK0),sK0) | ~r2_hidden(sK3(k1_wellord2(sK0),sK0),sK0) | spl7_6),
% 0.20/0.50    inference(resolution,[],[f148,f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r1_tarski(X4,X5) | ~r2_hidden(X4,X0) | ~r2_hidden(X5,X0)) )),
% 0.20/0.50    inference(global_subsumption,[],[f32,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.50    inference(equality_resolution,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK4(X0,X1),sK5(X0,X1)) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & (r1_tarski(sK4(X0,X1),sK5(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK4(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK4(X0,X1),sK5(X0,X1)) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & (r1_tarski(sK4(X0,X1),sK5(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(rectify,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    ~r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(sK0)) | spl7_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f146])).
% 0.20/0.50  fof(f274,plain,(
% 0.20/0.50    spl7_3 | ~spl7_5 | ~spl7_9 | ~spl7_10),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f273])).
% 0.20/0.50  fof(f273,plain,(
% 0.20/0.50    $false | (spl7_3 | ~spl7_5 | ~spl7_9 | ~spl7_10)),
% 0.20/0.50    inference(subsumption_resolution,[],[f272,f32])).
% 0.20/0.50  fof(f272,plain,(
% 0.20/0.50    ~v1_relat_1(k1_wellord2(sK0)) | (spl7_3 | ~spl7_5 | ~spl7_9 | ~spl7_10)),
% 0.20/0.50    inference(subsumption_resolution,[],[f271,f126])).
% 0.20/0.50  fof(f271,plain,(
% 0.20/0.50    r8_relat_2(k1_wellord2(sK0),sK0) | ~v1_relat_1(k1_wellord2(sK0)) | (~spl7_5 | ~spl7_9 | ~spl7_10)),
% 0.20/0.50    inference(subsumption_resolution,[],[f270,f239])).
% 0.20/0.50  fof(f239,plain,(
% 0.20/0.50    r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0) | ~spl7_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f238])).
% 0.20/0.50  fof(f238,plain,(
% 0.20/0.50    spl7_10 <=> r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.50  fof(f270,plain,(
% 0.20/0.50    ~r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0) | r8_relat_2(k1_wellord2(sK0),sK0) | ~v1_relat_1(k1_wellord2(sK0)) | (~spl7_5 | ~spl7_9)),
% 0.20/0.50    inference(subsumption_resolution,[],[f259,f143])).
% 0.20/0.50  fof(f259,plain,(
% 0.20/0.50    ~r2_hidden(sK3(k1_wellord2(sK0),sK0),sK0) | ~r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0) | r8_relat_2(k1_wellord2(sK0),sK0) | ~v1_relat_1(k1_wellord2(sK0)) | ~spl7_9),
% 0.20/0.50    inference(resolution,[],[f236,f40])).
% 0.20/0.50  % (8749)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r8_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f236,plain,(
% 0.20/0.50    ( ! [X2] : (~r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(X2)) | ~r2_hidden(sK3(k1_wellord2(sK0),sK0),X2) | ~r2_hidden(sK2(k1_wellord2(sK0),sK0),X2)) ) | ~spl7_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f235])).
% 0.20/0.50  fof(f235,plain,(
% 0.20/0.50    spl7_9 <=> ! [X2] : (~r2_hidden(sK2(k1_wellord2(sK0),sK0),X2) | ~r2_hidden(sK3(k1_wellord2(sK0),sK0),X2) | ~r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(X2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.50  fof(f257,plain,(
% 0.20/0.50    spl7_3 | spl7_10),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f256])).
% 0.20/0.50  fof(f256,plain,(
% 0.20/0.50    $false | (spl7_3 | spl7_10)),
% 0.20/0.50    inference(subsumption_resolution,[],[f255,f32])).
% 0.20/0.50  fof(f255,plain,(
% 0.20/0.50    ~v1_relat_1(k1_wellord2(sK0)) | (spl7_3 | spl7_10)),
% 0.20/0.50    inference(subsumption_resolution,[],[f253,f126])).
% 0.20/0.50  fof(f253,plain,(
% 0.20/0.50    r8_relat_2(k1_wellord2(sK0),sK0) | ~v1_relat_1(k1_wellord2(sK0)) | spl7_10),
% 0.20/0.50    inference(resolution,[],[f240,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r8_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f240,plain,(
% 0.20/0.50    ~r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0) | spl7_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f238])).
% 0.20/0.50  fof(f247,plain,(
% 0.20/0.50    spl7_3 | spl7_7),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f246])).
% 0.20/0.50  fof(f246,plain,(
% 0.20/0.50    $false | (spl7_3 | spl7_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f245,f32])).
% 0.20/0.50  fof(f245,plain,(
% 0.20/0.50    ~v1_relat_1(k1_wellord2(sK0)) | (spl7_3 | spl7_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f243,f126])).
% 0.20/0.50  fof(f243,plain,(
% 0.20/0.50    r8_relat_2(k1_wellord2(sK0),sK0) | ~v1_relat_1(k1_wellord2(sK0)) | spl7_7),
% 0.20/0.50    inference(resolution,[],[f227,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r8_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f227,plain,(
% 0.20/0.50    ~r2_hidden(sK1(k1_wellord2(sK0),sK0),sK0) | spl7_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f225])).
% 0.20/0.50  fof(f241,plain,(
% 0.20/0.50    spl7_9 | ~spl7_10 | spl7_3 | ~spl7_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f233,f129,f125,f238,f235])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    spl7_4 <=> ! [X0] : (~r1_tarski(X0,sK3(k1_wellord2(sK0),sK0)) | ~r2_hidden(X0,sK0) | ~r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.50  fof(f233,plain,(
% 0.20/0.50    ( ! [X2] : (~r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0) | ~r2_hidden(sK2(k1_wellord2(sK0),sK0),X2) | ~r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(X2)) | ~r2_hidden(sK3(k1_wellord2(sK0),sK0),X2)) ) | (spl7_3 | ~spl7_4)),
% 0.20/0.50    inference(subsumption_resolution,[],[f232,f32])).
% 0.20/0.50  fof(f232,plain,(
% 0.20/0.50    ( ! [X2] : (~r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0) | ~r2_hidden(sK2(k1_wellord2(sK0),sK0),X2) | ~r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(X2)) | ~r2_hidden(sK3(k1_wellord2(sK0),sK0),X2) | ~v1_relat_1(k1_wellord2(sK0))) ) | (spl7_3 | ~spl7_4)),
% 0.20/0.50    inference(subsumption_resolution,[],[f221,f126])).
% 0.20/0.50  fof(f221,plain,(
% 0.20/0.50    ( ! [X2] : (~r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0) | ~r2_hidden(sK2(k1_wellord2(sK0),sK0),X2) | ~r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(X2)) | ~r2_hidden(sK3(k1_wellord2(sK0),sK0),X2) | r8_relat_2(k1_wellord2(sK0),sK0) | ~v1_relat_1(k1_wellord2(sK0))) ) | ~spl7_4),
% 0.20/0.50    inference(resolution,[],[f136,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r8_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0)) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,X1) | ~r2_hidden(k4_tarski(X0,sK3(k1_wellord2(sK0),sK0)),k1_wellord2(X1)) | ~r2_hidden(sK3(k1_wellord2(sK0),sK0),X1)) ) | ~spl7_4),
% 0.20/0.50    inference(resolution,[],[f130,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X4,X0,X5] : (r1_tarski(X4,X5) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r2_hidden(X5,X0)) )),
% 0.20/0.50    inference(global_subsumption,[],[f32,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X4,X0,X5] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.50    inference(equality_resolution,[],[f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X4,X0,X5,X1] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,sK3(k1_wellord2(sK0),sK0)) | ~r2_hidden(X0,sK0) | ~r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0))) ) | ~spl7_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f129])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    spl7_3 | spl7_5),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f153])).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    $false | (spl7_3 | spl7_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f152,f32])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    ~v1_relat_1(k1_wellord2(sK0)) | (spl7_3 | spl7_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f150,f126])).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    r8_relat_2(k1_wellord2(sK0),sK0) | ~v1_relat_1(k1_wellord2(sK0)) | spl7_5),
% 0.20/0.50    inference(resolution,[],[f144,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r8_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    ~r2_hidden(sK3(k1_wellord2(sK0),sK0),sK0) | spl7_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f142])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    ~spl7_3),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f133])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    $false | ~spl7_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f132,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ~v8_relat_2(k1_wellord2(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ~v8_relat_2(k1_wellord2(sK0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ? [X0] : ~v8_relat_2(k1_wellord2(X0)) => ~v8_relat_2(k1_wellord2(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ? [X0] : ~v8_relat_2(k1_wellord2(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,negated_conjecture,(
% 0.20/0.50    ~! [X0] : v8_relat_2(k1_wellord2(X0))),
% 0.20/0.50    inference(negated_conjecture,[],[f6])).
% 0.20/0.50  fof(f6,conjecture,(
% 0.20/0.50    ! [X0] : v8_relat_2(k1_wellord2(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_wellord2)).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    v8_relat_2(k1_wellord2(sK0)) | ~spl7_3),
% 0.20/0.50    inference(resolution,[],[f127,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0] : (~r8_relat_2(k1_wellord2(X0),X0) | v8_relat_2(k1_wellord2(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f62,f32])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X0] : (~r8_relat_2(k1_wellord2(X0),X0) | v8_relat_2(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.50    inference(superposition,[],[f34,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.20/0.50    inference(global_subsumption,[],[f32,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.50    inference(equality_resolution,[],[f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X0] : (~r8_relat_2(X0,k3_relat_1(X0)) | v8_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (((v8_relat_2(X0) | ~r8_relat_2(X0,k3_relat_1(X0))) & (r8_relat_2(X0,k3_relat_1(X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ! [X0] : ((v8_relat_2(X0) <=> r8_relat_2(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> r8_relat_2(X0,k3_relat_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_2)).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    r8_relat_2(k1_wellord2(sK0),sK0) | ~spl7_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f125])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    spl7_3 | spl7_4 | spl7_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f123,f77,f129,f125])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,sK3(k1_wellord2(sK0),sK0)) | ~r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0)) | ~r2_hidden(X0,sK0) | r8_relat_2(k1_wellord2(sK0),sK0)) ) | spl7_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f121,f32])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,sK3(k1_wellord2(sK0),sK0)) | ~r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0)) | ~r2_hidden(X0,sK0) | r8_relat_2(k1_wellord2(sK0),sK0) | ~v1_relat_1(k1_wellord2(sK0))) ) | spl7_1),
% 0.20/0.50    inference(resolution,[],[f99,f36])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(sK1(k1_wellord2(sK0),sK0),X1) | ~r1_tarski(X0,sK3(k1_wellord2(sK0),sK0)) | ~r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(X1)) | ~r2_hidden(X0,X1)) ) | spl7_1),
% 0.20/0.50    inference(resolution,[],[f98,f60])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(sK1(k1_wellord2(sK0),sK0),X0) | ~r1_tarski(X0,sK3(k1_wellord2(sK0),sK0))) ) | spl7_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f96,f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ~r1_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)) | spl7_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f77])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(X0,sK3(k1_wellord2(sK0),sK0)) | ~r1_tarski(sK1(k1_wellord2(sK0),sK0),X0) | r1_tarski(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0))) ) | spl7_1),
% 0.20/0.50    inference(resolution,[],[f90,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(sK6(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),X1) | ~r1_tarski(X0,sK3(k1_wellord2(sK0),sK0)) | ~r1_tarski(X1,X0)) ) | spl7_1),
% 0.20/0.51    inference(resolution,[],[f86,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK6(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),X0) | ~r1_tarski(X0,sK3(k1_wellord2(sK0),sK0))) ) | spl7_1),
% 0.20/0.51    inference(resolution,[],[f85,f49])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ~r2_hidden(sK6(sK1(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),sK3(k1_wellord2(sK0),sK0)) | spl7_1),
% 0.20/0.51    inference(resolution,[],[f79,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK6(X0,X1),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (8748)------------------------------
% 0.20/0.51  % (8748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8748)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (8748)Memory used [KB]: 10874
% 0.20/0.51  % (8748)Time elapsed: 0.114 s
% 0.20/0.51  % (8748)------------------------------
% 0.20/0.51  % (8748)------------------------------
% 0.20/0.51  % (8749)Refutation not found, incomplete strategy% (8749)------------------------------
% 0.20/0.51  % (8749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8749)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (8749)Memory used [KB]: 6268
% 0.20/0.51  % (8749)Time elapsed: 0.101 s
% 0.20/0.51  % (8749)------------------------------
% 0.20/0.51  % (8749)------------------------------
% 0.20/0.51  % (8746)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (8740)Success in time 0.148 s
%------------------------------------------------------------------------------
