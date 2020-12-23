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
% DateTime   : Thu Dec  3 12:48:15 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 128 expanded)
%              Number of leaves         :   10 (  34 expanded)
%              Depth                    :   18
%              Number of atoms          :  203 ( 437 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f84,f121])).

fof(f121,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f119,f26])).

fof(f26,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f119,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f118,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)
      | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
          | ~ r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        | ~ r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
          & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f118,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | spl4_2 ),
    inference(resolution,[],[f114,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f114,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f110,f44])).

fof(f44,plain,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_2
  <=> r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f110,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | spl4_2 ),
    inference(resolution,[],[f109,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f109,plain,
    ( r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK3(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f107,f24])).

fof(f107,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK3(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK1)
    | spl4_2 ),
    inference(resolution,[],[f72,f44])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X1),X0),X2)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(X1),X0),X2),sK3(k5_relat_1(k6_relat_1(X1),X0),X2)),X0) ) ),
    inference(subsumption_resolution,[],[f71,f26])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k5_relat_1(k6_relat_1(X1),X0),X2)
      | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(X1),X0),X2),sK3(k5_relat_1(k6_relat_1(X1),X0),X2)),X0)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k5_relat_1(k6_relat_1(X1),X0),X2)
      | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(X1),X0),X2),sK3(k5_relat_1(k6_relat_1(X1),X0),X2)),X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(resolution,[],[f53,f30])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X2)
      | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(X0),X1),X2),sK3(k5_relat_1(k6_relat_1(X0),X1),X2)),X1) ) ),
    inference(resolution,[],[f35,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | r2_hidden(k4_tarski(X0,X1),X3)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).

fof(f84,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f82,f24])).

fof(f82,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f81,f26])).

fof(f81,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(resolution,[],[f77,f30])).

fof(f77,plain,
    ( ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f73,f40])).

fof(f40,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_1
  <=> r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f73,plain,
    ( r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)
    | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | spl4_1 ),
    inference(resolution,[],[f69,f29])).

fof(f69,plain,
    ( r2_hidden(k4_tarski(sK2(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK3(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f67,f24])).

fof(f67,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK2(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK3(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK1)
    | spl4_1 ),
    inference(resolution,[],[f66,f40])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X2)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(k5_relat_1(X0,k6_relat_1(X1)),X2),sK3(k5_relat_1(X0,k6_relat_1(X1)),X2)),X0) ) ),
    inference(subsumption_resolution,[],[f65,f26])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X2)
      | r2_hidden(k4_tarski(sK2(k5_relat_1(X0,k6_relat_1(X1)),X2),sK3(k5_relat_1(X0,k6_relat_1(X1)),X2)),X0)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X2)
      | r2_hidden(k4_tarski(sK2(k5_relat_1(X0,k6_relat_1(X1)),X2),sK3(k5_relat_1(X0,k6_relat_1(X1)),X2)),X0)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f52,f30])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(k5_relat_1(X0,k6_relat_1(X1)))
      | ~ v1_relat_1(X0)
      | r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X2)
      | r2_hidden(k4_tarski(sK2(k5_relat_1(X0,k6_relat_1(X1)),X2),sK3(k5_relat_1(X0,k6_relat_1(X1)),X2)),X0) ) ),
    inference(resolution,[],[f32,f28])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | r2_hidden(k4_tarski(X0,X1),X3)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f21])).

% (1537)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_relat_1)).

fof(f45,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f25,f42,f38])).

fof(f25,plain,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)
    | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.40  % (1542)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.19/0.47  % (1529)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.19/0.48  % (1529)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f122,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(avatar_sat_refutation,[],[f45,f84,f121])).
% 0.19/0.48  fof(f121,plain,(
% 0.19/0.48    spl4_2),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f120])).
% 0.19/0.48  fof(f120,plain,(
% 0.19/0.48    $false | spl4_2),
% 0.19/0.48    inference(subsumption_resolution,[],[f119,f26])).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.19/0.48  fof(f119,plain,(
% 0.19/0.48    ~v1_relat_1(k6_relat_1(sK0)) | spl4_2),
% 0.19/0.48    inference(subsumption_resolution,[],[f118,f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    v1_relat_1(sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    (~r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) | ~r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)) & v1_relat_1(sK1)),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    ? [X0,X1] : ((~r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) & v1_relat_1(X1)) => ((~r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) | ~r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)) & v1_relat_1(sK1))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f8,plain,(
% 0.19/0.48    ? [X0,X1] : ((~r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) & v1_relat_1(X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f7])).
% 0.19/0.48  fof(f7,negated_conjecture,(
% 0.19/0.48    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 0.19/0.48    inference(negated_conjecture,[],[f6])).
% 0.19/0.48  fof(f6,conjecture,(
% 0.19/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 0.19/0.48  fof(f118,plain,(
% 0.19/0.48    ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(sK0)) | spl4_2),
% 0.19/0.48    inference(resolution,[],[f114,f30])).
% 0.19/0.48  fof(f30,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f11])).
% 0.19/0.48  fof(f11,plain,(
% 0.19/0.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(flattening,[],[f10])).
% 0.19/0.48  fof(f10,plain,(
% 0.19/0.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.19/0.48  fof(f114,plain,(
% 0.19/0.48    ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | spl4_2),
% 0.19/0.48    inference(subsumption_resolution,[],[f110,f44])).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    ~r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) | spl4_2),
% 0.19/0.48    inference(avatar_component_clause,[],[f42])).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    spl4_2 <=> r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.48  fof(f110,plain,(
% 0.19/0.48    r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) | ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | spl4_2),
% 0.19/0.48    inference(resolution,[],[f109,f29])).
% 0.19/0.48  fof(f29,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f19])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(rectify,[],[f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(nnf_transformation,[],[f9])).
% 0.19/0.48  fof(f9,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).
% 0.19/0.48  fof(f109,plain,(
% 0.19/0.48    r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK3(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK1) | spl4_2),
% 0.19/0.48    inference(subsumption_resolution,[],[f107,f24])).
% 0.19/0.48  fof(f107,plain,(
% 0.19/0.48    ~v1_relat_1(sK1) | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK3(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK1) | spl4_2),
% 0.19/0.48    inference(resolution,[],[f72,f44])).
% 0.19/0.48  fof(f72,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X1),X0),X2) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(X1),X0),X2),sK3(k5_relat_1(k6_relat_1(X1),X0),X2)),X0)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f71,f26])).
% 0.19/0.48  fof(f71,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k5_relat_1(k6_relat_1(X1),X0),X2) | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(X1),X0),X2),sK3(k5_relat_1(k6_relat_1(X1),X0),X2)),X0) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.19/0.48    inference(duplicate_literal_removal,[],[f70])).
% 0.19/0.48  fof(f70,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k5_relat_1(k6_relat_1(X1),X0),X2) | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(X1),X0),X2),sK3(k5_relat_1(k6_relat_1(X1),X0),X2)),X0) | ~v1_relat_1(X0) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.19/0.48    inference(resolution,[],[f53,f30])).
% 0.19/0.48  fof(f53,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(X1) | r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X2) | r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(X0),X1),X2),sK3(k5_relat_1(k6_relat_1(X0),X1),X2)),X1)) )),
% 0.19/0.48    inference(resolution,[],[f35,f28])).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f19])).
% 0.19/0.48  fof(f35,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | r2_hidden(k4_tarski(X0,X1),X3) | ~v1_relat_1(X3)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) | ~v1_relat_1(X3))),
% 0.19/0.48    inference(flattening,[],[f22])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | (~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)))) | ~v1_relat_1(X3))),
% 0.19/0.48    inference(nnf_transformation,[],[f13])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))) | ~v1_relat_1(X3))),
% 0.19/0.48    inference(ennf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).
% 0.19/0.48  fof(f84,plain,(
% 0.19/0.48    spl4_1),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f83])).
% 0.19/0.48  fof(f83,plain,(
% 0.19/0.48    $false | spl4_1),
% 0.19/0.48    inference(subsumption_resolution,[],[f82,f24])).
% 0.19/0.48  fof(f82,plain,(
% 0.19/0.48    ~v1_relat_1(sK1) | spl4_1),
% 0.19/0.48    inference(subsumption_resolution,[],[f81,f26])).
% 0.19/0.48  fof(f81,plain,(
% 0.19/0.48    ~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK1) | spl4_1),
% 0.19/0.48    inference(resolution,[],[f77,f30])).
% 0.19/0.48  fof(f77,plain,(
% 0.19/0.48    ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0))) | spl4_1),
% 0.19/0.48    inference(subsumption_resolution,[],[f73,f40])).
% 0.19/0.48  fof(f40,plain,(
% 0.19/0.48    ~r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) | spl4_1),
% 0.19/0.48    inference(avatar_component_clause,[],[f38])).
% 0.19/0.48  fof(f38,plain,(
% 0.19/0.48    spl4_1 <=> r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.48  fof(f73,plain,(
% 0.19/0.48    r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) | ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0))) | spl4_1),
% 0.19/0.48    inference(resolution,[],[f69,f29])).
% 0.19/0.48  fof(f69,plain,(
% 0.19/0.48    r2_hidden(k4_tarski(sK2(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK3(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK1) | spl4_1),
% 0.19/0.48    inference(subsumption_resolution,[],[f67,f24])).
% 0.19/0.48  fof(f67,plain,(
% 0.19/0.48    ~v1_relat_1(sK1) | r2_hidden(k4_tarski(sK2(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK3(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK1) | spl4_1),
% 0.19/0.48    inference(resolution,[],[f66,f40])).
% 0.19/0.48  fof(f66,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X2) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(k5_relat_1(X0,k6_relat_1(X1)),X2),sK3(k5_relat_1(X0,k6_relat_1(X1)),X2)),X0)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f65,f26])).
% 0.19/0.48  fof(f65,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X2) | r2_hidden(k4_tarski(sK2(k5_relat_1(X0,k6_relat_1(X1)),X2),sK3(k5_relat_1(X0,k6_relat_1(X1)),X2)),X0) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.19/0.48    inference(duplicate_literal_removal,[],[f64])).
% 0.19/0.48  fof(f64,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X2) | r2_hidden(k4_tarski(sK2(k5_relat_1(X0,k6_relat_1(X1)),X2),sK3(k5_relat_1(X0,k6_relat_1(X1)),X2)),X0) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(resolution,[],[f52,f30])).
% 0.19/0.48  fof(f52,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) | ~v1_relat_1(X0) | r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X2) | r2_hidden(k4_tarski(sK2(k5_relat_1(X0,k6_relat_1(X1)),X2),sK3(k5_relat_1(X0,k6_relat_1(X1)),X2)),X0)) )),
% 0.19/0.48    inference(resolution,[],[f32,f28])).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | r2_hidden(k4_tarski(X0,X1),X3) | ~v1_relat_1(X3)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f21])).
% 0.19/0.48  % (1537)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2)) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) | ~v1_relat_1(X3))),
% 0.19/0.48    inference(flattening,[],[f20])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | (~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) | ~v1_relat_1(X3))),
% 0.19/0.48    inference(nnf_transformation,[],[f12])).
% 0.19/0.48  fof(f12,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))) | ~v1_relat_1(X3))),
% 0.19/0.48    inference(ennf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_relat_1)).
% 0.19/0.48  fof(f45,plain,(
% 0.19/0.48    ~spl4_1 | ~spl4_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f25,f42,f38])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    ~r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) | ~r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f15])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (1529)------------------------------
% 0.19/0.48  % (1529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (1529)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (1529)Memory used [KB]: 5373
% 0.19/0.48  % (1529)Time elapsed: 0.070 s
% 0.19/0.48  % (1529)------------------------------
% 0.19/0.48  % (1529)------------------------------
% 0.19/0.48  % (1528)Success in time 0.132 s
%------------------------------------------------------------------------------
