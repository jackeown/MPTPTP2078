%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:23 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 209 expanded)
%              Number of leaves         :   21 (  77 expanded)
%              Depth                    :   17
%              Number of atoms          :  382 ( 985 expanded)
%              Number of equality atoms :   40 ( 155 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f530,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f504,f527])).

fof(f527,plain,(
    ~ spl14_1 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f525,f39])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1))
    & r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,X1))
            & r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,X1))
          & r1_tarski(k2_relat_1(sK0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,X1))
        & r1_tarski(k2_relat_1(sK0),k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1))
      & r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,X1))
          & r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,X1))
          & r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
             => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f525,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f524,f40])).

fof(f40,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f524,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f513,f508])).

fof(f508,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0),sK0)
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f506,f69])).

fof(f69,plain,(
    ~ sQ13_eqProxy(k1_relat_1(sK0),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(equality_proxy_replacement,[],[f42,f68])).

fof(f68,plain,(
    ! [X1,X0] :
      ( sQ13_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ13_eqProxy])])).

fof(f42,plain,(
    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f506,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0),sK0)
        | sQ13_eqProxy(k1_relat_1(sK0),k1_relat_1(k5_relat_1(sK0,sK1))) )
    | ~ spl14_1 ),
    inference(resolution,[],[f104,f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
      | sQ13_eqProxy(k1_relat_1(X0),X1) ) ),
    inference(equality_proxy_replacement,[],[f56,f68])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f28,f31,f30,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f104,plain,
    ( r2_hidden(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl14_1
  <=> r2_hidden(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f513,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK5(sK0,sK1,sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK9(k5_relat_1(sK0,sK1),sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))))),sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl14_1 ),
    inference(resolution,[],[f505,f80])).

fof(f80,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f63,f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f63,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f21,f20,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

% (22954)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f505,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK9(k5_relat_1(sK0,sK1),sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))))),k5_relat_1(sK0,sK1))
    | ~ spl14_1 ),
    inference(resolution,[],[f104,f65])).

fof(f65,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f504,plain,(
    ~ spl14_2 ),
    inference(avatar_contradiction_clause,[],[f501])).

fof(f501,plain,
    ( $false
    | ~ spl14_2 ),
    inference(resolution,[],[f500,f108])).

fof(f108,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))),sK0)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl14_2
  <=> r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f500,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0),sK0)
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f498,f69])).

fof(f498,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0),sK0)
        | sQ13_eqProxy(k1_relat_1(sK0),k1_relat_1(k5_relat_1(sK0,sK1))) )
    | ~ spl14_2 ),
    inference(resolution,[],[f486,f73])).

fof(f486,plain,
    ( r2_hidden(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl14_2 ),
    inference(resolution,[],[f474,f64])).

fof(f64,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f474,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK9(sK1,sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))))),k5_relat_1(sK0,sK1))
    | ~ spl14_2 ),
    inference(resolution,[],[f181,f108])).

fof(f181,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k4_tarski(X2,sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))),sK0)
        | r2_hidden(k4_tarski(X2,sK9(sK1,sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))))),k5_relat_1(sK0,sK1)) )
    | ~ spl14_2 ),
    inference(resolution,[],[f173,f119])).

fof(f119,plain,
    ( r2_hidden(k4_tarski(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK9(sK1,sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))))),sK1)
    | ~ spl14_2 ),
    inference(resolution,[],[f117,f65])).

fof(f117,plain,
    ( r2_hidden(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
    | ~ spl14_2 ),
    inference(resolution,[],[f114,f41])).

fof(f41,plain,(
    r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK0),X0)
        | r2_hidden(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0) )
    | ~ spl14_2 ),
    inference(resolution,[],[f111,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f111,plain,
    ( r2_hidden(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(sK0))
    | ~ spl14_2 ),
    inference(resolution,[],[f108,f66])).

fof(f66,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK10(X0,X1)),X0)
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK11(X0,X1),sK10(X0,X1)),X0)
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK12(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f34,f37,f36,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK10(X0,X1)),X0)
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK10(X0,X1)),X0)
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK10(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK11(X0,X1),sK10(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK12(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f173,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(k4_tarski(X4,X5),sK1)
      | ~ r2_hidden(k4_tarski(X3,X4),sK0)
      | r2_hidden(k4_tarski(X3,X5),k5_relat_1(sK0,sK1)) ) ),
    inference(resolution,[],[f146,f40])).

fof(f146,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X3,X0),sK0)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(k4_tarski(X3,X1),k5_relat_1(sK0,X2)) ) ),
    inference(resolution,[],[f78,f39])).

fof(f78,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f61,f43])).

fof(f61,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f109,plain,
    ( spl14_1
    | spl14_2 ),
    inference(avatar_split_clause,[],[f100,f106,f102])).

fof(f100,plain,
    ( r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))),sK0)
    | r2_hidden(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(resolution,[],[f74,f69])).

fof(f74,plain,(
    ! [X0,X1] :
      ( sQ13_eqProxy(k1_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f55,f68])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:34:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (22940)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (22940)Refutation not found, incomplete strategy% (22940)------------------------------
% 0.21/0.50  % (22940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22963)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (22940)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22940)Memory used [KB]: 10746
% 0.21/0.51  % (22940)Time elapsed: 0.096 s
% 0.21/0.51  % (22940)------------------------------
% 0.21/0.51  % (22940)------------------------------
% 0.21/0.51  % (22955)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (22953)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (22949)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (22961)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (22944)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (22959)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (22943)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (22960)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (22946)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (22939)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.34/0.54  % (22960)Refutation not found, incomplete strategy% (22960)------------------------------
% 1.34/0.54  % (22960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (22960)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (22960)Memory used [KB]: 10746
% 1.34/0.54  % (22960)Time elapsed: 0.090 s
% 1.34/0.54  % (22960)------------------------------
% 1.34/0.54  % (22960)------------------------------
% 1.34/0.54  % (22941)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.54  % (22966)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.54  % (22942)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.54  % (22952)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.34/0.55  % (22955)Refutation found. Thanks to Tanya!
% 1.34/0.55  % SZS status Theorem for theBenchmark
% 1.34/0.55  % (22948)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.34/0.55  % SZS output start Proof for theBenchmark
% 1.34/0.55  fof(f530,plain,(
% 1.34/0.55    $false),
% 1.34/0.55    inference(avatar_sat_refutation,[],[f109,f504,f527])).
% 1.34/0.55  fof(f527,plain,(
% 1.34/0.55    ~spl14_1),
% 1.34/0.55    inference(avatar_contradiction_clause,[],[f526])).
% 1.34/0.55  fof(f526,plain,(
% 1.34/0.55    $false | ~spl14_1),
% 1.34/0.55    inference(subsumption_resolution,[],[f525,f39])).
% 1.34/0.55  fof(f39,plain,(
% 1.34/0.55    v1_relat_1(sK0)),
% 1.34/0.55    inference(cnf_transformation,[],[f16])).
% 1.34/0.55  fof(f16,plain,(
% 1.34/0.55    (k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1)) & r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.34/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15,f14])).
% 1.34/0.55  fof(f14,plain,(
% 1.34/0.55    ? [X0] : (? [X1] : (k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,X1)) & r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,X1)) & r1_tarski(k2_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f15,plain,(
% 1.34/0.55    ? [X1] : (k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,X1)) & r1_tarski(k2_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) => (k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1)) & r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f9,plain,(
% 1.34/0.55    ? [X0] : (? [X1] : (k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,X1)) & r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.34/0.55    inference(flattening,[],[f8])).
% 1.34/0.55  fof(f8,plain,(
% 1.34/0.55    ? [X0] : (? [X1] : ((k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,X1)) & r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.34/0.55    inference(ennf_transformation,[],[f7])).
% 1.34/0.55  fof(f7,negated_conjecture,(
% 1.34/0.55    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.34/0.55    inference(negated_conjecture,[],[f6])).
% 1.34/0.55  fof(f6,conjecture,(
% 1.34/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 1.34/0.55  fof(f525,plain,(
% 1.34/0.55    ~v1_relat_1(sK0) | ~spl14_1),
% 1.34/0.55    inference(subsumption_resolution,[],[f524,f40])).
% 1.34/0.55  fof(f40,plain,(
% 1.34/0.55    v1_relat_1(sK1)),
% 1.34/0.55    inference(cnf_transformation,[],[f16])).
% 1.34/0.55  fof(f524,plain,(
% 1.34/0.55    ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~spl14_1),
% 1.34/0.55    inference(subsumption_resolution,[],[f513,f508])).
% 1.34/0.55  fof(f508,plain,(
% 1.34/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0),sK0)) ) | ~spl14_1),
% 1.34/0.55    inference(subsumption_resolution,[],[f506,f69])).
% 1.34/0.55  fof(f69,plain,(
% 1.34/0.55    ~sQ13_eqProxy(k1_relat_1(sK0),k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.34/0.55    inference(equality_proxy_replacement,[],[f42,f68])).
% 1.34/0.55  fof(f68,plain,(
% 1.34/0.55    ! [X1,X0] : (sQ13_eqProxy(X0,X1) <=> X0 = X1)),
% 1.34/0.55    introduced(equality_proxy_definition,[new_symbols(naming,[sQ13_eqProxy])])).
% 1.34/0.55  fof(f42,plain,(
% 1.34/0.55    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1))),
% 1.34/0.55    inference(cnf_transformation,[],[f16])).
% 1.34/0.55  fof(f506,plain,(
% 1.34/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0),sK0) | sQ13_eqProxy(k1_relat_1(sK0),k1_relat_1(k5_relat_1(sK0,sK1)))) ) | ~spl14_1),
% 1.34/0.55    inference(resolution,[],[f104,f73])).
% 1.34/0.55  fof(f73,plain,(
% 1.34/0.55    ( ! [X0,X3,X1] : (~r2_hidden(sK7(X0,X1),X1) | ~r2_hidden(k4_tarski(sK7(X0,X1),X3),X0) | sQ13_eqProxy(k1_relat_1(X0),X1)) )),
% 1.34/0.55    inference(equality_proxy_replacement,[],[f56,f68])).
% 1.34/0.55  fof(f56,plain,(
% 1.34/0.55    ( ! [X0,X3,X1] : (k1_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(sK7(X0,X1),X3),X0) | ~r2_hidden(sK7(X0,X1),X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f32])).
% 1.34/0.55  fof(f32,plain,(
% 1.34/0.55    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK7(X0,X1),X3),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.34/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f28,f31,f30,f29])).
% 1.34/0.55  fof(f29,plain,(
% 1.34/0.55    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK7(X0,X1),X3),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f30,plain,(
% 1.34/0.55    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f31,plain,(
% 1.34/0.55    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f28,plain,(
% 1.34/0.55    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.34/0.55    inference(rectify,[],[f27])).
% 1.34/0.55  fof(f27,plain,(
% 1.34/0.55    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.34/0.55    inference(nnf_transformation,[],[f2])).
% 1.34/0.55  fof(f2,axiom,(
% 1.34/0.55    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.34/0.55  fof(f104,plain,(
% 1.34/0.55    r2_hidden(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl14_1),
% 1.34/0.55    inference(avatar_component_clause,[],[f102])).
% 1.34/0.55  fof(f102,plain,(
% 1.34/0.55    spl14_1 <=> r2_hidden(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.34/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 1.34/0.55  fof(f513,plain,(
% 1.34/0.55    r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK5(sK0,sK1,sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK9(k5_relat_1(sK0,sK1),sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))))),sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~spl14_1),
% 1.34/0.55    inference(resolution,[],[f505,f80])).
% 1.34/0.55  fof(f80,plain,(
% 1.34/0.55    ( ! [X0,X8,X7,X1] : (~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.34/0.55    inference(subsumption_resolution,[],[f63,f43])).
% 1.34/0.55  fof(f43,plain,(
% 1.34/0.55    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f11])).
% 1.34/0.55  fof(f11,plain,(
% 1.34/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.34/0.55    inference(flattening,[],[f10])).
% 1.34/0.55  fof(f10,plain,(
% 1.34/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.34/0.55    inference(ennf_transformation,[],[f5])).
% 1.34/0.55  fof(f5,axiom,(
% 1.34/0.55    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.34/0.55  fof(f63,plain,(
% 1.34/0.55    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.34/0.55    inference(equality_resolution,[],[f44])).
% 1.34/0.55  fof(f44,plain,(
% 1.34/0.55    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f22])).
% 1.34/0.55  fof(f22,plain,(
% 1.34/0.55    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.34/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f21,f20,f19])).
% 1.34/0.55  fof(f19,plain,(
% 1.34/0.55    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f20,plain,(
% 1.34/0.55    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f21,plain,(
% 1.34/0.55    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f18,plain,(
% 1.34/0.55    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.34/0.55    inference(rectify,[],[f17])).
% 1.34/0.55  fof(f17,plain,(
% 1.34/0.55    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.34/0.55    inference(nnf_transformation,[],[f12])).
% 1.34/0.55  % (22954)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.55  fof(f12,plain,(
% 1.34/0.55    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.34/0.55    inference(ennf_transformation,[],[f4])).
% 1.34/0.55  fof(f4,axiom,(
% 1.34/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 1.34/0.55  fof(f505,plain,(
% 1.34/0.55    r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK9(k5_relat_1(sK0,sK1),sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))))),k5_relat_1(sK0,sK1)) | ~spl14_1),
% 1.34/0.55    inference(resolution,[],[f104,f65])).
% 1.34/0.55  fof(f65,plain,(
% 1.34/0.55    ( ! [X0,X5] : (~r2_hidden(X5,k1_relat_1(X0)) | r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)) )),
% 1.34/0.55    inference(equality_resolution,[],[f53])).
% 1.34/0.55  fof(f53,plain,(
% 1.34/0.55    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 1.34/0.55    inference(cnf_transformation,[],[f32])).
% 1.34/0.55  fof(f504,plain,(
% 1.34/0.55    ~spl14_2),
% 1.34/0.55    inference(avatar_contradiction_clause,[],[f501])).
% 1.34/0.55  fof(f501,plain,(
% 1.34/0.55    $false | ~spl14_2),
% 1.34/0.55    inference(resolution,[],[f500,f108])).
% 1.34/0.55  fof(f108,plain,(
% 1.34/0.55    r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))),sK0) | ~spl14_2),
% 1.34/0.55    inference(avatar_component_clause,[],[f106])).
% 1.34/0.55  fof(f106,plain,(
% 1.34/0.55    spl14_2 <=> r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))),sK0)),
% 1.34/0.55    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 1.34/0.55  fof(f500,plain,(
% 1.34/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0),sK0)) ) | ~spl14_2),
% 1.34/0.55    inference(subsumption_resolution,[],[f498,f69])).
% 1.34/0.55  fof(f498,plain,(
% 1.34/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0),sK0) | sQ13_eqProxy(k1_relat_1(sK0),k1_relat_1(k5_relat_1(sK0,sK1)))) ) | ~spl14_2),
% 1.34/0.55    inference(resolution,[],[f486,f73])).
% 1.34/0.55  fof(f486,plain,(
% 1.34/0.55    r2_hidden(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl14_2),
% 1.34/0.55    inference(resolution,[],[f474,f64])).
% 1.34/0.55  fof(f64,plain,(
% 1.34/0.55    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 1.34/0.55    inference(equality_resolution,[],[f54])).
% 1.34/0.55  fof(f54,plain,(
% 1.34/0.55    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.34/0.55    inference(cnf_transformation,[],[f32])).
% 1.34/0.55  fof(f474,plain,(
% 1.34/0.55    r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK9(sK1,sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))))),k5_relat_1(sK0,sK1)) | ~spl14_2),
% 1.34/0.55    inference(resolution,[],[f181,f108])).
% 1.34/0.55  fof(f181,plain,(
% 1.34/0.55    ( ! [X2] : (~r2_hidden(k4_tarski(X2,sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))),sK0) | r2_hidden(k4_tarski(X2,sK9(sK1,sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))))),k5_relat_1(sK0,sK1))) ) | ~spl14_2),
% 1.34/0.55    inference(resolution,[],[f173,f119])).
% 1.34/0.55  fof(f119,plain,(
% 1.34/0.55    r2_hidden(k4_tarski(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK9(sK1,sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))))),sK1) | ~spl14_2),
% 1.34/0.55    inference(resolution,[],[f117,f65])).
% 1.34/0.55  fof(f117,plain,(
% 1.34/0.55    r2_hidden(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) | ~spl14_2),
% 1.34/0.55    inference(resolution,[],[f114,f41])).
% 1.34/0.55  fof(f41,plain,(
% 1.34/0.55    r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))),
% 1.34/0.55    inference(cnf_transformation,[],[f16])).
% 1.34/0.55  fof(f114,plain,(
% 1.34/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | r2_hidden(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),X0)) ) | ~spl14_2),
% 1.34/0.55    inference(resolution,[],[f111,f50])).
% 1.34/0.55  fof(f50,plain,(
% 1.34/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f26])).
% 1.34/0.55  fof(f26,plain,(
% 1.34/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).
% 1.34/0.55  fof(f25,plain,(
% 1.34/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f24,plain,(
% 1.34/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.55    inference(rectify,[],[f23])).
% 1.34/0.55  fof(f23,plain,(
% 1.34/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.55    inference(nnf_transformation,[],[f13])).
% 1.34/0.55  fof(f13,plain,(
% 1.34/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.34/0.55    inference(ennf_transformation,[],[f1])).
% 1.34/0.55  fof(f1,axiom,(
% 1.34/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.34/0.55  fof(f111,plain,(
% 1.34/0.55    r2_hidden(sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k2_relat_1(sK0)) | ~spl14_2),
% 1.34/0.55    inference(resolution,[],[f108,f66])).
% 1.34/0.55  fof(f66,plain,(
% 1.34/0.55    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 1.34/0.55    inference(equality_resolution,[],[f58])).
% 1.34/0.55  fof(f58,plain,(
% 1.34/0.55    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 1.34/0.55    inference(cnf_transformation,[],[f38])).
% 1.34/0.55  fof(f38,plain,(
% 1.34/0.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK10(X0,X1)),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (r2_hidden(k4_tarski(sK11(X0,X1),sK10(X0,X1)),X0) | r2_hidden(sK10(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK12(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.34/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f34,f37,f36,f35])).
% 1.34/0.55  fof(f35,plain,(
% 1.34/0.55    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK10(X0,X1)),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK10(X0,X1)),X0) | r2_hidden(sK10(X0,X1),X1))))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f36,plain,(
% 1.34/0.55    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK10(X0,X1)),X0) => r2_hidden(k4_tarski(sK11(X0,X1),sK10(X0,X1)),X0))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f37,plain,(
% 1.34/0.55    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK12(X0,X5),X5),X0))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f34,plain,(
% 1.34/0.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.34/0.55    inference(rectify,[],[f33])).
% 1.34/0.55  fof(f33,plain,(
% 1.34/0.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.34/0.55    inference(nnf_transformation,[],[f3])).
% 1.34/0.55  fof(f3,axiom,(
% 1.34/0.55    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.34/0.55  fof(f173,plain,(
% 1.34/0.55    ( ! [X4,X5,X3] : (~r2_hidden(k4_tarski(X4,X5),sK1) | ~r2_hidden(k4_tarski(X3,X4),sK0) | r2_hidden(k4_tarski(X3,X5),k5_relat_1(sK0,sK1))) )),
% 1.34/0.55    inference(resolution,[],[f146,f40])).
% 1.34/0.55  fof(f146,plain,(
% 1.34/0.55    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X3,X0),sK0) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(k4_tarski(X3,X1),k5_relat_1(sK0,X2))) )),
% 1.34/0.55    inference(resolution,[],[f78,f39])).
% 1.34/0.55  fof(f78,plain,(
% 1.34/0.55    ( ! [X0,X8,X7,X1,X9] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))) )),
% 1.34/0.55    inference(subsumption_resolution,[],[f61,f43])).
% 1.34/0.55  fof(f61,plain,(
% 1.34/0.55    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.34/0.55    inference(equality_resolution,[],[f46])).
% 1.34/0.55  fof(f46,plain,(
% 1.34/0.55    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f22])).
% 1.34/0.55  fof(f109,plain,(
% 1.34/0.55    spl14_1 | spl14_2),
% 1.34/0.55    inference(avatar_split_clause,[],[f100,f106,f102])).
% 1.34/0.55  fof(f100,plain,(
% 1.34/0.55    r2_hidden(k4_tarski(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),sK8(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))),sK0) | r2_hidden(sK7(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.34/0.55    inference(resolution,[],[f74,f69])).
% 1.34/0.55  fof(f74,plain,(
% 1.34/0.55    ( ! [X0,X1] : (sQ13_eqProxy(k1_relat_1(X0),X1) | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)) )),
% 1.34/0.55    inference(equality_proxy_replacement,[],[f55,f68])).
% 1.34/0.55  fof(f55,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f32])).
% 1.34/0.55  % SZS output end Proof for theBenchmark
% 1.34/0.55  % (22955)------------------------------
% 1.34/0.55  % (22955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (22955)Termination reason: Refutation
% 1.34/0.55  
% 1.34/0.55  % (22955)Memory used [KB]: 11385
% 1.34/0.55  % (22955)Time elapsed: 0.128 s
% 1.34/0.55  % (22955)------------------------------
% 1.34/0.55  % (22955)------------------------------
% 1.34/0.55  % (22967)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.55  % (22965)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.55  % (22936)Success in time 0.189 s
%------------------------------------------------------------------------------
