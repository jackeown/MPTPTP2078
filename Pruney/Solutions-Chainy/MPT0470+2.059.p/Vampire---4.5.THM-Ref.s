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
% DateTime   : Thu Dec  3 12:47:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 277 expanded)
%              Number of leaves         :   18 (  76 expanded)
%              Depth                    :   21
%              Number of atoms          :  417 (1475 expanded)
%              Number of equality atoms :   66 ( 245 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (12141)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (12150)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (12137)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (12150)Refutation not found, incomplete strategy% (12150)------------------------------
% (12150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12150)Termination reason: Refutation not found, incomplete strategy

% (12150)Memory used [KB]: 10618
% (12150)Time elapsed: 0.080 s
% (12150)------------------------------
% (12150)------------------------------
fof(f555,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f165,f195,f542,f554])).

fof(f554,plain,
    ( spl8_2
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f553])).

fof(f553,plain,
    ( $false
    | spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f552,f32])).

fof(f32,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f552,plain,
    ( ~ v1_relat_1(sK0)
    | spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f550,f64])).

fof(f64,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f36,f34])).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f550,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f545,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f545,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f544,f32])).

fof(f544,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl8_2
    | ~ spl8_4 ),
    inference(trivial_inequality_removal,[],[f543])).

fof(f543,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl8_2
    | ~ spl8_4 ),
    inference(superposition,[],[f62,f264])).

fof(f264,plain,
    ( ! [X4] :
        ( k1_xboole_0 = k5_relat_1(X4,k1_xboole_0)
        | ~ v1_relat_1(X4)
        | ~ v1_relat_1(k5_relat_1(X4,k1_xboole_0)) )
    | ~ spl8_4 ),
    inference(resolution,[],[f212,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f13,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(f212,plain,
    ( ! [X2,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,k1_xboole_0))
        | ~ v1_relat_1(X1) )
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f211,f64])).

fof(f211,plain,
    ( ! [X2,X3,X1] :
        ( ~ v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,k1_xboole_0)) )
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f204,f164])).

fof(f164,plain,
    ( ! [X7] : ~ r2_hidden(X7,k1_xboole_0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl8_4
  <=> ! [X7] : ~ r2_hidden(X7,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f204,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k4_tarski(sK6(X1,k1_xboole_0,X2,X3),X3),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,k1_xboole_0)) ) ),
    inference(superposition,[],[f101,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK6(X2,k4_xboole_0(X3,X4),X0,X1),X1),X3)
      | ~ v1_relat_1(k4_xboole_0(X3,X4))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,k4_xboole_0(X3,X4))) ) ),
    inference(subsumption_resolution,[],[f98,f44])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,k4_xboole_0(X3,X4)))
      | ~ v1_relat_1(k5_relat_1(X2,k4_xboole_0(X3,X4)))
      | ~ v1_relat_1(k4_xboole_0(X3,X4))
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK6(X2,k4_xboole_0(X3,X4),X0,X1),X1),X3) ) ),
    inference(resolution,[],[f52,f56])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f52,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f22,f25,f24,f23])).

fof(f23,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f62,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl8_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f542,plain,
    ( spl8_1
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f541])).

fof(f541,plain,
    ( $false
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f540,f64])).

fof(f540,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f538,f32])).

fof(f538,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f520,f44])).

fof(f520,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f519,f32])).

fof(f519,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl8_1
    | ~ spl8_4 ),
    inference(trivial_inequality_removal,[],[f508])).

fof(f508,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl8_1
    | ~ spl8_4 ),
    inference(superposition,[],[f59,f298])).

fof(f298,plain,
    ( ! [X4] :
        ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X4)
        | ~ v1_relat_1(X4)
        | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X4)) )
    | ~ spl8_4 ),
    inference(resolution,[],[f251,f37])).

fof(f251,plain,
    ( ! [X14,X12,X15] :
        ( ~ r2_hidden(k4_tarski(X14,X15),k5_relat_1(k1_xboole_0,X12))
        | ~ v1_relat_1(X12) )
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f250,f35])).

fof(f250,plain,
    ( ! [X14,X12,X15,X13] :
        ( ~ v1_relat_1(X12)
        | ~ r2_hidden(k4_tarski(X14,X15),k5_relat_1(k4_xboole_0(k1_xboole_0,X13),X12)) )
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f249,f64])).

fof(f249,plain,
    ( ! [X14,X12,X15,X13] :
        ( ~ v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(X12)
        | ~ r2_hidden(k4_tarski(X14,X15),k5_relat_1(k4_xboole_0(k1_xboole_0,X13),X12)) )
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f244,f35])).

fof(f244,plain,
    ( ! [X14,X12,X15,X13] :
        ( ~ v1_relat_1(X12)
        | ~ v1_relat_1(k4_xboole_0(k1_xboole_0,X13))
        | ~ r2_hidden(k4_tarski(X14,X15),k5_relat_1(k4_xboole_0(k1_xboole_0,X13),X12)) )
    | ~ spl8_4 ),
    inference(resolution,[],[f107,f164])).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,sK6(k4_xboole_0(X2,X3),X4,X0,X1)),X2)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k4_xboole_0(X2,X3))
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k4_xboole_0(X2,X3),X4)) ) ),
    inference(subsumption_resolution,[],[f104,f44])).

fof(f104,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k4_xboole_0(X2,X3),X4))
      | ~ v1_relat_1(k5_relat_1(k4_xboole_0(X2,X3),X4))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k4_xboole_0(X2,X3))
      | r2_hidden(k4_tarski(X0,sK6(k4_xboole_0(X2,X3),X4,X0,X1)),X2) ) ),
    inference(resolution,[],[f53,f56])).

fof(f53,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl8_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f195,plain,(
    ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f190,f64])).

fof(f190,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl8_3 ),
    inference(superposition,[],[f161,f115])).

fof(f115,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X1] :
      ( k4_xboole_0(X1,k1_xboole_0) = X1
      | k4_xboole_0(X1,k1_xboole_0) = X1 ) ),
    inference(resolution,[],[f95,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X2)
      | r2_hidden(sK7(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f95,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(sK7(X9,k1_xboole_0,X9),X10)
      | k4_xboole_0(X9,k1_xboole_0) = X9 ) ),
    inference(resolution,[],[f90,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f55,f35])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f90,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK7(X3,X4,X3),X4)
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(subsumption_resolution,[],[f88,f48])).

fof(f88,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK7(X3,X4,X3),X4)
      | ~ r2_hidden(sK7(X3,X4,X3),X3)
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK7(X3,X4,X3),X4)
      | ~ r2_hidden(sK7(X3,X4,X3),X3)
      | k4_xboole_0(X3,X4) = X3
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(resolution,[],[f50,f76])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X2)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(sK7(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f161,plain,
    ( ! [X6] : ~ v1_relat_1(k4_xboole_0(X6,X6))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl8_3
  <=> ! [X6] : ~ v1_relat_1(k4_xboole_0(X6,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f165,plain,
    ( spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f158,f163,f160])).

fof(f158,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,k1_xboole_0)
      | ~ v1_relat_1(k4_xboole_0(X6,X6)) ) ),
    inference(subsumption_resolution,[],[f156,f65])).

fof(f156,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,k1_xboole_0)
      | r2_hidden(X7,X6)
      | ~ v1_relat_1(k4_xboole_0(X6,X6)) ) ),
    inference(superposition,[],[f56,f150])).

fof(f150,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | ~ v1_relat_1(k4_xboole_0(X0,X0)) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k4_xboole_0(X0,X0))
      | k1_xboole_0 = k4_xboole_0(X0,X0)
      | ~ v1_relat_1(k4_xboole_0(X0,X0))
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f71,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(k4_xboole_0(X0,X1)),sK2(k4_xboole_0(X0,X1))),X0)
      | ~ v1_relat_1(k4_xboole_0(X0,X1))
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f37,f56])).

fof(f71,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(sK1(k4_xboole_0(X2,X3)),sK2(k4_xboole_0(X2,X3))),X3)
      | ~ v1_relat_1(k4_xboole_0(X2,X3))
      | k1_xboole_0 = k4_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f37,f55])).

fof(f63,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f33,f61,f58])).

fof(f33,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n009.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 15:08:41 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.47  % (12130)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (12130)Refutation not found, incomplete strategy% (12130)------------------------------
% 0.21/0.47  % (12130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (12147)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.47  % (12130)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (12130)Memory used [KB]: 10618
% 0.21/0.47  % (12130)Time elapsed: 0.060 s
% 0.21/0.47  % (12130)------------------------------
% 0.21/0.47  % (12130)------------------------------
% 0.21/0.48  % (12132)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (12134)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (12142)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (12135)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (12132)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (12140)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (12143)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (12136)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (12145)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (12133)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (12133)Refutation not found, incomplete strategy% (12133)------------------------------
% 0.21/0.50  % (12133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12133)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12133)Memory used [KB]: 10618
% 0.21/0.50  % (12133)Time elapsed: 0.079 s
% 0.21/0.50  % (12133)------------------------------
% 0.21/0.50  % (12133)------------------------------
% 0.21/0.50  % (12149)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (12129)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  % (12141)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (12150)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (12137)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (12150)Refutation not found, incomplete strategy% (12150)------------------------------
% 0.21/0.51  % (12150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12150)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12150)Memory used [KB]: 10618
% 0.21/0.51  % (12150)Time elapsed: 0.080 s
% 0.21/0.51  % (12150)------------------------------
% 0.21/0.51  % (12150)------------------------------
% 0.21/0.51  fof(f555,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f63,f165,f195,f542,f554])).
% 0.21/0.51  fof(f554,plain,(
% 0.21/0.51    spl8_2 | ~spl8_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f553])).
% 0.21/0.51  fof(f553,plain,(
% 0.21/0.51    $false | (spl8_2 | ~spl8_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f552,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    v1_relat_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.51    inference(negated_conjecture,[],[f8])).
% 0.21/0.51  fof(f8,conjecture,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.21/0.51  fof(f552,plain,(
% 0.21/0.51    ~v1_relat_1(sK0) | (spl8_2 | ~spl8_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f550,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    v1_relat_1(k1_xboole_0)),
% 0.21/0.51    inference(resolution,[],[f36,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.51  fof(f550,plain,(
% 0.21/0.51    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | (spl8_2 | ~spl8_4)),
% 0.21/0.51    inference(resolution,[],[f545,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.51  fof(f545,plain,(
% 0.21/0.51    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (spl8_2 | ~spl8_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f544,f32])).
% 0.21/0.51  fof(f544,plain,(
% 0.21/0.51    ~v1_relat_1(sK0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (spl8_2 | ~spl8_4)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f543])).
% 0.21/0.51  fof(f543,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (spl8_2 | ~spl8_4)),
% 0.21/0.51    inference(superposition,[],[f62,f264])).
% 0.21/0.51  fof(f264,plain,(
% 0.21/0.51    ( ! [X4] : (k1_xboole_0 = k5_relat_1(X4,k1_xboole_0) | ~v1_relat_1(X4) | ~v1_relat_1(k5_relat_1(X4,k1_xboole_0))) ) | ~spl8_4),
% 0.21/0.51    inference(resolution,[],[f212,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f13,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    ( ! [X2,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,k1_xboole_0)) | ~v1_relat_1(X1)) ) | ~spl8_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f211,f64])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    ( ! [X2,X3,X1] : (~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X1) | ~r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,k1_xboole_0))) ) | ~spl8_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f204,f164])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ( ! [X7] : (~r2_hidden(X7,k1_xboole_0)) ) | ~spl8_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f163])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    spl8_4 <=> ! [X7] : ~r2_hidden(X7,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    ( ! [X2,X3,X1] : (r2_hidden(k4_tarski(sK6(X1,k1_xboole_0,X2,X3),X3),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X1) | ~r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,k1_xboole_0))) )),
% 0.21/0.51    inference(superposition,[],[f101,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK6(X2,k4_xboole_0(X3,X4),X0,X1),X1),X3) | ~v1_relat_1(k4_xboole_0(X3,X4)) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,k4_xboole_0(X3,X4)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f98,f44])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,k4_xboole_0(X3,X4))) | ~v1_relat_1(k5_relat_1(X2,k4_xboole_0(X3,X4))) | ~v1_relat_1(k4_xboole_0(X3,X4)) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK6(X2,k4_xboole_0(X3,X4),X0,X1),X1),X3)) )),
% 0.21/0.51    inference(resolution,[],[f52,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((~r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.51    inference(rectify,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f22,f25,f24,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(rectify,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl8_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl8_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.51  fof(f542,plain,(
% 0.21/0.51    spl8_1 | ~spl8_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f541])).
% 0.21/0.51  fof(f541,plain,(
% 0.21/0.51    $false | (spl8_1 | ~spl8_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f540,f64])).
% 0.21/0.51  fof(f540,plain,(
% 0.21/0.51    ~v1_relat_1(k1_xboole_0) | (spl8_1 | ~spl8_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f538,f32])).
% 0.21/0.51  fof(f538,plain,(
% 0.21/0.51    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | (spl8_1 | ~spl8_4)),
% 0.21/0.51    inference(resolution,[],[f520,f44])).
% 0.21/0.51  fof(f520,plain,(
% 0.21/0.51    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (spl8_1 | ~spl8_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f519,f32])).
% 0.21/0.51  fof(f519,plain,(
% 0.21/0.51    ~v1_relat_1(sK0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (spl8_1 | ~spl8_4)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f508])).
% 0.21/0.51  fof(f508,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (spl8_1 | ~spl8_4)),
% 0.21/0.51    inference(superposition,[],[f59,f298])).
% 0.21/0.51  fof(f298,plain,(
% 0.21/0.51    ( ! [X4] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X4) | ~v1_relat_1(X4) | ~v1_relat_1(k5_relat_1(k1_xboole_0,X4))) ) | ~spl8_4),
% 0.21/0.51    inference(resolution,[],[f251,f37])).
% 0.21/0.51  fof(f251,plain,(
% 0.21/0.51    ( ! [X14,X12,X15] : (~r2_hidden(k4_tarski(X14,X15),k5_relat_1(k1_xboole_0,X12)) | ~v1_relat_1(X12)) ) | ~spl8_4),
% 0.21/0.51    inference(forward_demodulation,[],[f250,f35])).
% 0.21/0.51  fof(f250,plain,(
% 0.21/0.51    ( ! [X14,X12,X15,X13] : (~v1_relat_1(X12) | ~r2_hidden(k4_tarski(X14,X15),k5_relat_1(k4_xboole_0(k1_xboole_0,X13),X12))) ) | ~spl8_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f249,f64])).
% 0.21/0.51  fof(f249,plain,(
% 0.21/0.51    ( ! [X14,X12,X15,X13] : (~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X12) | ~r2_hidden(k4_tarski(X14,X15),k5_relat_1(k4_xboole_0(k1_xboole_0,X13),X12))) ) | ~spl8_4),
% 0.21/0.51    inference(forward_demodulation,[],[f244,f35])).
% 0.21/0.51  fof(f244,plain,(
% 0.21/0.51    ( ! [X14,X12,X15,X13] : (~v1_relat_1(X12) | ~v1_relat_1(k4_xboole_0(k1_xboole_0,X13)) | ~r2_hidden(k4_tarski(X14,X15),k5_relat_1(k4_xboole_0(k1_xboole_0,X13),X12))) ) | ~spl8_4),
% 0.21/0.51    inference(resolution,[],[f107,f164])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,sK6(k4_xboole_0(X2,X3),X4,X0,X1)),X2) | ~v1_relat_1(X4) | ~v1_relat_1(k4_xboole_0(X2,X3)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k4_xboole_0(X2,X3),X4))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f104,f44])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k4_xboole_0(X2,X3),X4)) | ~v1_relat_1(k5_relat_1(k4_xboole_0(X2,X3),X4)) | ~v1_relat_1(X4) | ~v1_relat_1(k4_xboole_0(X2,X3)) | r2_hidden(k4_tarski(X0,sK6(k4_xboole_0(X2,X3),X4,X0,X1)),X2)) )),
% 0.21/0.51    inference(resolution,[],[f53,f56])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl8_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    spl8_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    ~spl8_3),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f194])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    $false | ~spl8_3),
% 0.21/0.51    inference(subsumption_resolution,[],[f190,f64])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    ~v1_relat_1(k1_xboole_0) | ~spl8_3),
% 0.21/0.51    inference(superposition,[],[f161,f115])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1 | k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.21/0.51    inference(resolution,[],[f95,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.51    inference(factoring,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X2) | r2_hidden(sK7(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X10,X9] : (~r2_hidden(sK7(X9,k1_xboole_0,X9),X10) | k4_xboole_0(X9,k1_xboole_0) = X9) )),
% 0.21/0.51    inference(resolution,[],[f90,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.51    inference(superposition,[],[f55,f35])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ( ! [X4,X3] : (r2_hidden(sK7(X3,X4,X3),X4) | k4_xboole_0(X3,X4) = X3) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f88,f48])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X4,X3] : (r2_hidden(sK7(X3,X4,X3),X4) | ~r2_hidden(sK7(X3,X4,X3),X3) | k4_xboole_0(X3,X4) = X3) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f86])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X4,X3] : (r2_hidden(sK7(X3,X4,X3),X4) | ~r2_hidden(sK7(X3,X4,X3),X3) | k4_xboole_0(X3,X4) = X3 | k4_xboole_0(X3,X4) = X3) )),
% 0.21/0.51    inference(resolution,[],[f50,f76])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK7(X0,X1,X2),X2) | r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    ( ! [X6] : (~v1_relat_1(k4_xboole_0(X6,X6))) ) | ~spl8_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f160])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    spl8_3 <=> ! [X6] : ~v1_relat_1(k4_xboole_0(X6,X6))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    spl8_3 | spl8_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f158,f163,f160])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    ( ! [X6,X7] : (~r2_hidden(X7,k1_xboole_0) | ~v1_relat_1(k4_xboole_0(X6,X6))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f156,f65])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    ( ! [X6,X7] : (~r2_hidden(X7,k1_xboole_0) | r2_hidden(X7,X6) | ~v1_relat_1(k4_xboole_0(X6,X6))) )),
% 0.21/0.51    inference(superposition,[],[f56,f150])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | ~v1_relat_1(k4_xboole_0(X0,X0))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f145])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(k4_xboole_0(X0,X0)) | k1_xboole_0 = k4_xboole_0(X0,X0) | ~v1_relat_1(k4_xboole_0(X0,X0)) | k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.51    inference(resolution,[],[f71,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK1(k4_xboole_0(X0,X1)),sK2(k4_xboole_0(X0,X1))),X0) | ~v1_relat_1(k4_xboole_0(X0,X1)) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.51    inference(resolution,[],[f37,f56])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r2_hidden(k4_tarski(sK1(k4_xboole_0(X2,X3)),sK2(k4_xboole_0(X2,X3))),X3) | ~v1_relat_1(k4_xboole_0(X2,X3)) | k1_xboole_0 = k4_xboole_0(X2,X3)) )),
% 0.21/0.51    inference(resolution,[],[f37,f55])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ~spl8_1 | ~spl8_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f61,f58])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (12132)------------------------------
% 0.21/0.51  % (12132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12132)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (12132)Memory used [KB]: 11129
% 0.21/0.51  % (12132)Time elapsed: 0.073 s
% 0.21/0.51  % (12132)------------------------------
% 0.21/0.51  % (12132)------------------------------
% 0.21/0.51  % (12146)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (12126)Success in time 0.154 s
%------------------------------------------------------------------------------
