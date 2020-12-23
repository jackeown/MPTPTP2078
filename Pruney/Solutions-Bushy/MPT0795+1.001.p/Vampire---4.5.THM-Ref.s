%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0795+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 450 expanded)
%              Number of leaves         :   11 ( 122 expanded)
%              Depth                    :   31
%              Number of atoms          :  446 (2234 expanded)
%              Number of equality atoms :   77 ( 333 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f195,plain,(
    $false ),
    inference(resolution,[],[f187,f28])).

fof(f28,plain,(
    ~ r3_wellord1(sK2,sK2,k6_relat_1(k3_relat_1(sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r3_wellord1(sK2,sK2,k6_relat_1(k3_relat_1(sK2)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ~ r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))
        & v1_relat_1(X0) )
   => ( ~ r3_wellord1(sK2,sK2,k6_relat_1(k3_relat_1(sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ~ r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_wellord1)).

fof(f187,plain,(
    r3_wellord1(sK2,sK2,k6_relat_1(k3_relat_1(sK2))) ),
    inference(resolution,[],[f186,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ sP0(sK2,k6_relat_1(X0),sK2)
      | r3_wellord1(sK2,sK2,k6_relat_1(X0)) ) ),
    inference(resolution,[],[f56,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r3_wellord1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_wellord1(X0,X2,X1)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r3_wellord1(X0,X2,X1) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X2,X1] :
      ( ( ( r3_wellord1(X0,X1,X2)
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r3_wellord1(X0,X1,X2) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X2,X1] :
      ( ( r3_wellord1(X0,X1,X2)
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f56,plain,(
    ! [X0] : sP1(sK2,k6_relat_1(X0),sK2) ),
    inference(resolution,[],[f54,f27])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | sP1(sK2,k6_relat_1(X1),X0) ) ),
    inference(resolution,[],[f53,f27])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | sP1(X0,k6_relat_1(X1),X2) ) ),
    inference(resolution,[],[f52,f29])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X1))
      | sP1(X0,k6_relat_1(X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f48,f32])).

fof(f32,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | sP1(X0,X2,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f11,f16,f15])).

fof(f15,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ( ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X0)
          <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              & r2_hidden(X4,k3_relat_1(X0))
              & r2_hidden(X3,k3_relat_1(X0)) ) )
        & v2_funct_1(X2)
        & k2_relat_1(X2) = k3_relat_1(X1)
        & k1_relat_1(X2) = k3_relat_1(X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_wellord1)).

fof(f186,plain,(
    sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2) ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,
    ( sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)
    | sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2) ),
    inference(resolution,[],[f178,f168])).

fof(f168,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),sK2)
    | sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),sK2)
    | r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),sK2)
    | sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2) ),
    inference(forward_demodulation,[],[f165,f146])).

fof(f146,plain,(
    sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2) = k1_funct_1(k6_relat_1(k3_relat_1(sK2)),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)) ),
    inference(resolution,[],[f139,f28])).

fof(f139,plain,
    ( r3_wellord1(sK2,sK2,k6_relat_1(k3_relat_1(sK2)))
    | sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2) = k1_funct_1(k6_relat_1(k3_relat_1(sK2)),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)) ),
    inference(resolution,[],[f130,f58])).

fof(f130,plain,
    ( sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)
    | sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2) = k1_funct_1(k6_relat_1(k3_relat_1(sK2)),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)) ),
    inference(resolution,[],[f126,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

fof(f126,plain,
    ( r2_hidden(sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),k3_relat_1(sK2))
    | sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2) ),
    inference(resolution,[],[f124,f27])).

fof(f124,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | sP0(X9,k6_relat_1(k3_relat_1(X9)),X9)
      | r2_hidden(sK4(X9,k6_relat_1(k3_relat_1(X9)),X9),k3_relat_1(X9)) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X9] :
      ( r2_hidden(sK4(X9,k6_relat_1(k3_relat_1(X9)),X9),k3_relat_1(X9))
      | sP0(X9,k6_relat_1(k3_relat_1(X9)),X9)
      | r2_hidden(sK4(X9,k6_relat_1(k3_relat_1(X9)),X9),k3_relat_1(X9))
      | ~ v1_relat_1(X9) ) ),
    inference(resolution,[],[f116,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f116,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK3(X0,k6_relat_1(k3_relat_1(X0)),X0),sK4(X0,k6_relat_1(k3_relat_1(X0)),X0)),X0)
      | r2_hidden(sK4(X0,k6_relat_1(k3_relat_1(X0)),X0),k3_relat_1(X0))
      | sP0(X0,k6_relat_1(k3_relat_1(X0)),X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X0) != k3_relat_1(X1)
      | r2_hidden(sK4(X1,k6_relat_1(k3_relat_1(X1)),X0),k3_relat_1(X0))
      | r2_hidden(k4_tarski(sK3(X1,k6_relat_1(k3_relat_1(X1)),X0),sK4(X1,k6_relat_1(k3_relat_1(X1)),X0)),X0)
      | sP0(X1,k6_relat_1(k3_relat_1(X1)),X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k3_relat_1(X0) != X1
      | k3_relat_1(X2) != X1
      | r2_hidden(sK4(X0,k6_relat_1(X1),X2),k3_relat_1(X2))
      | r2_hidden(k4_tarski(sK3(X0,k6_relat_1(X1),X2),sK4(X0,k6_relat_1(X1),X2)),X2)
      | sP0(X0,k6_relat_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f72,f33])).

fof(f33,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k3_relat_1(X0) != X1
      | r2_hidden(sK4(X0,k6_relat_1(X1),X2),k3_relat_1(X2))
      | r2_hidden(k4_tarski(sK3(X0,k6_relat_1(X1),X2),sK4(X0,k6_relat_1(X1),X2)),X2)
      | sP0(X0,k6_relat_1(X1),X2)
      | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f71,f34])).

fof(f34,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,k6_relat_1(X1),X2),k3_relat_1(X2))
      | r2_hidden(k4_tarski(sK3(X0,k6_relat_1(X1),X2),sK4(X0,k6_relat_1(X1),X2)),X2)
      | sP0(X0,k6_relat_1(X1),X2)
      | k3_relat_1(X0) != k2_relat_1(k6_relat_1(X1))
      | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X1)) ) ),
    inference(resolution,[],[f45,f30])).

fof(f30,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X1)
      | r2_hidden(sK4(X0,X1,X2),k3_relat_1(X2))
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | sP0(X0,X1,X2)
      | k3_relat_1(X0) != k2_relat_1(X1)
      | k3_relat_1(X2) != k1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

% (14456)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% (14456)Refutation not found, incomplete strategy% (14456)------------------------------
% (14456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14456)Termination reason: Refutation not found, incomplete strategy

% (14456)Memory used [KB]: 10618
% (14456)Time elapsed: 0.154 s
% (14456)------------------------------
% (14456)------------------------------
fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,sK3(X0,X1,X2)),k1_funct_1(X1,sK4(X0,X1,X2))),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),k3_relat_1(X2))
            | ~ r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
            | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
          & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,sK3(X0,X1,X2)),k1_funct_1(X1,sK4(X0,X1,X2))),X0)
              & r2_hidden(sK4(X0,X1,X2),k3_relat_1(X2))
              & r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2)) )
            | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) )
        | ~ v2_funct_1(X1)
        | k3_relat_1(X0) != k2_relat_1(X1)
        | k3_relat_1(X2) != k1_relat_1(X1) )
      & ( ( ! [X5,X6] :
              ( ( r2_hidden(k4_tarski(X5,X6),X2)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                | ~ r2_hidden(X6,k3_relat_1(X2))
                | ~ r2_hidden(X5,k3_relat_1(X2)) )
              & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                  & r2_hidden(X6,k3_relat_1(X2))
                  & r2_hidden(X5,k3_relat_1(X2)) )
                | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
          & v2_funct_1(X1)
          & k3_relat_1(X0) = k2_relat_1(X1)
          & k3_relat_1(X2) = k1_relat_1(X1) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
            | ~ r2_hidden(X4,k3_relat_1(X2))
            | ~ r2_hidden(X3,k3_relat_1(X2))
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
              & r2_hidden(X4,k3_relat_1(X2))
              & r2_hidden(X3,k3_relat_1(X2)) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,sK3(X0,X1,X2)),k1_funct_1(X1,sK4(X0,X1,X2))),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),k3_relat_1(X2))
          | ~ r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,sK3(X0,X1,X2)),k1_funct_1(X1,sK4(X0,X1,X2))),X0)
            & r2_hidden(sK4(X0,X1,X2),k3_relat_1(X2))
            & r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2)) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
              | ~ r2_hidden(X4,k3_relat_1(X2))
              | ~ r2_hidden(X3,k3_relat_1(X2))
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
                & r2_hidden(X4,k3_relat_1(X2))
                & r2_hidden(X3,k3_relat_1(X2)) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) )
        | ~ v2_funct_1(X1)
        | k3_relat_1(X0) != k2_relat_1(X1)
        | k3_relat_1(X2) != k1_relat_1(X1) )
      & ( ( ! [X5,X6] :
              ( ( r2_hidden(k4_tarski(X5,X6),X2)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                | ~ r2_hidden(X6,k3_relat_1(X2))
                | ~ r2_hidden(X5,k3_relat_1(X2)) )
              & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                  & r2_hidden(X6,k3_relat_1(X2))
                  & r2_hidden(X5,k3_relat_1(X2)) )
                | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
          & v2_funct_1(X1)
          & k3_relat_1(X0) = k2_relat_1(X1)
          & k3_relat_1(X2) = k1_relat_1(X1) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f23])).

% (14467)Refutation not found, incomplete strategy% (14467)------------------------------
% (14467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14467)Termination reason: Refutation not found, incomplete strategy

% (14467)Memory used [KB]: 6780
% (14467)Time elapsed: 0.156 s
% (14467)------------------------------
% (14467)------------------------------
% (14459)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% (14464)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% (14464)Refutation not found, incomplete strategy% (14464)------------------------------
% (14464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14464)Termination reason: Refutation not found, incomplete strategy

% (14464)Memory used [KB]: 1663
% (14464)Time elapsed: 0.163 s
% (14464)------------------------------
% (14464)------------------------------
fof(f23,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0))
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                & r2_hidden(X4,k3_relat_1(X0))
                & r2_hidden(X3,k3_relat_1(X0)) )
              | r2_hidden(k4_tarski(X3,X4),X0) ) )
        | ~ v2_funct_1(X2)
        | k2_relat_1(X2) != k3_relat_1(X1)
        | k1_relat_1(X2) != k3_relat_1(X0) )
      & ( ( ! [X3,X4] :
              ( ( r2_hidden(k4_tarski(X3,X4),X0)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                | ~ r2_hidden(X4,k3_relat_1(X0))
                | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                  & r2_hidden(X4,k3_relat_1(X0))
                  & r2_hidden(X3,k3_relat_1(X0)) )
                | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
          & v2_funct_1(X2)
          & k2_relat_1(X2) = k3_relat_1(X1)
          & k1_relat_1(X2) = k3_relat_1(X0) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0))
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                & r2_hidden(X4,k3_relat_1(X0))
                & r2_hidden(X3,k3_relat_1(X0)) )
              | r2_hidden(k4_tarski(X3,X4),X0) ) )
        | ~ v2_funct_1(X2)
        | k2_relat_1(X2) != k3_relat_1(X1)
        | k1_relat_1(X2) != k3_relat_1(X0) )
      & ( ( ! [X3,X4] :
              ( ( r2_hidden(k4_tarski(X3,X4),X0)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                | ~ r2_hidden(X4,k3_relat_1(X0))
                | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                  & r2_hidden(X4,k3_relat_1(X0))
                  & r2_hidden(X3,k3_relat_1(X0)) )
                | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
          & v2_funct_1(X2)
          & k2_relat_1(X2) = k3_relat_1(X1)
          & k1_relat_1(X2) = k3_relat_1(X0) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f165,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),k1_funct_1(k6_relat_1(k3_relat_1(sK2)),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2))),sK2)
    | r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),sK2)
    | sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2) ),
    inference(superposition,[],[f137,f98])).

fof(f98,plain,(
    sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2) = k1_funct_1(k6_relat_1(k3_relat_1(sK2)),sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)) ),
    inference(resolution,[],[f93,f28])).

fof(f93,plain,
    ( r3_wellord1(sK2,sK2,k6_relat_1(k3_relat_1(sK2)))
    | sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2) = k1_funct_1(k6_relat_1(k3_relat_1(sK2)),sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)) ),
    inference(resolution,[],[f91,f58])).

fof(f91,plain,
    ( sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)
    | sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2) = k1_funct_1(k6_relat_1(k3_relat_1(sK2)),sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)) ),
    inference(resolution,[],[f87,f27])).

fof(f87,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | sP0(X4,k6_relat_1(k3_relat_1(X4)),X4)
      | sK3(X4,k6_relat_1(k3_relat_1(X4)),X4) = k1_funct_1(k6_relat_1(k3_relat_1(X4)),sK3(X4,k6_relat_1(k3_relat_1(X4)),X4)) ) ),
    inference(resolution,[],[f84,f49])).

fof(f84,plain,(
    ! [X10] :
      ( r2_hidden(sK3(X10,k6_relat_1(k3_relat_1(X10)),X10),k3_relat_1(X10))
      | sP0(X10,k6_relat_1(k3_relat_1(X10)),X10)
      | ~ v1_relat_1(X10) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X10] :
      ( r2_hidden(sK3(X10,k6_relat_1(k3_relat_1(X10)),X10),k3_relat_1(X10))
      | sP0(X10,k6_relat_1(k3_relat_1(X10)),X10)
      | r2_hidden(sK3(X10,k6_relat_1(k3_relat_1(X10)),X10),k3_relat_1(X10))
      | ~ v1_relat_1(X10) ) ),
    inference(resolution,[],[f76,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK3(X0,k6_relat_1(k3_relat_1(X0)),X0),sK4(X0,k6_relat_1(k3_relat_1(X0)),X0)),X0)
      | r2_hidden(sK3(X0,k6_relat_1(k3_relat_1(X0)),X0),k3_relat_1(X0))
      | sP0(X0,k6_relat_1(k3_relat_1(X0)),X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X0) != k3_relat_1(X1)
      | r2_hidden(sK3(X1,k6_relat_1(k3_relat_1(X1)),X0),k3_relat_1(X0))
      | r2_hidden(k4_tarski(sK3(X1,k6_relat_1(k3_relat_1(X1)),X0),sK4(X1,k6_relat_1(k3_relat_1(X1)),X0)),X0)
      | sP0(X1,k6_relat_1(k3_relat_1(X1)),X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k3_relat_1(X0) != X1
      | k3_relat_1(X2) != X1
      | r2_hidden(sK3(X0,k6_relat_1(X1),X2),k3_relat_1(X2))
      | r2_hidden(k4_tarski(sK3(X0,k6_relat_1(X1),X2),sK4(X0,k6_relat_1(X1),X2)),X2)
      | sP0(X0,k6_relat_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f69,f33])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k3_relat_1(X0) != X1
      | r2_hidden(sK3(X0,k6_relat_1(X1),X2),k3_relat_1(X2))
      | r2_hidden(k4_tarski(sK3(X0,k6_relat_1(X1),X2),sK4(X0,k6_relat_1(X1),X2)),X2)
      | sP0(X0,k6_relat_1(X1),X2)
      | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f68,f34])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,k6_relat_1(X1),X2),k3_relat_1(X2))
      | r2_hidden(k4_tarski(sK3(X0,k6_relat_1(X1),X2),sK4(X0,k6_relat_1(X1),X2)),X2)
      | sP0(X0,k6_relat_1(X1),X2)
      | k3_relat_1(X0) != k2_relat_1(k6_relat_1(X1))
      | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X1)) ) ),
    inference(resolution,[],[f44,f30])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X1)
      | r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | sP0(X0,X1,X2)
      | k3_relat_1(X0) != k2_relat_1(X1)
      | k3_relat_1(X2) != k1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f137,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X0)),sK3(X0,k6_relat_1(k3_relat_1(X0)),X0)),k1_funct_1(k6_relat_1(k3_relat_1(X0)),sK4(X0,k6_relat_1(k3_relat_1(X0)),X0))),X0)
      | r2_hidden(k4_tarski(sK3(X0,k6_relat_1(k3_relat_1(X0)),X0),sK4(X0,k6_relat_1(k3_relat_1(X0)),X0)),X0)
      | sP0(X0,k6_relat_1(k3_relat_1(X0)),X0) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X0) != k3_relat_1(X1)
      | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(X1)),sK3(X1,k6_relat_1(k3_relat_1(X1)),X0)),k1_funct_1(k6_relat_1(k3_relat_1(X1)),sK4(X1,k6_relat_1(k3_relat_1(X1)),X0))),X1)
      | r2_hidden(k4_tarski(sK3(X1,k6_relat_1(k3_relat_1(X1)),X0),sK4(X1,k6_relat_1(k3_relat_1(X1)),X0)),X0)
      | sP0(X1,k6_relat_1(k3_relat_1(X1)),X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k3_relat_1(X1) != X0
      | k3_relat_1(X2) != X0
      | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(X0),sK3(X1,k6_relat_1(X0),X2)),k1_funct_1(k6_relat_1(X0),sK4(X1,k6_relat_1(X0),X2))),X1)
      | r2_hidden(k4_tarski(sK3(X1,k6_relat_1(X0),X2),sK4(X1,k6_relat_1(X0),X2)),X2)
      | sP0(X1,k6_relat_1(X0),X2) ) ),
    inference(forward_demodulation,[],[f89,f33])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k3_relat_1(X1) != X0
      | r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(X0),sK3(X1,k6_relat_1(X0),X2)),k1_funct_1(k6_relat_1(X0),sK4(X1,k6_relat_1(X0),X2))),X1)
      | r2_hidden(k4_tarski(sK3(X1,k6_relat_1(X0),X2),sK4(X1,k6_relat_1(X0),X2)),X2)
      | sP0(X1,k6_relat_1(X0),X2)
      | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f88,f34])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(X0),sK3(X1,k6_relat_1(X0),X2)),k1_funct_1(k6_relat_1(X0),sK4(X1,k6_relat_1(X0),X2))),X1)
      | r2_hidden(k4_tarski(sK3(X1,k6_relat_1(X0),X2),sK4(X1,k6_relat_1(X0),X2)),X2)
      | sP0(X1,k6_relat_1(X0),X2)
      | k3_relat_1(X1) != k2_relat_1(k6_relat_1(X0))
      | k3_relat_1(X2) != k1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f46,f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X1)
      | r2_hidden(k4_tarski(k1_funct_1(X1,sK3(X0,X1,X2)),k1_funct_1(X1,sK4(X0,X1,X2))),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | sP0(X0,X1,X2)
      | k3_relat_1(X0) != k2_relat_1(X1)
      | k3_relat_1(X2) != k1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f178,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),sK2)
    | sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2) ),
    inference(resolution,[],[f177,f27])).

fof(f177,plain,
    ( ~ v1_relat_1(sK2)
    | sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)
    | ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),sK2) ),
    inference(resolution,[],[f176,f30])).

fof(f176,plain,
    ( ~ v2_funct_1(k6_relat_1(k3_relat_1(sK2)))
    | ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),sK2)
    | sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f175])).

fof(f175,plain,
    ( sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)
    | ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),sK2)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK2)))
    | sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f149,f84])).

fof(f149,plain,
    ( ~ r2_hidden(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),k3_relat_1(sK2))
    | sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)
    | ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),sK2)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK2))) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),sK2)
    | sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)
    | ~ r2_hidden(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),k3_relat_1(sK2))
    | ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),sK2)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f136,f146])).

fof(f136,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),k1_funct_1(k6_relat_1(k3_relat_1(sK2)),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2))),sK2)
    | sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)
    | ~ r2_hidden(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),k3_relat_1(sK2))
    | ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),sK2)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK2))) ),
    inference(trivial_inequality_removal,[],[f135])).

fof(f135,plain,
    ( k3_relat_1(sK2) != k3_relat_1(sK2)
    | ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),k1_funct_1(k6_relat_1(k3_relat_1(sK2)),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2))),sK2)
    | sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)
    | ~ r2_hidden(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),k3_relat_1(sK2))
    | ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),sK2)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f134,f33])).

fof(f134,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),k1_funct_1(k6_relat_1(k3_relat_1(sK2)),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2))),sK2)
    | sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)
    | ~ r2_hidden(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),k3_relat_1(sK2))
    | ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),sK2)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK2)))
    | k3_relat_1(sK2) != k1_relat_1(k6_relat_1(k3_relat_1(sK2))) ),
    inference(trivial_inequality_removal,[],[f133])).

fof(f133,plain,
    ( k3_relat_1(sK2) != k3_relat_1(sK2)
    | ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),k1_funct_1(k6_relat_1(k3_relat_1(sK2)),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2))),sK2)
    | sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)
    | ~ r2_hidden(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),k3_relat_1(sK2))
    | ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),sK2)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK2)))
    | k3_relat_1(sK2) != k1_relat_1(k6_relat_1(k3_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f132,f34])).

fof(f132,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),k1_funct_1(k6_relat_1(k3_relat_1(sK2)),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2))),sK2)
    | sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)
    | ~ r2_hidden(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),k3_relat_1(sK2))
    | ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),sK2)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK2)))
    | k3_relat_1(sK2) != k2_relat_1(k6_relat_1(k3_relat_1(sK2)))
    | k3_relat_1(sK2) != k1_relat_1(k6_relat_1(k3_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f131,f98])).

fof(f131,plain,
    ( sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)
    | ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK2)),sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),k1_funct_1(k6_relat_1(k3_relat_1(sK2)),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2))),sK2)
    | ~ r2_hidden(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),k3_relat_1(sK2))
    | ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),sK2)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK2)))
    | k3_relat_1(sK2) != k2_relat_1(k6_relat_1(k3_relat_1(sK2)))
    | k3_relat_1(sK2) != k1_relat_1(k6_relat_1(k3_relat_1(sK2))) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,
    ( sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)
    | ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK2)),sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),k1_funct_1(k6_relat_1(k3_relat_1(sK2)),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2))),sK2)
    | sP0(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)
    | ~ r2_hidden(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),k3_relat_1(sK2))
    | ~ r2_hidden(k4_tarski(sK3(sK2,k6_relat_1(k3_relat_1(sK2)),sK2),sK4(sK2,k6_relat_1(k3_relat_1(sK2)),sK2)),sK2)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK2)))
    | k3_relat_1(sK2) != k2_relat_1(k6_relat_1(k3_relat_1(sK2)))
    | k3_relat_1(sK2) != k1_relat_1(k6_relat_1(k3_relat_1(sK2))) ),
    inference(resolution,[],[f126,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(k1_funct_1(X1,sK3(X0,X1,X2)),k1_funct_1(X1,sK4(X0,X1,X2))),X0)
      | sP0(X0,X1,X2)
      | ~ r2_hidden(sK3(X0,X1,X2),k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v2_funct_1(X1)
      | k3_relat_1(X0) != k2_relat_1(X1)
      | k3_relat_1(X2) != k1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

%------------------------------------------------------------------------------
