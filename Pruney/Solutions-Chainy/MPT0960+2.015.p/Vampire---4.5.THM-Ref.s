%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 322 expanded)
%              Number of leaves         :   17 (  90 expanded)
%              Depth                    :   18
%              Number of atoms          :  289 (1301 expanded)
%              Number of equality atoms :   52 ( 206 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (32346)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f292,plain,(
    $false ),
    inference(subsumption_resolution,[],[f39,f284])).

fof(f284,plain,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(backward_demodulation,[],[f244,f272])).

fof(f272,plain,(
    ! [X1] : k2_relat_1(k1_wellord2(X1)) = X1 ),
    inference(forward_demodulation,[],[f268,f245])).

fof(f245,plain,(
    ! [X0] : k2_xboole_0(X0,k2_relat_1(k1_wellord2(X0))) = X0 ),
    inference(backward_demodulation,[],[f92,f243])).

fof(f243,plain,(
    ! [X0] : k1_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f235,f242])).

fof(f242,plain,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) ),
    inference(duplicate_literal_removal,[],[f241])).

fof(f241,plain,(
    ! [X0] :
      ( r1_tarski(k6_relat_1(X0),k1_wellord2(X0))
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) ) ),
    inference(resolution,[],[f240,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,k1_wellord2(X1)),X0)
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) ) ),
    inference(resolution,[],[f49,f40])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1)
        & r2_hidden(sK3(X0,X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r2_hidden(k4_tarski(X2,X2),X1) )
       => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).

fof(f240,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,k1_wellord2(X1)),X1)
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) ) ),
    inference(resolution,[],[f204,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f204,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK3(X0,k1_wellord2(X1)),sK3(X0,k1_wellord2(X1)))
      | ~ r2_hidden(sK3(X0,k1_wellord2(X1)),X1)
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) ) ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),k1_wellord2(X1))
      | ~ r2_hidden(sK3(X0,k1_wellord2(X1)),X1)
      | ~ r2_hidden(sK3(X0,k1_wellord2(X1)),X1)
      | ~ r1_tarski(sK3(X0,k1_wellord2(X1)),sK3(X0,k1_wellord2(X1))) ) ),
    inference(resolution,[],[f146,f169])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f55,f74])).

fof(f74,plain,(
    ! [X0] : sP0(k1_wellord2(X0),X0) ),
    inference(subsumption_resolution,[],[f65,f72])).

fof(f72,plain,(
    ! [X0,X1] : sP1(X0,k1_wellord2(X1)) ),
    inference(resolution,[],[f60,f40])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f22,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
            <=> r1_tarski(X2,X3) )
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        & k3_relat_1(X1) = X0 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f65,plain,(
    ! [X0] :
      ( sP0(k1_wellord2(X0),X0)
      | ~ sP1(X0,k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | k1_wellord2(X0) != X1
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | k1_wellord2(X0) != X1 ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f55,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(k4_tarski(X4,X5),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
            | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
          & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
            | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
          & r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X1) )
        | k3_relat_1(X0) != X1 )
      & ( ( ! [X4,X5] :
              ( ( ( r2_hidden(k4_tarski(X4,X5),X0)
                  | ~ r1_tarski(X4,X5) )
                & ( r1_tarski(X4,X5)
                  | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          & k3_relat_1(X0) = X1 )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X0) )
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
        & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X0) )
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | k3_relat_1(X0) != X1 )
      & ( ( ! [X4,X5] :
              ( ( ( r2_hidden(k4_tarski(X4,X5),X0)
                  | ~ r1_tarski(X4,X5) )
                & ( r1_tarski(X4,X5)
                  | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          & k3_relat_1(X0) = X1 )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
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
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
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
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,k1_wellord2(X1)),sK3(X0,k1_wellord2(X1))),k1_wellord2(X1))
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) ) ),
    inference(resolution,[],[f50,f40])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1)
      | r1_tarski(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f235,plain,(
    ! [X0] :
      ( ~ r1_tarski(k6_relat_1(X0),k1_wellord2(X0))
      | k1_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(global_subsumption,[],[f40,f41,f234])).

fof(f234,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | ~ r1_tarski(k6_relat_1(X0),k1_wellord2(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k1_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(superposition,[],[f120,f42])).

fof(f42,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f120,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_wellord2(k1_relat_1(X0)))
      | ~ r1_tarski(X0,k1_wellord2(k1_relat_1(X0)))
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k1_wellord2(k1_relat_1(X0))) ) ),
    inference(resolution,[],[f46,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(k1_wellord2(X0)))
      | k1_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(resolution,[],[f97,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f97,plain,(
    ! [X1] : r1_tarski(k1_relat_1(k1_wellord2(X1)),X1) ),
    inference(superposition,[],[f48,f92])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f92,plain,(
    ! [X0] : k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = X0 ),
    inference(forward_demodulation,[],[f90,f75])).

fof(f75,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(resolution,[],[f53,f74])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k3_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) ),
    inference(resolution,[],[f45,f40])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f268,plain,(
    ! [X1] : k2_relat_1(k1_wellord2(X1)) = k2_xboole_0(X1,k2_relat_1(k1_wellord2(X1))) ),
    inference(resolution,[],[f242,f166])).

fof(f166,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k6_relat_1(X2),k1_wellord2(X3))
      | k2_relat_1(k1_wellord2(X3)) = k2_xboole_0(X2,k2_relat_1(k1_wellord2(X3))) ) ),
    inference(forward_demodulation,[],[f165,f43])).

fof(f43,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f165,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k6_relat_1(X2),k1_wellord2(X3))
      | k2_relat_1(k1_wellord2(X3)) = k2_xboole_0(k2_relat_1(k6_relat_1(X2)),k2_relat_1(k1_wellord2(X3))) ) ),
    inference(resolution,[],[f155,f41])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,k1_wellord2(X1))
      | k2_relat_1(k1_wellord2(X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(k1_wellord2(X1))) ) ),
    inference(resolution,[],[f126,f40])).

fof(f126,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X2)
      | k2_relat_1(X3) = k2_xboole_0(k2_relat_1(X2),k2_relat_1(X3)) ) ),
    inference(resolution,[],[f47,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f244,plain,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,k2_relat_1(k1_wellord2(X0)))) ),
    inference(backward_demodulation,[],[f79,f243])).

fof(f79,plain,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) ),
    inference(resolution,[],[f44,f40])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

% (32344)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f15,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f39,plain,(
    ~ r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ~ r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f27])).

fof(f27,plain,
    ( ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:37:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (32349)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.46  % (32357)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.48  % (32349)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.49  % (32346)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.49  fof(f292,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f39,f284])).
% 0.20/0.49  fof(f284,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))) )),
% 0.20/0.49    inference(backward_demodulation,[],[f244,f272])).
% 0.20/0.49  fof(f272,plain,(
% 0.20/0.49    ( ! [X1] : (k2_relat_1(k1_wellord2(X1)) = X1) )),
% 0.20/0.49    inference(forward_demodulation,[],[f268,f245])).
% 0.20/0.49  fof(f245,plain,(
% 0.20/0.49    ( ! [X0] : (k2_xboole_0(X0,k2_relat_1(k1_wellord2(X0))) = X0) )),
% 0.20/0.49    inference(backward_demodulation,[],[f92,f243])).
% 0.20/0.49  fof(f243,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(k1_wellord2(X0)) = X0) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f235,f242])).
% 0.20/0.49  fof(f242,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k1_wellord2(X0))) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f241])).
% 0.20/0.49  fof(f241,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) | r1_tarski(k6_relat_1(X0),k1_wellord2(X0))) )),
% 0.20/0.49    inference(resolution,[],[f240,f114])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,k1_wellord2(X1)),X0) | r1_tarski(k6_relat_1(X0),k1_wellord2(X1))) )),
% 0.20/0.49    inference(resolution,[],[f49,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r2_hidden(sK3(X0,X1),X0) | r1_tarski(k6_relat_1(X0),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | (~r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1) & r2_hidden(sK3(X0,X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0)) => (~r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0))) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : (r2_hidden(X2,X0) => r2_hidden(k4_tarski(X2,X2),X1)) => r1_tarski(k6_relat_1(X0),X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).
% 0.20/0.49  fof(f240,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(sK3(X0,k1_wellord2(X1)),X1) | r1_tarski(k6_relat_1(X0),k1_wellord2(X1))) )),
% 0.20/0.49    inference(resolution,[],[f204,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(flattening,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(sK3(X0,k1_wellord2(X1)),sK3(X0,k1_wellord2(X1))) | ~r2_hidden(sK3(X0,k1_wellord2(X1)),X1) | r1_tarski(k6_relat_1(X0),k1_wellord2(X1))) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f203])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) | ~r2_hidden(sK3(X0,k1_wellord2(X1)),X1) | ~r2_hidden(sK3(X0,k1_wellord2(X1)),X1) | ~r1_tarski(sK3(X0,k1_wellord2(X1)),sK3(X0,k1_wellord2(X1)))) )),
% 0.20/0.49    inference(resolution,[],[f146,f169])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(resolution,[],[f55,f74])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ( ! [X0] : (sP0(k1_wellord2(X0),X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f65,f72])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sP1(X0,k1_wellord2(X1))) )),
% 0.20/0.49    inference(resolution,[],[f60,f40])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | sP1(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1] : (sP1(X0,X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(definition_folding,[],[f22,f25,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ( ! [X0] : (sP0(k1_wellord2(X0),X0) | ~sP1(X0,k1_wellord2(X0))) )),
% 0.20/0.49    inference(equality_resolution,[],[f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sP0(X1,X0) | k1_wellord2(X0) != X1 | ~sP1(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ~sP0(X1,X0)) & (sP0(X1,X0) | k1_wellord2(X0) != X1)) | ~sP1(X0,X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f25])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X4,X0,X5,X1] : (~sP0(X0,X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | r2_hidden(k4_tarski(X4,X5),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_tarski(sK4(X0,X1),sK5(X0,X1)) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & (r1_tarski(sK4(X0,X1),sK5(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1)) | k3_relat_1(X0) != X1) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X0))) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) & k3_relat_1(X0) = X1) | ~sP0(X0,X1)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f34,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => ((~r1_tarski(sK4(X0,X1),sK5(X0,X1)) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & (r1_tarski(sK4(X0,X1),sK5(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) | k3_relat_1(X0) != X1) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X0))) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) & k3_relat_1(X0) = X1) | ~sP0(X0,X1)))),
% 0.20/0.49    inference(rectify,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X1,X0] : ((sP0(X1,X0) | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | ~sP0(X1,X0)))),
% 0.20/0.49    inference(flattening,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X1,X0] : ((sP0(X1,X0) | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | ~sP0(X1,X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f24])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK3(X0,k1_wellord2(X1)),sK3(X0,k1_wellord2(X1))),k1_wellord2(X1)) | r1_tarski(k6_relat_1(X0),k1_wellord2(X1))) )),
% 0.20/0.49    inference(resolution,[],[f50,f40])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1) | r1_tarski(k6_relat_1(X0),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f235,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) | k1_relat_1(k1_wellord2(X0)) = X0) )),
% 0.20/0.49    inference(global_subsumption,[],[f40,f41,f234])).
% 0.20/0.49  fof(f234,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(k1_wellord2(X0)) | ~r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) | ~v1_relat_1(k6_relat_1(X0)) | k1_relat_1(k1_wellord2(X0)) = X0) )),
% 0.20/0.49    inference(superposition,[],[f120,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(k1_wellord2(k1_relat_1(X0))) | ~r1_tarski(X0,k1_wellord2(k1_relat_1(X0))) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k1_wellord2(k1_relat_1(X0)))) )),
% 0.20/0.49    inference(resolution,[],[f46,f98])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k1_wellord2(X0))) | k1_relat_1(k1_wellord2(X0)) = X0) )),
% 0.20/0.49    inference(resolution,[],[f97,f64])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ( ! [X1] : (r1_tarski(k1_relat_1(k1_wellord2(X1)),X1)) )),
% 0.20/0.49    inference(superposition,[],[f48,f92])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    ( ! [X0] : (k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = X0) )),
% 0.20/0.49    inference(forward_demodulation,[],[f90,f75])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.20/0.49    inference(resolution,[],[f53,f74])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~sP0(X0,X1) | k3_relat_1(X0) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) )),
% 0.20/0.49    inference(resolution,[],[f45,f40])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.20/0.49  fof(f268,plain,(
% 0.20/0.49    ( ! [X1] : (k2_relat_1(k1_wellord2(X1)) = k2_xboole_0(X1,k2_relat_1(k1_wellord2(X1)))) )),
% 0.20/0.49    inference(resolution,[],[f242,f166])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~r1_tarski(k6_relat_1(X2),k1_wellord2(X3)) | k2_relat_1(k1_wellord2(X3)) = k2_xboole_0(X2,k2_relat_1(k1_wellord2(X3)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f165,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~r1_tarski(k6_relat_1(X2),k1_wellord2(X3)) | k2_relat_1(k1_wellord2(X3)) = k2_xboole_0(k2_relat_1(k6_relat_1(X2)),k2_relat_1(k1_wellord2(X3)))) )),
% 0.20/0.49    inference(resolution,[],[f155,f41])).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X0,k1_wellord2(X1)) | k2_relat_1(k1_wellord2(X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(k1_wellord2(X1)))) )),
% 0.20/0.49    inference(resolution,[],[f126,f40])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~v1_relat_1(X3) | ~r1_tarski(X2,X3) | ~v1_relat_1(X2) | k2_relat_1(X3) = k2_xboole_0(k2_relat_1(X2),k2_relat_1(X3))) )),
% 0.20/0.49    inference(resolution,[],[f47,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f244,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,k2_relat_1(k1_wellord2(X0))))) )),
% 0.20/0.49    inference(backward_demodulation,[],[f79,f243])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))))) )),
% 0.20/0.49    inference(resolution,[],[f44,f40])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  % (32344)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ~r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ~r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,negated_conjecture,(
% 0.20/0.49    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.20/0.49    inference(negated_conjecture,[],[f12])).
% 0.20/0.49  fof(f12,conjecture,(
% 0.20/0.49    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (32349)------------------------------
% 0.20/0.49  % (32349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (32349)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (32349)Memory used [KB]: 6396
% 0.20/0.49  % (32349)Time elapsed: 0.075 s
% 0.20/0.49  % (32349)------------------------------
% 0.20/0.49  % (32349)------------------------------
% 0.20/0.49  % (32336)Success in time 0.14 s
%------------------------------------------------------------------------------
