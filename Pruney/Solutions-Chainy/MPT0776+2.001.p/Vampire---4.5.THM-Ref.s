%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 306 expanded)
%              Number of leaves         :   13 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  316 (1347 expanded)
%              Number of equality atoms :   74 ( 258 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(subsumption_resolution,[],[f331,f308])).

fof(f308,plain,(
    ~ r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),sK1) ),
    inference(unit_resulting_resolution,[],[f88,f298,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | X0 = X1
      | ~ r2_hidden(X1,k1_wellord1(sK1,X0)) ) ),
    inference(resolution,[],[f85,f82])).

fof(f82,plain,(
    ! [X8,X9] :
      ( r2_hidden(k4_tarski(X8,X9),sK1)
      | ~ r2_hidden(X8,k1_wellord1(sK1,X9)) ) ),
    inference(resolution,[],[f35,f67])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | r2_hidden(k4_tarski(X4,X1),X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0)
                | sK4(X0,X1,X2) = X1
                | ~ r2_hidden(sK4(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0)
                  & sK4(X0,X1,X2) != X1 )
                | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0)
          | sK4(X0,X1,X2) = X1
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0)
            & sK4(X0,X1,X2) != X1 )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

% (26629)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
fof(f25,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

% (26645)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ v4_relat_2(k2_wellord1(sK1,sK0))
    & v4_relat_2(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ~ v4_relat_2(k2_wellord1(X1,X0))
        & v4_relat_2(X1)
        & v1_relat_1(X1) )
   => ( ~ v4_relat_2(k2_wellord1(sK1,sK0))
      & v4_relat_2(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ~ v4_relat_2(k2_wellord1(X1,X0))
      & v4_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ~ v4_relat_2(k2_wellord1(X1,X0))
      & v4_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v4_relat_2(X1)
         => v4_relat_2(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
       => v4_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_wellord1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X0),sK1)
      | ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f84,f35])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | ~ r2_hidden(k4_tarski(X1,X0),sK1)
      | X0 = X1
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f36,f38])).

fof(f38,plain,(
    ! [X4,X0,X3] :
      ( ~ v4_relat_2(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ( sK2(X0) != sK3(X0)
            & r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0)
            & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f22,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK2(X0) != sK3(X0)
        & r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0)
        & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | ~ r2_hidden(k4_tarski(X2,X1),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).

fof(f36,plain,(
    v4_relat_2(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f298,plain,(
    r2_hidden(sK2(k2_wellord1(sK1,sK0)),k1_wellord1(sK1,sK3(k2_wellord1(sK1,sK0)))) ),
    inference(unit_resulting_resolution,[],[f211,f294])).

fof(f294,plain,(
    ! [X12,X10,X11] :
      ( ~ r2_hidden(X12,k1_wellord1(k2_wellord1(sK1,X11),X10))
      | r2_hidden(X12,k1_wellord1(sK1,X10)) ) ),
    inference(superposition,[],[f72,f117])).

fof(f117,plain,(
    ! [X0,X1] : k1_wellord1(k2_wellord1(sK1,X0),X1) = k1_setfam_1(k2_tarski(k1_wellord1(sK1,X1),k1_wellord1(k2_wellord1(sK1,X0),X1))) ),
    inference(forward_demodulation,[],[f115,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f115,plain,(
    ! [X0,X1] : k1_wellord1(k2_wellord1(sK1,X0),X1) = k1_setfam_1(k2_tarski(k1_wellord1(k2_wellord1(sK1,X0),X1),k1_wellord1(sK1,X1))) ),
    inference(unit_resulting_resolution,[],[f74,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f51,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

% (26627)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k1_wellord1(k2_wellord1(sK1,X0),X1),k1_wellord1(sK1,X1)) ),
    inference(unit_resulting_resolution,[],[f35,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_wellord1)).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f53,f49])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f211,plain,(
    r2_hidden(sK2(k2_wellord1(sK1,sK0)),k1_wellord1(k2_wellord1(sK1,sK0),sK3(k2_wellord1(sK1,sK0)))) ),
    inference(unit_resulting_resolution,[],[f73,f88,f86,f66])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | r2_hidden(X4,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f37,f73,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | v4_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    ~ v4_relat_2(k2_wellord1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    ! [X0] : v1_relat_1(k2_wellord1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f35,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f88,plain,(
    sK2(k2_wellord1(sK1,sK0)) != sK3(k2_wellord1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f37,f73,f41])).

fof(f41,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f331,plain,(
    r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),sK1) ),
    inference(unit_resulting_resolution,[],[f35,f299,f67])).

fof(f299,plain,(
    r2_hidden(sK3(k2_wellord1(sK1,sK0)),k1_wellord1(sK1,sK2(k2_wellord1(sK1,sK0)))) ),
    inference(unit_resulting_resolution,[],[f240,f294])).

fof(f240,plain,(
    r2_hidden(sK3(k2_wellord1(sK1,sK0)),k1_wellord1(k2_wellord1(sK1,sK0),sK2(k2_wellord1(sK1,sK0)))) ),
    inference(unit_resulting_resolution,[],[f73,f88,f87,f66])).

fof(f87,plain,(
    r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f37,f73,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0)
      | v4_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:25:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (26646)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (26630)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (26623)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.56  % (26619)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.56  % (26632)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (26622)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.56  % (26631)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (26646)Refutation not found, incomplete strategy% (26646)------------------------------
% 0.22/0.56  % (26646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (26646)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (26646)Memory used [KB]: 6268
% 0.22/0.57  % (26646)Time elapsed: 0.137 s
% 0.22/0.57  % (26646)------------------------------
% 0.22/0.57  % (26646)------------------------------
% 0.22/0.57  % (26626)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.57  % (26620)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.57  % (26624)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.58  % (26633)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.58  % (26637)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.58  % (26643)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.58  % (26640)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.58  % (26635)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.58  % (26630)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % (26635)Refutation not found, incomplete strategy% (26635)------------------------------
% 0.22/0.58  % (26635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (26635)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (26635)Memory used [KB]: 10618
% 0.22/0.58  % (26635)Time elapsed: 0.165 s
% 0.22/0.58  % (26635)------------------------------
% 0.22/0.58  % (26635)------------------------------
% 1.72/0.58  % (26648)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.72/0.58  % SZS output start Proof for theBenchmark
% 1.72/0.58  fof(f349,plain,(
% 1.72/0.58    $false),
% 1.72/0.58    inference(subsumption_resolution,[],[f331,f308])).
% 1.72/0.58  fof(f308,plain,(
% 1.72/0.58    ~r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),sK1)),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f88,f298,f148])).
% 1.72/0.58  fof(f148,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | X0 = X1 | ~r2_hidden(X1,k1_wellord1(sK1,X0))) )),
% 1.72/0.58    inference(resolution,[],[f85,f82])).
% 1.72/0.58  fof(f82,plain,(
% 1.72/0.58    ( ! [X8,X9] : (r2_hidden(k4_tarski(X8,X9),sK1) | ~r2_hidden(X8,k1_wellord1(sK1,X9))) )),
% 1.72/0.58    inference(resolution,[],[f35,f67])).
% 1.72/0.58  fof(f67,plain,(
% 1.72/0.58    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | r2_hidden(k4_tarski(X4,X1),X0)) )),
% 1.72/0.58    inference(equality_resolution,[],[f43])).
% 1.72/0.58  fof(f43,plain,(
% 1.72/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f29])).
% 1.72/0.58  fof(f29,plain,(
% 1.72/0.58    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0) | sK4(X0,X1,X2) = X1 | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0) & sK4(X0,X1,X2) != X1) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.72/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 1.72/0.58  fof(f28,plain,(
% 1.72/0.58    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0) | sK4(X0,X1,X2) = X1 | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),X1),X0) & sK4(X0,X1,X2) != X1) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.72/0.58    introduced(choice_axiom,[])).
% 1.72/0.58  fof(f27,plain,(
% 1.72/0.58    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.72/0.58    inference(rectify,[],[f26])).
% 1.72/0.58  fof(f26,plain,(
% 1.72/0.58    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.72/0.58    inference(flattening,[],[f25])).
% 1.72/0.58  % (26629)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.72/0.58  fof(f25,plain,(
% 1.72/0.58    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.72/0.58    inference(nnf_transformation,[],[f15])).
% 1.72/0.58  fof(f15,plain,(
% 1.72/0.58    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 1.72/0.58    inference(ennf_transformation,[],[f5])).
% 1.72/0.58  fof(f5,axiom,(
% 1.72/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 1.72/0.58  % (26645)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.72/0.58  fof(f35,plain,(
% 1.72/0.58    v1_relat_1(sK1)),
% 1.72/0.58    inference(cnf_transformation,[],[f20])).
% 1.72/0.58  fof(f20,plain,(
% 1.72/0.58    ~v4_relat_2(k2_wellord1(sK1,sK0)) & v4_relat_2(sK1) & v1_relat_1(sK1)),
% 1.72/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f19])).
% 1.72/0.58  fof(f19,plain,(
% 1.72/0.58    ? [X0,X1] : (~v4_relat_2(k2_wellord1(X1,X0)) & v4_relat_2(X1) & v1_relat_1(X1)) => (~v4_relat_2(k2_wellord1(sK1,sK0)) & v4_relat_2(sK1) & v1_relat_1(sK1))),
% 1.72/0.58    introduced(choice_axiom,[])).
% 1.72/0.58  fof(f12,plain,(
% 1.72/0.58    ? [X0,X1] : (~v4_relat_2(k2_wellord1(X1,X0)) & v4_relat_2(X1) & v1_relat_1(X1))),
% 1.72/0.58    inference(flattening,[],[f11])).
% 1.72/0.58  fof(f11,plain,(
% 1.72/0.58    ? [X0,X1] : ((~v4_relat_2(k2_wellord1(X1,X0)) & v4_relat_2(X1)) & v1_relat_1(X1))),
% 1.72/0.58    inference(ennf_transformation,[],[f10])).
% 1.72/0.58  fof(f10,negated_conjecture,(
% 1.72/0.58    ~! [X0,X1] : (v1_relat_1(X1) => (v4_relat_2(X1) => v4_relat_2(k2_wellord1(X1,X0))))),
% 1.72/0.58    inference(negated_conjecture,[],[f9])).
% 1.72/0.58  fof(f9,conjecture,(
% 1.72/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_2(X1) => v4_relat_2(k2_wellord1(X1,X0))))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_wellord1)).
% 1.72/0.58  fof(f85,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X1,X0),sK1) | ~r2_hidden(k4_tarski(X0,X1),sK1) | X0 = X1) )),
% 1.72/0.58    inference(subsumption_resolution,[],[f84,f35])).
% 1.72/0.58  fof(f84,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(k4_tarski(X1,X0),sK1) | X0 = X1 | ~v1_relat_1(sK1)) )),
% 1.72/0.58    inference(resolution,[],[f36,f38])).
% 1.72/0.58  fof(f38,plain,(
% 1.72/0.58    ( ! [X4,X0,X3] : (~v4_relat_2(X0) | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~v1_relat_1(X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f24])).
% 1.72/0.58  fof(f24,plain,(
% 1.72/0.58    ! [X0] : (((v4_relat_2(X0) | (sK2(X0) != sK3(X0) & r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0) & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.72/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f22,f23])).
% 1.72/0.58  fof(f23,plain,(
% 1.72/0.58    ! [X0] : (? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (sK2(X0) != sK3(X0) & r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0) & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)))),
% 1.72/0.58    introduced(choice_axiom,[])).
% 1.72/0.58  fof(f22,plain,(
% 1.72/0.58    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.72/0.58    inference(rectify,[],[f21])).
% 1.72/0.58  fof(f21,plain,(
% 1.72/0.58    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.72/0.58    inference(nnf_transformation,[],[f14])).
% 1.72/0.58  fof(f14,plain,(
% 1.72/0.58    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 1.72/0.58    inference(flattening,[],[f13])).
% 1.72/0.58  fof(f13,plain,(
% 1.72/0.58    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | (~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 1.72/0.58    inference(ennf_transformation,[],[f7])).
% 1.72/0.58  fof(f7,axiom,(
% 1.72/0.58    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> ! [X1,X2] : ((r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => X1 = X2)))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).
% 1.72/0.58  fof(f36,plain,(
% 1.72/0.58    v4_relat_2(sK1)),
% 1.72/0.58    inference(cnf_transformation,[],[f20])).
% 1.72/0.58  fof(f298,plain,(
% 1.72/0.58    r2_hidden(sK2(k2_wellord1(sK1,sK0)),k1_wellord1(sK1,sK3(k2_wellord1(sK1,sK0))))),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f211,f294])).
% 1.72/0.58  fof(f294,plain,(
% 1.72/0.58    ( ! [X12,X10,X11] : (~r2_hidden(X12,k1_wellord1(k2_wellord1(sK1,X11),X10)) | r2_hidden(X12,k1_wellord1(sK1,X10))) )),
% 1.72/0.58    inference(superposition,[],[f72,f117])).
% 1.72/0.58  fof(f117,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k1_wellord1(k2_wellord1(sK1,X0),X1) = k1_setfam_1(k2_tarski(k1_wellord1(sK1,X1),k1_wellord1(k2_wellord1(sK1,X0),X1)))) )),
% 1.72/0.58    inference(forward_demodulation,[],[f115,f48])).
% 1.72/0.58  fof(f48,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f3])).
% 1.72/0.58  fof(f3,axiom,(
% 1.72/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.72/0.58  fof(f115,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k1_wellord1(k2_wellord1(sK1,X0),X1) = k1_setfam_1(k2_tarski(k1_wellord1(k2_wellord1(sK1,X0),X1),k1_wellord1(sK1,X1)))) )),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f74,f59])).
% 1.72/0.58  fof(f59,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 1.72/0.58    inference(definition_unfolding,[],[f51,f49])).
% 1.72/0.58  fof(f49,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.72/0.58    inference(cnf_transformation,[],[f4])).
% 1.72/0.58  fof(f4,axiom,(
% 1.72/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.72/0.58  fof(f51,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f17])).
% 1.72/0.58  % (26627)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.72/0.58  fof(f17,plain,(
% 1.72/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.72/0.58    inference(ennf_transformation,[],[f2])).
% 1.72/0.58  fof(f2,axiom,(
% 1.72/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.72/0.58  fof(f74,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r1_tarski(k1_wellord1(k2_wellord1(sK1,X0),X1),k1_wellord1(sK1,X1))) )),
% 1.72/0.58    inference(unit_resulting_resolution,[],[f35,f52])).
% 1.72/0.58  fof(f52,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f18])).
% 1.72/0.58  fof(f18,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)) | ~v1_relat_1(X2))),
% 1.72/0.58    inference(ennf_transformation,[],[f8])).
% 1.72/0.58  fof(f8,axiom,(
% 1.72/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k1_wellord1(k2_wellord1(X2,X0),X1),k1_wellord1(X2,X1)))),
% 1.72/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_wellord1)).
% 1.72/0.58  fof(f72,plain,(
% 1.72/0.58    ( ! [X4,X0,X1] : (~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) | r2_hidden(X4,X0)) )),
% 1.72/0.58    inference(equality_resolution,[],[f65])).
% 1.72/0.58  fof(f65,plain,(
% 1.72/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.72/0.58    inference(definition_unfolding,[],[f53,f49])).
% 1.72/0.58  fof(f53,plain,(
% 1.72/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.72/0.58    inference(cnf_transformation,[],[f34])).
% 1.72/0.59  fof(f34,plain,(
% 1.72/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.72/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).
% 1.72/0.59  fof(f33,plain,(
% 1.72/0.59    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.72/0.59    introduced(choice_axiom,[])).
% 1.72/0.59  fof(f32,plain,(
% 1.72/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.72/0.59    inference(rectify,[],[f31])).
% 1.72/0.59  fof(f31,plain,(
% 1.72/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.72/0.59    inference(flattening,[],[f30])).
% 1.72/0.59  fof(f30,plain,(
% 1.72/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.72/0.59    inference(nnf_transformation,[],[f1])).
% 1.72/0.59  fof(f1,axiom,(
% 1.72/0.59    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.72/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.72/0.59  fof(f211,plain,(
% 1.72/0.59    r2_hidden(sK2(k2_wellord1(sK1,sK0)),k1_wellord1(k2_wellord1(sK1,sK0),sK3(k2_wellord1(sK1,sK0))))),
% 1.72/0.59    inference(unit_resulting_resolution,[],[f73,f88,f86,f66])).
% 1.72/0.59  fof(f66,plain,(
% 1.72/0.59    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | r2_hidden(X4,k1_wellord1(X0,X1))) )),
% 1.72/0.59    inference(equality_resolution,[],[f44])).
% 1.72/0.59  fof(f44,plain,(
% 1.72/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f29])).
% 1.72/0.59  fof(f86,plain,(
% 1.72/0.59    r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))),
% 1.72/0.59    inference(unit_resulting_resolution,[],[f37,f73,f39])).
% 1.72/0.59  fof(f39,plain,(
% 1.72/0.59    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) | v4_relat_2(X0)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f24])).
% 1.72/0.59  fof(f37,plain,(
% 1.72/0.59    ~v4_relat_2(k2_wellord1(sK1,sK0))),
% 1.72/0.59    inference(cnf_transformation,[],[f20])).
% 1.72/0.59  fof(f73,plain,(
% 1.72/0.59    ( ! [X0] : (v1_relat_1(k2_wellord1(sK1,X0))) )),
% 1.72/0.59    inference(unit_resulting_resolution,[],[f35,f50])).
% 1.72/0.59  fof(f50,plain,(
% 1.72/0.59    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f16])).
% 1.72/0.59  fof(f16,plain,(
% 1.72/0.59    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 1.72/0.59    inference(ennf_transformation,[],[f6])).
% 1.72/0.59  fof(f6,axiom,(
% 1.72/0.59    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 1.72/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 1.72/0.59  fof(f88,plain,(
% 1.72/0.59    sK2(k2_wellord1(sK1,sK0)) != sK3(k2_wellord1(sK1,sK0))),
% 1.72/0.59    inference(unit_resulting_resolution,[],[f37,f73,f41])).
% 1.72/0.59  fof(f41,plain,(
% 1.72/0.59    ( ! [X0] : (sK2(X0) != sK3(X0) | v4_relat_2(X0) | ~v1_relat_1(X0)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f24])).
% 1.72/0.59  fof(f331,plain,(
% 1.72/0.59    r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),sK1)),
% 1.72/0.59    inference(unit_resulting_resolution,[],[f35,f299,f67])).
% 1.72/0.59  fof(f299,plain,(
% 1.72/0.59    r2_hidden(sK3(k2_wellord1(sK1,sK0)),k1_wellord1(sK1,sK2(k2_wellord1(sK1,sK0))))),
% 1.72/0.59    inference(unit_resulting_resolution,[],[f240,f294])).
% 1.72/0.59  fof(f240,plain,(
% 1.72/0.59    r2_hidden(sK3(k2_wellord1(sK1,sK0)),k1_wellord1(k2_wellord1(sK1,sK0),sK2(k2_wellord1(sK1,sK0))))),
% 1.72/0.59    inference(unit_resulting_resolution,[],[f73,f88,f87,f66])).
% 1.72/0.59  fof(f87,plain,(
% 1.72/0.59    r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))),
% 1.72/0.59    inference(unit_resulting_resolution,[],[f37,f73,f40])).
% 1.72/0.59  fof(f40,plain,(
% 1.72/0.59    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0) | v4_relat_2(X0)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f24])).
% 1.72/0.59  % SZS output end Proof for theBenchmark
% 1.72/0.59  % (26630)------------------------------
% 1.72/0.59  % (26630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.59  % (26630)Termination reason: Refutation
% 1.72/0.59  
% 1.72/0.59  % (26630)Memory used [KB]: 6652
% 1.72/0.59  % (26630)Time elapsed: 0.150 s
% 1.72/0.59  % (26630)------------------------------
% 1.72/0.59  % (26630)------------------------------
% 1.72/0.59  % (26618)Success in time 0.224 s
%------------------------------------------------------------------------------
