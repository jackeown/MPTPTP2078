%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0776+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 113 expanded)
%              Number of leaves         :    8 (  27 expanded)
%              Depth                    :   16
%              Number of atoms          :  208 ( 546 expanded)
%              Number of equality atoms :   30 (  77 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(resolution,[],[f70,f26])).

fof(f26,plain,(
    ~ v4_relat_2(k2_wellord1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ v4_relat_2(k2_wellord1(sK1,sK0))
    & v4_relat_2(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ~ v4_relat_2(k2_wellord1(X1,X0))
        & v4_relat_2(X1)
        & v1_relat_1(X1) )
   => ( ~ v4_relat_2(k2_wellord1(sK1,sK0))
      & v4_relat_2(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ v4_relat_2(k2_wellord1(X1,X0))
      & v4_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ v4_relat_2(k2_wellord1(X1,X0))
      & v4_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v4_relat_2(X1)
         => v4_relat_2(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
       => v4_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_wellord1)).

fof(f70,plain,(
    ! [X0] : v4_relat_2(k2_wellord1(sK1,X0)) ),
    inference(subsumption_resolution,[],[f69,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X0] :
      ( v4_relat_2(k2_wellord1(sK1,X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f68,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f68,plain,(
    ! [X1] :
      ( ~ v1_relat_1(k2_wellord1(sK1,X1))
      | v4_relat_2(k2_wellord1(sK1,X1)) ) ),
    inference(global_subsumption,[],[f67,f47])).

fof(f47,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,X1)),sK3(k2_wellord1(sK1,X1))),sK1)
      | v4_relat_2(k2_wellord1(sK1,X1))
      | ~ v1_relat_1(k2_wellord1(sK1,X1)) ) ),
    inference(resolution,[],[f43,f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK2(X0) != sK3(X0)
        & r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0)
        & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_wellord1(sK1,X0))
      | r2_hidden(X1,sK1) ) ),
    inference(superposition,[],[f41,f42])).

fof(f42,plain,(
    ! [X0] : k2_wellord1(sK1,X0) = k3_xboole_0(sK1,k2_zfmisc_1(X0,X0)) ),
    inference(resolution,[],[f24,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
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

% (9204)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
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

fof(f67,plain,(
    ! [X0] :
      ( v4_relat_2(k2_wellord1(sK1,X0))
      | ~ v1_relat_1(k2_wellord1(sK1,X0))
      | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,X0)),sK3(k2_wellord1(sK1,X0))),sK1) ) ),
    inference(subsumption_resolution,[],[f66,f30])).

fof(f30,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    ! [X0] :
      ( v4_relat_2(k2_wellord1(sK1,X0))
      | ~ v1_relat_1(k2_wellord1(sK1,X0))
      | sK3(k2_wellord1(sK1,X0)) = sK2(k2_wellord1(sK1,X0))
      | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,X0)),sK3(k2_wellord1(sK1,X0))),sK1) ) ),
    inference(subsumption_resolution,[],[f65,f24])).

fof(f65,plain,(
    ! [X0] :
      ( v4_relat_2(k2_wellord1(sK1,X0))
      | ~ v1_relat_1(k2_wellord1(sK1,X0))
      | sK3(k2_wellord1(sK1,X0)) = sK2(k2_wellord1(sK1,X0))
      | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,X0)),sK3(k2_wellord1(sK1,X0))),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f64,f25])).

fof(f25,plain,(
    v4_relat_2(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X0] :
      ( v4_relat_2(k2_wellord1(sK1,X0))
      | ~ v1_relat_1(k2_wellord1(sK1,X0))
      | sK3(k2_wellord1(sK1,X0)) = sK2(k2_wellord1(sK1,X0))
      | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,X0)),sK3(k2_wellord1(sK1,X0))),sK1)
      | ~ v4_relat_2(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f46,f27])).

fof(f27,plain,(
    ! [X4,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X4,X3),X0)
      | X3 = X4
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,X0)),sK2(k2_wellord1(sK1,X0))),sK1)
      | v4_relat_2(k2_wellord1(sK1,X0))
      | ~ v1_relat_1(k2_wellord1(sK1,X0)) ) ),
    inference(resolution,[],[f43,f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0)
      | v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

%------------------------------------------------------------------------------
