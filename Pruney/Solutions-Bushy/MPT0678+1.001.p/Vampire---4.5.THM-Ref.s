%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0678+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:26 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 355 expanded)
%              Number of leaves         :   12 (  86 expanded)
%              Depth                    :   18
%              Number of atoms          :  264 (1534 expanded)
%              Number of equality atoms :   74 ( 420 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f775,plain,(
    $false ),
    inference(resolution,[],[f725,f217])).

fof(f217,plain,(
    ~ v1_xboole_0(k11_relat_1(sK0,sK1(sK0))) ),
    inference(superposition,[],[f40,f155])).

fof(f155,plain,(
    k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0))) ),
    inference(subsumption_resolution,[],[f154,f36])).

fof(f36,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ v2_funct_1(sK0)
    & ! [X1,X2] : k9_relat_1(sK0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2))
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(X0)
        & ! [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(sK0)
      & ! [X2,X1] : k9_relat_1(sK0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2))
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

% (12624)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ! [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_funct_1)).

fof(f154,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f153,f37])).

fof(f37,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f153,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f151,f39])).

fof(f39,plain,(
    ~ v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f151,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0)))
    | v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f101,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK1(X0) != sK2(X0)
            & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
            & r2_hidden(sK2(X0),k1_relat_1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK1(X0) != sK2(X0)
        & k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
        & r2_hidden(sK2(X0),k1_relat_1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f101,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK0))
      | k11_relat_1(sK0,X0) = k1_tarski(k1_funct_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f100,f36])).

fof(f100,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK0))
      | k11_relat_1(sK0,X0) = k1_tarski(k1_funct_1(sK0,X0))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f54,f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(f40,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f725,plain,(
    ! [X0] : v1_xboole_0(X0) ),
    inference(subsumption_resolution,[],[f724,f217])).

fof(f724,plain,(
    ! [X0] :
      ( v1_xboole_0(k11_relat_1(sK0,sK1(sK0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f551,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | v1_xboole_0(X0)
      | v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f53,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ~ r1_subset_1(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r1_subset_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f551,plain,(
    r1_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK1(sK0))) ),
    inference(forward_demodulation,[],[f550,f160])).

fof(f160,plain,(
    k11_relat_1(sK0,sK1(sK0)) = k11_relat_1(sK0,sK2(sK0)) ),
    inference(forward_demodulation,[],[f159,f155])).

fof(f159,plain,(
    k1_tarski(k1_funct_1(sK0,sK1(sK0))) = k11_relat_1(sK0,sK2(sK0)) ),
    inference(forward_demodulation,[],[f158,f99])).

fof(f99,plain,(
    k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0)) ),
    inference(subsumption_resolution,[],[f98,f36])).

fof(f98,plain,
    ( k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f97,f37])).

fof(f97,plain,
    ( k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f46,f39])).

fof(f46,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f158,plain,(
    k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK2(sK0))) ),
    inference(subsumption_resolution,[],[f157,f36])).

fof(f157,plain,
    ( k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK2(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f156,f37])).

fof(f156,plain,
    ( k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK2(sK0)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f152,f39])).

fof(f152,plain,
    ( k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK2(sK0)))
    | v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f101,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f550,plain,(
    r1_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK2(sK0))) ),
    inference(forward_demodulation,[],[f549,f67])).

fof(f67,plain,(
    ! [X0] : k11_relat_1(sK0,X0) = k9_relat_1(sK0,k1_tarski(X0)) ),
    inference(resolution,[],[f42,f36])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f549,plain,(
    r1_xboole_0(k11_relat_1(sK0,sK1(sK0)),k9_relat_1(sK0,k1_tarski(sK2(sK0)))) ),
    inference(subsumption_resolution,[],[f539,f57])).

fof(f57,plain,(
    k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f41,f36])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

fof(f539,plain,
    ( k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0)
    | r1_xboole_0(k11_relat_1(sK0,sK1(sK0)),k9_relat_1(sK0,k1_tarski(sK2(sK0)))) ),
    inference(superposition,[],[f187,f538])).

fof(f538,plain,(
    k1_xboole_0 = k3_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0))) ),
    inference(subsumption_resolution,[],[f537,f36])).

fof(f537,plain,
    ( ~ v1_relat_1(sK0)
    | k1_xboole_0 = k3_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0))) ),
    inference(subsumption_resolution,[],[f536,f37])).

fof(f536,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_xboole_0 = k3_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0))) ),
    inference(resolution,[],[f180,f39])).

fof(f180,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k3_xboole_0(k1_tarski(sK1(X0)),k1_tarski(sK2(X0))) ) ),
    inference(resolution,[],[f77,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f77,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_tarski(sK1(X0)),k1_tarski(sK2(X0)))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(extensionality_resolution,[],[f50,f47])).

fof(f47,plain,(
    ! [X0] :
      ( sK1(X0) != sK2(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f187,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k9_relat_1(sK0,k3_xboole_0(k1_tarski(X1),X2))
      | r1_xboole_0(k11_relat_1(sK0,X1),k9_relat_1(sK0,X2)) ) ),
    inference(superposition,[],[f87,f67])).

fof(f87,plain,(
    ! [X2,X1] :
      ( r1_xboole_0(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2))
      | k1_xboole_0 != k9_relat_1(sK0,k3_xboole_0(X1,X2)) ) ),
    inference(superposition,[],[f56,f38])).

fof(f38,plain,(
    ! [X2,X1] : k9_relat_1(sK0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

%------------------------------------------------------------------------------
