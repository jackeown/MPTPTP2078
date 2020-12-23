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
% DateTime   : Thu Dec  3 12:54:05 EST 2020

% Result     : Theorem 2.73s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 222 expanded)
%              Number of leaves         :   14 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  267 ( 876 expanded)
%              Number of equality atoms :   42 (  64 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1443,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1424,f776])).

fof(f776,plain,(
    r2_hidden(sK3(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k6_subset_1(k1_relat_1(sK1),sK0)) ),
    inference(unit_resulting_resolution,[],[f152,f391,f134])).

fof(f134,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k6_subset_1(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f110,f87])).

fof(f87,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f110,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f68])).

% (1879)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f66,f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
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
    inference(rectify,[],[f65])).

fof(f65,plain,(
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
    inference(flattening,[],[f64])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f391,plain,(
    r2_hidden(sK3(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f138,f151,f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f60,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f151,plain,(
    r2_hidden(sK3(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f72,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f72,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f50])).

fof(f50,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f138,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f69,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f69,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f152,plain,(
    ~ r2_hidden(sK3(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f72,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1424,plain,(
    ~ r2_hidden(sK3(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k6_subset_1(k1_relat_1(sK1),sK0)) ),
    inference(unit_resulting_resolution,[],[f285,f387,f98])).

fof(f387,plain,(
    ! [X0] : ~ r2_hidden(sK3(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k6_subset_1(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) ),
    inference(unit_resulting_resolution,[],[f151,f135])).

fof(f135,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f109,f87])).

fof(f109,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f285,plain,(
    ! [X0] : r1_tarski(k6_subset_1(k1_relat_1(sK1),X0),k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ),
    inference(backward_demodulation,[],[f185,f284])).

fof(f284,plain,(
    ! [X4] : k10_relat_1(sK1,k6_subset_1(k2_relat_1(sK1),X4)) = k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,X4)) ),
    inference(subsumption_resolution,[],[f283,f69])).

fof(f283,plain,(
    ! [X4] :
      ( k10_relat_1(sK1,k6_subset_1(k2_relat_1(sK1),X4)) = k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,X4))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f268,f70])).

fof(f70,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f268,plain,(
    ! [X4] :
      ( k10_relat_1(sK1,k6_subset_1(k2_relat_1(sK1),X4)) = k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,X4))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f106,f191])).

fof(f191,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f138,f145,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f145,plain,(
    r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(backward_demodulation,[],[f143,f137])).

fof(f137,plain,(
    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f69,f76])).

fof(f76,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f143,plain,(
    r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))) ),
    inference(unit_resulting_resolution,[],[f132,f69,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f132,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f185,plain,(
    ! [X0] : r1_tarski(k6_subset_1(k1_relat_1(sK1),X0),k10_relat_1(sK1,k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,X0)))) ),
    inference(backward_demodulation,[],[f141,f184])).

fof(f184,plain,(
    ! [X1] : k9_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X1)) = k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f183,f69])).

fof(f183,plain,(
    ! [X1] :
      ( k9_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X1)) = k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f182,f70])).

fof(f182,plain,(
    ! [X1] :
      ( k9_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X1)) = k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,X1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f175,f71])).

fof(f71,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f175,plain,(
    ! [X1] :
      ( k9_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X1)) = k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,X1))
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f107,f137])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(f141,plain,(
    ! [X0] : r1_tarski(k6_subset_1(k1_relat_1(sK1),X0),k10_relat_1(sK1,k9_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)))) ),
    inference(unit_resulting_resolution,[],[f117,f69,f92])).

fof(f117,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f84,f87])).

fof(f84,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:59:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (1838)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (1846)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (1859)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (1845)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (1868)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (1842)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (1841)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (1863)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (1865)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (1843)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (1864)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (1869)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (1839)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (1866)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (1860)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (1854)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (1856)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (1867)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.47/0.55  % (1844)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.47/0.55  % (1832)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.47/0.55  % (1857)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.47/0.56  % (1850)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.47/0.56  % (1849)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.47/0.56  % (1851)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.47/0.56  % (1861)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.47/0.56  % (1840)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.47/0.56  % (1858)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.47/0.57  % (1849)Refutation not found, incomplete strategy% (1849)------------------------------
% 1.47/0.57  % (1849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (1849)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (1849)Memory used [KB]: 10618
% 1.47/0.57  % (1849)Time elapsed: 0.167 s
% 1.47/0.57  % (1849)------------------------------
% 1.47/0.57  % (1849)------------------------------
% 1.67/0.57  % (1848)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.67/0.57  % (1848)Refutation not found, incomplete strategy% (1848)------------------------------
% 1.67/0.57  % (1848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.57  % (1848)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.57  
% 1.67/0.57  % (1848)Memory used [KB]: 10618
% 1.67/0.57  % (1848)Time elapsed: 0.167 s
% 1.67/0.57  % (1848)------------------------------
% 1.67/0.57  % (1848)------------------------------
% 1.67/0.59  % (1862)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.67/0.59  % (1852)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.67/0.60  % (1862)Refutation not found, incomplete strategy% (1862)------------------------------
% 1.67/0.60  % (1862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.61  % (1862)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.61  
% 1.67/0.61  % (1862)Memory used [KB]: 10746
% 1.67/0.61  % (1862)Time elapsed: 0.167 s
% 1.67/0.61  % (1862)------------------------------
% 1.67/0.61  % (1862)------------------------------
% 2.73/0.74  % (1877)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.73/0.74  % (1866)Refutation found. Thanks to Tanya!
% 2.73/0.74  % SZS status Theorem for theBenchmark
% 2.73/0.74  % SZS output start Proof for theBenchmark
% 2.73/0.74  fof(f1443,plain,(
% 2.73/0.74    $false),
% 2.73/0.74    inference(subsumption_resolution,[],[f1424,f776])).
% 2.73/0.74  fof(f776,plain,(
% 2.73/0.74    r2_hidden(sK3(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k6_subset_1(k1_relat_1(sK1),sK0))),
% 2.73/0.74    inference(unit_resulting_resolution,[],[f152,f391,f134])).
% 2.73/0.74  fof(f134,plain,(
% 2.73/0.74    ( ! [X4,X0,X1] : (r2_hidden(X4,k6_subset_1(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.73/0.74    inference(equality_resolution,[],[f126])).
% 2.73/0.74  fof(f126,plain,(
% 2.73/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k6_subset_1(X0,X1) != X2) )),
% 2.73/0.74    inference(definition_unfolding,[],[f110,f87])).
% 2.73/0.74  fof(f87,plain,(
% 2.73/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.73/0.74    inference(cnf_transformation,[],[f17])).
% 2.73/0.74  fof(f17,axiom,(
% 2.73/0.74    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.73/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.73/0.74  fof(f110,plain,(
% 2.73/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 2.73/0.74    inference(cnf_transformation,[],[f68])).
% 2.73/0.75  % (1879)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.73/0.76  fof(f68,plain,(
% 2.73/0.76    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.73/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f66,f67])).
% 2.73/0.76  fof(f67,plain,(
% 2.73/0.76    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.73/0.76    introduced(choice_axiom,[])).
% 2.73/0.76  fof(f66,plain,(
% 2.73/0.76    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.73/0.76    inference(rectify,[],[f65])).
% 2.73/0.76  fof(f65,plain,(
% 2.73/0.76    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.73/0.76    inference(flattening,[],[f64])).
% 2.73/0.76  fof(f64,plain,(
% 2.73/0.76    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.73/0.76    inference(nnf_transformation,[],[f4])).
% 2.73/0.76  fof(f4,axiom,(
% 2.73/0.76    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.73/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.73/0.76  fof(f391,plain,(
% 2.73/0.76    r2_hidden(sK3(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k1_relat_1(sK1))),
% 2.73/0.76    inference(unit_resulting_resolution,[],[f138,f151,f98])).
% 2.73/0.76  fof(f98,plain,(
% 2.73/0.76    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.73/0.76    inference(cnf_transformation,[],[f62])).
% 2.73/0.76  fof(f62,plain,(
% 2.73/0.76    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.73/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f60,f61])).
% 2.73/0.76  fof(f61,plain,(
% 2.73/0.76    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.73/0.76    introduced(choice_axiom,[])).
% 2.73/0.76  fof(f60,plain,(
% 2.73/0.76    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.73/0.76    inference(rectify,[],[f59])).
% 2.73/0.76  fof(f59,plain,(
% 2.73/0.76    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.73/0.76    inference(nnf_transformation,[],[f42])).
% 2.73/0.76  fof(f42,plain,(
% 2.73/0.76    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.73/0.76    inference(ennf_transformation,[],[f3])).
% 2.73/0.76  fof(f3,axiom,(
% 2.73/0.76    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.73/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.73/0.76  fof(f151,plain,(
% 2.73/0.76    r2_hidden(sK3(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 2.73/0.76    inference(unit_resulting_resolution,[],[f72,f99])).
% 2.73/0.76  fof(f99,plain,(
% 2.73/0.76    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 2.73/0.76    inference(cnf_transformation,[],[f62])).
% 2.73/0.76  fof(f72,plain,(
% 2.73/0.76    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 2.73/0.76    inference(cnf_transformation,[],[f51])).
% 2.73/0.76  fof(f51,plain,(
% 2.73/0.76    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 2.73/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f50])).
% 2.73/0.76  fof(f50,plain,(
% 2.73/0.76    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 2.73/0.76    introduced(choice_axiom,[])).
% 2.73/0.76  fof(f30,plain,(
% 2.73/0.76    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.73/0.76    inference(flattening,[],[f29])).
% 2.73/0.76  fof(f29,plain,(
% 2.73/0.76    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.73/0.76    inference(ennf_transformation,[],[f28])).
% 2.73/0.76  fof(f28,negated_conjecture,(
% 2.73/0.76    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 2.73/0.76    inference(negated_conjecture,[],[f27])).
% 2.73/0.76  fof(f27,conjecture,(
% 2.73/0.76    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 2.73/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 2.73/0.76  fof(f138,plain,(
% 2.73/0.76    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 2.73/0.76    inference(unit_resulting_resolution,[],[f69,f90])).
% 2.73/0.76  fof(f90,plain,(
% 2.73/0.76    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.73/0.76    inference(cnf_transformation,[],[f35])).
% 2.73/0.76  fof(f35,plain,(
% 2.73/0.76    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.73/0.76    inference(ennf_transformation,[],[f20])).
% 2.73/0.76  fof(f20,axiom,(
% 2.73/0.76    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.73/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 2.73/0.76  fof(f69,plain,(
% 2.73/0.76    v1_relat_1(sK1)),
% 2.73/0.76    inference(cnf_transformation,[],[f51])).
% 2.73/0.76  fof(f152,plain,(
% 2.73/0.76    ~r2_hidden(sK3(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),sK0)),
% 2.73/0.76    inference(unit_resulting_resolution,[],[f72,f100])).
% 2.73/0.76  fof(f100,plain,(
% 2.73/0.76    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 2.73/0.76    inference(cnf_transformation,[],[f62])).
% 2.73/0.76  fof(f1424,plain,(
% 2.73/0.76    ~r2_hidden(sK3(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k6_subset_1(k1_relat_1(sK1),sK0))),
% 2.73/0.76    inference(unit_resulting_resolution,[],[f285,f387,f98])).
% 2.73/0.76  fof(f387,plain,(
% 2.73/0.76    ( ! [X0] : (~r2_hidden(sK3(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0),k6_subset_1(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) )),
% 2.73/0.76    inference(unit_resulting_resolution,[],[f151,f135])).
% 2.73/0.76  fof(f135,plain,(
% 2.73/0.76    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 2.73/0.76    inference(equality_resolution,[],[f127])).
% 2.73/0.76  fof(f127,plain,(
% 2.73/0.76    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 2.73/0.76    inference(definition_unfolding,[],[f109,f87])).
% 2.73/0.76  fof(f109,plain,(
% 2.73/0.76    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.73/0.76    inference(cnf_transformation,[],[f68])).
% 2.73/0.76  fof(f285,plain,(
% 2.73/0.76    ( ! [X0] : (r1_tarski(k6_subset_1(k1_relat_1(sK1),X0),k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,X0))))) )),
% 2.73/0.76    inference(backward_demodulation,[],[f185,f284])).
% 2.73/0.76  fof(f284,plain,(
% 2.73/0.76    ( ! [X4] : (k10_relat_1(sK1,k6_subset_1(k2_relat_1(sK1),X4)) = k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,X4))) )),
% 2.73/0.76    inference(subsumption_resolution,[],[f283,f69])).
% 2.73/0.76  fof(f283,plain,(
% 2.73/0.76    ( ! [X4] : (k10_relat_1(sK1,k6_subset_1(k2_relat_1(sK1),X4)) = k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,X4)) | ~v1_relat_1(sK1)) )),
% 2.73/0.76    inference(subsumption_resolution,[],[f268,f70])).
% 2.73/0.76  fof(f70,plain,(
% 2.73/0.76    v1_funct_1(sK1)),
% 2.73/0.76    inference(cnf_transformation,[],[f51])).
% 2.73/0.76  fof(f268,plain,(
% 2.73/0.76    ( ! [X4] : (k10_relat_1(sK1,k6_subset_1(k2_relat_1(sK1),X4)) = k6_subset_1(k1_relat_1(sK1),k10_relat_1(sK1,X4)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 2.73/0.76    inference(superposition,[],[f106,f191])).
% 2.73/0.76  fof(f191,plain,(
% 2.73/0.76    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 2.73/0.76    inference(unit_resulting_resolution,[],[f138,f145,f97])).
% 2.73/0.76  fof(f97,plain,(
% 2.73/0.76    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.73/0.76    inference(cnf_transformation,[],[f58])).
% 2.73/0.76  fof(f58,plain,(
% 2.73/0.76    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.73/0.76    inference(flattening,[],[f57])).
% 2.73/0.76  fof(f57,plain,(
% 2.73/0.76    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.73/0.76    inference(nnf_transformation,[],[f5])).
% 2.73/0.76  fof(f5,axiom,(
% 2.73/0.76    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.73/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.73/0.76  fof(f145,plain,(
% 2.73/0.76    r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1)))),
% 2.73/0.76    inference(backward_demodulation,[],[f143,f137])).
% 2.73/0.76  fof(f137,plain,(
% 2.73/0.76    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)),
% 2.73/0.76    inference(unit_resulting_resolution,[],[f69,f76])).
% 2.73/0.76  fof(f76,plain,(
% 2.73/0.76    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/0.76    inference(cnf_transformation,[],[f31])).
% 2.73/0.76  fof(f31,plain,(
% 2.73/0.76    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.73/0.76    inference(ennf_transformation,[],[f18])).
% 2.73/0.76  fof(f18,axiom,(
% 2.73/0.76    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.73/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 2.73/0.76  fof(f143,plain,(
% 2.73/0.76    r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))))),
% 2.73/0.76    inference(unit_resulting_resolution,[],[f132,f69,f92])).
% 2.73/0.76  fof(f92,plain,(
% 2.73/0.76    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.73/0.76    inference(cnf_transformation,[],[f38])).
% 2.73/0.76  fof(f38,plain,(
% 2.73/0.76    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.73/0.76    inference(flattening,[],[f37])).
% 2.73/0.76  fof(f37,plain,(
% 2.73/0.76    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.73/0.76    inference(ennf_transformation,[],[f26])).
% 2.73/0.76  fof(f26,axiom,(
% 2.73/0.76    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.73/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 2.73/0.76  fof(f132,plain,(
% 2.73/0.76    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.73/0.76    inference(equality_resolution,[],[f96])).
% 2.73/0.76  fof(f96,plain,(
% 2.73/0.76    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.73/0.76    inference(cnf_transformation,[],[f58])).
% 2.73/0.76  fof(f106,plain,(
% 2.73/0.76    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.73/0.76    inference(cnf_transformation,[],[f47])).
% 2.73/0.76  fof(f47,plain,(
% 2.73/0.76    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.73/0.76    inference(flattening,[],[f46])).
% 2.73/0.76  fof(f46,plain,(
% 2.73/0.76    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.73/0.76    inference(ennf_transformation,[],[f24])).
% 2.73/0.76  fof(f24,axiom,(
% 2.73/0.76    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 2.73/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 2.73/0.76  fof(f185,plain,(
% 2.73/0.76    ( ! [X0] : (r1_tarski(k6_subset_1(k1_relat_1(sK1),X0),k10_relat_1(sK1,k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,X0))))) )),
% 2.73/0.76    inference(backward_demodulation,[],[f141,f184])).
% 2.73/0.76  fof(f184,plain,(
% 2.73/0.76    ( ! [X1] : (k9_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X1)) = k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,X1))) )),
% 2.73/0.76    inference(subsumption_resolution,[],[f183,f69])).
% 2.73/0.76  fof(f183,plain,(
% 2.73/0.76    ( ! [X1] : (k9_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X1)) = k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 2.73/0.76    inference(subsumption_resolution,[],[f182,f70])).
% 2.73/0.76  fof(f182,plain,(
% 2.73/0.76    ( ! [X1] : (k9_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X1)) = k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,X1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 2.73/0.76    inference(subsumption_resolution,[],[f175,f71])).
% 2.73/0.76  fof(f71,plain,(
% 2.73/0.76    v2_funct_1(sK1)),
% 2.73/0.76    inference(cnf_transformation,[],[f51])).
% 2.73/0.76  fof(f175,plain,(
% 2.73/0.76    ( ! [X1] : (k9_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X1)) = k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,X1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 2.73/0.76    inference(superposition,[],[f107,f137])).
% 2.73/0.76  fof(f107,plain,(
% 2.73/0.76    ( ! [X2,X0,X1] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.73/0.76    inference(cnf_transformation,[],[f49])).
% 2.73/0.76  fof(f49,plain,(
% 2.73/0.76    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.73/0.76    inference(flattening,[],[f48])).
% 2.73/0.76  fof(f48,plain,(
% 2.73/0.76    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.73/0.76    inference(ennf_transformation,[],[f23])).
% 2.73/0.76  fof(f23,axiom,(
% 2.73/0.76    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.73/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
% 2.73/0.76  fof(f141,plain,(
% 2.73/0.76    ( ! [X0] : (r1_tarski(k6_subset_1(k1_relat_1(sK1),X0),k10_relat_1(sK1,k9_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))))) )),
% 2.73/0.76    inference(unit_resulting_resolution,[],[f117,f69,f92])).
% 2.73/0.76  fof(f117,plain,(
% 2.73/0.76    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 2.73/0.76    inference(definition_unfolding,[],[f84,f87])).
% 2.73/0.76  fof(f84,plain,(
% 2.73/0.76    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.73/0.76    inference(cnf_transformation,[],[f10])).
% 2.73/0.76  fof(f10,axiom,(
% 2.73/0.76    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.73/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.73/0.76  % SZS output end Proof for theBenchmark
% 2.73/0.76  % (1866)------------------------------
% 2.73/0.76  % (1866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.73/0.76  % (1866)Termination reason: Refutation
% 2.73/0.76  
% 2.73/0.76  % (1866)Memory used [KB]: 12025
% 2.73/0.76  % (1866)Time elapsed: 0.333 s
% 2.73/0.76  % (1866)------------------------------
% 2.73/0.76  % (1866)------------------------------
% 2.73/0.77  % (1830)Success in time 0.402 s
%------------------------------------------------------------------------------
