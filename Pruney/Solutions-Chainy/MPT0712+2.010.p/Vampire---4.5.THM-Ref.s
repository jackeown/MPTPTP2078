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
% DateTime   : Thu Dec  3 12:54:44 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 131 expanded)
%              Number of leaves         :   14 (  31 expanded)
%              Depth                    :   17
%              Number of atoms          :  227 ( 396 expanded)
%              Number of equality atoms :   35 (  45 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f914,plain,(
    $false ),
    inference(subsumption_resolution,[],[f913,f37])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

fof(f913,plain,(
    ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f911,f221])).

fof(f221,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f220,f37])).

fof(f220,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f219,f38])).

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f219,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f213,f61])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f213,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1(sK1,sK0)),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f74,f120])).

fof(f120,plain,(
    ! [X4,X3] :
      ( k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k1_tarski(X4))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(forward_demodulation,[],[f119,f43])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f119,plain,(
    ! [X4,X3] :
      ( k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X4,X3] :
      ( k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ r2_hidden(X4,k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f55,f43])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

fof(f74,plain,(
    ~ r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f73,f37])).

fof(f73,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f39,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f39,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f911,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f858,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v4_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f49,f61])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f858,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK1,X0)
      | r2_hidden(sK0,X0) ) ),
    inference(resolution,[],[f857,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f59,f43])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f857,plain,(
    ! [X80] :
      ( ~ r1_xboole_0(k1_tarski(sK0),X80)
      | ~ v4_relat_1(sK1,X80) ) ),
    inference(subsumption_resolution,[],[f856,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f856,plain,(
    ! [X80] :
      ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK1,sK0)))
      | ~ r1_xboole_0(k1_tarski(sK0),X80)
      | ~ v4_relat_1(sK1,X80) ) ),
    inference(forward_demodulation,[],[f855,f41])).

fof(f41,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f855,plain,(
    ! [X80] :
      ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(sK1,sK0)))
      | ~ r1_xboole_0(k1_tarski(sK0),X80)
      | ~ v4_relat_1(sK1,X80) ) ),
    inference(subsumption_resolution,[],[f827,f37])).

fof(f827,plain,(
    ! [X80] :
      ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(sK1,sK0)))
      | ~ v1_relat_1(sK1)
      | ~ r1_xboole_0(k1_tarski(sK0),X80)
      | ~ v4_relat_1(sK1,X80) ) ),
    inference(superposition,[],[f39,f302])).

fof(f302,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = k7_relat_1(X3,X4)
      | ~ v1_relat_1(X3)
      | ~ r1_xboole_0(X4,X5)
      | ~ v4_relat_1(X3,X5) ) ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_relat_1(X3)
      | k1_xboole_0 = k7_relat_1(X3,X4)
      | ~ r1_xboole_0(X4,X5)
      | ~ v4_relat_1(X3,X5)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f203,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

fof(f203,plain,(
    ! [X4,X2,X3] :
      ( ~ v4_relat_1(k7_relat_1(X4,X2),X3)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = k7_relat_1(X4,X2)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(subsumption_resolution,[],[f196,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f196,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = k7_relat_1(X4,X2)
      | ~ v4_relat_1(k7_relat_1(X4,X2),X3)
      | ~ v1_relat_1(k7_relat_1(X4,X2)) ) ),
    inference(resolution,[],[f107,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f107,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1(X3,X4)),X5)
      | ~ r1_xboole_0(X4,X5)
      | ~ v1_relat_1(X3)
      | k1_xboole_0 = k7_relat_1(X3,X4) ) ),
    inference(subsumption_resolution,[],[f99,f45])).

fof(f99,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = k7_relat_1(X3,X4)
      | ~ r1_xboole_0(X4,X5)
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(k1_relat_1(k7_relat_1(X3,X4)),X5)
      | ~ v1_relat_1(k7_relat_1(X3,X4)) ) ),
    inference(superposition,[],[f54,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (23720)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (23718)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (23723)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (23714)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (23739)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.51  % (23731)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (23736)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (23730)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (23737)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (23715)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (23719)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (23716)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (23729)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (23732)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (23717)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (23728)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (23728)Refutation not found, incomplete strategy% (23728)------------------------------
% 0.21/0.53  % (23728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23728)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23728)Memory used [KB]: 1663
% 0.21/0.53  % (23728)Time elapsed: 0.123 s
% 0.21/0.53  % (23728)------------------------------
% 0.21/0.53  % (23728)------------------------------
% 0.21/0.53  % (23721)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (23742)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (23735)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (23742)Refutation not found, incomplete strategy% (23742)------------------------------
% 0.21/0.53  % (23742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23722)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (23743)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (23743)Refutation not found, incomplete strategy% (23743)------------------------------
% 0.21/0.53  % (23743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23727)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (23743)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23743)Memory used [KB]: 1663
% 0.21/0.53  % (23743)Time elapsed: 0.002 s
% 0.21/0.53  % (23743)------------------------------
% 0.21/0.53  % (23743)------------------------------
% 0.21/0.54  % (23740)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (23724)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (23734)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (23724)Refutation not found, incomplete strategy% (23724)------------------------------
% 0.21/0.54  % (23724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23730)Refutation not found, incomplete strategy% (23730)------------------------------
% 0.21/0.54  % (23730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23726)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.42/0.54  % (23738)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.42/0.54  % (23730)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (23730)Memory used [KB]: 10618
% 1.42/0.54  % (23733)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.42/0.54  % (23730)Time elapsed: 0.129 s
% 1.42/0.54  % (23730)------------------------------
% 1.42/0.54  % (23730)------------------------------
% 1.42/0.55  % (23724)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (23724)Memory used [KB]: 10746
% 1.42/0.55  % (23724)Time elapsed: 0.131 s
% 1.42/0.55  % (23724)------------------------------
% 1.42/0.55  % (23724)------------------------------
% 1.42/0.55  % (23738)Refutation not found, incomplete strategy% (23738)------------------------------
% 1.42/0.55  % (23738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (23738)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (23738)Memory used [KB]: 10618
% 1.42/0.55  % (23738)Time elapsed: 0.140 s
% 1.42/0.55  % (23738)------------------------------
% 1.42/0.55  % (23738)------------------------------
% 1.42/0.55  % (23725)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.42/0.55  % (23742)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (23742)Memory used [KB]: 10746
% 1.42/0.55  % (23742)Time elapsed: 0.122 s
% 1.42/0.55  % (23742)------------------------------
% 1.42/0.55  % (23742)------------------------------
% 1.42/0.55  % (23741)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.42/0.56  % (23741)Refutation not found, incomplete strategy% (23741)------------------------------
% 1.42/0.56  % (23741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.56  % (23741)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.56  
% 1.59/0.56  % (23741)Memory used [KB]: 6140
% 1.59/0.56  % (23741)Time elapsed: 0.138 s
% 1.59/0.56  % (23741)------------------------------
% 1.59/0.56  % (23741)------------------------------
% 1.59/0.58  % (23723)Refutation found. Thanks to Tanya!
% 1.59/0.58  % SZS status Theorem for theBenchmark
% 1.59/0.58  % SZS output start Proof for theBenchmark
% 1.59/0.58  fof(f914,plain,(
% 1.59/0.58    $false),
% 1.59/0.58    inference(subsumption_resolution,[],[f913,f37])).
% 1.59/0.58  fof(f37,plain,(
% 1.59/0.58    v1_relat_1(sK1)),
% 1.59/0.58    inference(cnf_transformation,[],[f33])).
% 1.59/0.58  fof(f33,plain,(
% 1.59/0.58    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.59/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f32])).
% 1.59/0.58  fof(f32,plain,(
% 1.59/0.58    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.59/0.58    introduced(choice_axiom,[])).
% 1.59/0.58  fof(f19,plain,(
% 1.59/0.58    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.59/0.58    inference(flattening,[],[f18])).
% 1.59/0.58  fof(f18,plain,(
% 1.59/0.58    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.59/0.58    inference(ennf_transformation,[],[f17])).
% 1.59/0.58  fof(f17,negated_conjecture,(
% 1.59/0.58    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 1.59/0.58    inference(negated_conjecture,[],[f16])).
% 1.59/0.58  fof(f16,conjecture,(
% 1.59/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).
% 1.59/0.58  fof(f913,plain,(
% 1.59/0.58    ~v1_relat_1(sK1)),
% 1.59/0.58    inference(subsumption_resolution,[],[f911,f221])).
% 1.59/0.58  fof(f221,plain,(
% 1.59/0.58    ~r2_hidden(sK0,k1_relat_1(sK1))),
% 1.59/0.58    inference(subsumption_resolution,[],[f220,f37])).
% 1.59/0.58  fof(f220,plain,(
% 1.59/0.58    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.59/0.58    inference(subsumption_resolution,[],[f219,f38])).
% 1.59/0.58  fof(f38,plain,(
% 1.59/0.58    v1_funct_1(sK1)),
% 1.59/0.58    inference(cnf_transformation,[],[f33])).
% 1.59/0.58  fof(f219,plain,(
% 1.59/0.58    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.59/0.58    inference(subsumption_resolution,[],[f213,f61])).
% 1.59/0.58  fof(f61,plain,(
% 1.59/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.59/0.58    inference(equality_resolution,[],[f51])).
% 1.59/0.58  fof(f51,plain,(
% 1.59/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.59/0.58    inference(cnf_transformation,[],[f36])).
% 1.59/0.58  fof(f36,plain,(
% 1.59/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.59/0.58    inference(flattening,[],[f35])).
% 1.59/0.58  fof(f35,plain,(
% 1.59/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.59/0.58    inference(nnf_transformation,[],[f1])).
% 1.59/0.58  fof(f1,axiom,(
% 1.59/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.59/0.58  fof(f213,plain,(
% 1.59/0.58    ~r1_tarski(k1_tarski(k1_funct_1(sK1,sK0)),k1_tarski(k1_funct_1(sK1,sK0))) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.59/0.58    inference(superposition,[],[f74,f120])).
% 1.59/0.58  fof(f120,plain,(
% 1.59/0.58    ( ! [X4,X3] : (k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k1_tarski(X4)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 1.59/0.58    inference(forward_demodulation,[],[f119,f43])).
% 1.59/0.58  fof(f43,plain,(
% 1.59/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f3])).
% 1.59/0.58  fof(f3,axiom,(
% 1.59/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.59/0.58  fof(f119,plain,(
% 1.59/0.58    ( ! [X4,X3] : (k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 1.59/0.58    inference(duplicate_literal_removal,[],[f115])).
% 1.59/0.58  fof(f115,plain,(
% 1.59/0.58    ( ! [X4,X3] : (k1_tarski(k1_funct_1(X3,X4)) = k9_relat_1(X3,k2_tarski(X4,X4)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~r2_hidden(X4,k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 1.59/0.58    inference(superposition,[],[f55,f43])).
% 1.59/0.58  fof(f55,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f28])).
% 1.59/0.58  fof(f28,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.59/0.58    inference(flattening,[],[f27])).
% 1.59/0.58  fof(f27,plain,(
% 1.59/0.58    ! [X0,X1,X2] : ((k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.59/0.58    inference(ennf_transformation,[],[f15])).
% 1.59/0.58  fof(f15,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).
% 1.59/0.58  fof(f74,plain,(
% 1.59/0.58    ~r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0)))),
% 1.59/0.58    inference(subsumption_resolution,[],[f73,f37])).
% 1.59/0.58  fof(f73,plain,(
% 1.59/0.58    ~r1_tarski(k9_relat_1(sK1,k1_tarski(sK0)),k1_tarski(k1_funct_1(sK1,sK0))) | ~v1_relat_1(sK1)),
% 1.59/0.58    inference(superposition,[],[f39,f46])).
% 1.59/0.58  fof(f46,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f21])).
% 1.59/0.58  fof(f21,plain,(
% 1.59/0.58    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.59/0.58    inference(ennf_transformation,[],[f11])).
% 1.59/0.58  fof(f11,axiom,(
% 1.59/0.58    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.59/0.58  fof(f39,plain,(
% 1.59/0.58    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 1.59/0.58    inference(cnf_transformation,[],[f33])).
% 1.59/0.58  fof(f911,plain,(
% 1.59/0.58    r2_hidden(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.59/0.58    inference(resolution,[],[f858,f64])).
% 1.59/0.58  fof(f64,plain,(
% 1.59/0.58    ( ! [X0] : (v4_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.59/0.58    inference(resolution,[],[f49,f61])).
% 1.59/0.58  fof(f49,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f34])).
% 1.59/0.58  fof(f34,plain,(
% 1.59/0.58    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.59/0.58    inference(nnf_transformation,[],[f24])).
% 1.59/0.58  fof(f24,plain,(
% 1.59/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.59/0.58    inference(ennf_transformation,[],[f8])).
% 1.59/0.58  fof(f8,axiom,(
% 1.59/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.59/0.58  fof(f858,plain,(
% 1.59/0.58    ( ! [X0] : (~v4_relat_1(sK1,X0) | r2_hidden(sK0,X0)) )),
% 1.59/0.58    inference(resolution,[],[f857,f96])).
% 1.59/0.58  fof(f96,plain,(
% 1.59/0.58    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.59/0.58    inference(duplicate_literal_removal,[],[f95])).
% 1.59/0.58  fof(f95,plain,(
% 1.59/0.58    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1) | r2_hidden(X0,X1)) )),
% 1.59/0.58    inference(superposition,[],[f59,f43])).
% 1.59/0.58  fof(f59,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f31])).
% 1.59/0.58  fof(f31,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 1.59/0.58    inference(ennf_transformation,[],[f7])).
% 1.59/0.58  fof(f7,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 1.59/0.58  fof(f857,plain,(
% 1.59/0.58    ( ! [X80] : (~r1_xboole_0(k1_tarski(sK0),X80) | ~v4_relat_1(sK1,X80)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f856,f42])).
% 1.59/0.58  fof(f42,plain,(
% 1.59/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f2])).
% 1.59/0.58  fof(f2,axiom,(
% 1.59/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.59/0.58  fof(f856,plain,(
% 1.59/0.58    ( ! [X80] : (~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(sK1,sK0))) | ~r1_xboole_0(k1_tarski(sK0),X80) | ~v4_relat_1(sK1,X80)) )),
% 1.59/0.58    inference(forward_demodulation,[],[f855,f41])).
% 1.59/0.58  fof(f41,plain,(
% 1.59/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.59/0.58    inference(cnf_transformation,[],[f13])).
% 1.59/0.58  fof(f13,axiom,(
% 1.59/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.59/0.58  fof(f855,plain,(
% 1.59/0.58    ( ! [X80] : (~r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(sK1,sK0))) | ~r1_xboole_0(k1_tarski(sK0),X80) | ~v4_relat_1(sK1,X80)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f827,f37])).
% 1.59/0.58  fof(f827,plain,(
% 1.59/0.58    ( ! [X80] : (~r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1(sK1,sK0))) | ~v1_relat_1(sK1) | ~r1_xboole_0(k1_tarski(sK0),X80) | ~v4_relat_1(sK1,X80)) )),
% 1.59/0.58    inference(superposition,[],[f39,f302])).
% 1.59/0.58  fof(f302,plain,(
% 1.59/0.58    ( ! [X4,X5,X3] : (k1_xboole_0 = k7_relat_1(X3,X4) | ~v1_relat_1(X3) | ~r1_xboole_0(X4,X5) | ~v4_relat_1(X3,X5)) )),
% 1.59/0.58    inference(duplicate_literal_removal,[],[f294])).
% 1.59/0.58  fof(f294,plain,(
% 1.59/0.58    ( ! [X4,X5,X3] : (~v1_relat_1(X3) | k1_xboole_0 = k7_relat_1(X3,X4) | ~r1_xboole_0(X4,X5) | ~v4_relat_1(X3,X5) | ~v1_relat_1(X3)) )),
% 1.59/0.58    inference(resolution,[],[f203,f58])).
% 1.59/0.58  fof(f58,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X1) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f30])).
% 1.59/0.58  fof(f30,plain,(
% 1.59/0.58    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 1.59/0.58    inference(flattening,[],[f29])).
% 1.59/0.58  fof(f29,plain,(
% 1.59/0.58    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 1.59/0.58    inference(ennf_transformation,[],[f10])).
% 1.59/0.58  fof(f10,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).
% 1.59/0.58  fof(f203,plain,(
% 1.59/0.58    ( ! [X4,X2,X3] : (~v4_relat_1(k7_relat_1(X4,X2),X3) | ~v1_relat_1(X4) | k1_xboole_0 = k7_relat_1(X4,X2) | ~r1_xboole_0(X2,X3)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f196,f45])).
% 1.59/0.58  fof(f45,plain,(
% 1.59/0.58    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f20])).
% 1.59/0.58  fof(f20,plain,(
% 1.59/0.58    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.59/0.58    inference(ennf_transformation,[],[f9])).
% 1.59/0.58  fof(f9,axiom,(
% 1.59/0.58    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.59/0.58  fof(f196,plain,(
% 1.59/0.58    ( ! [X4,X2,X3] : (~r1_xboole_0(X2,X3) | ~v1_relat_1(X4) | k1_xboole_0 = k7_relat_1(X4,X2) | ~v4_relat_1(k7_relat_1(X4,X2),X3) | ~v1_relat_1(k7_relat_1(X4,X2))) )),
% 1.59/0.58    inference(resolution,[],[f107,f48])).
% 1.59/0.58  fof(f48,plain,(
% 1.59/0.58    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f34])).
% 1.59/0.58  fof(f107,plain,(
% 1.59/0.58    ( ! [X4,X5,X3] : (~r1_tarski(k1_relat_1(k7_relat_1(X3,X4)),X5) | ~r1_xboole_0(X4,X5) | ~v1_relat_1(X3) | k1_xboole_0 = k7_relat_1(X3,X4)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f99,f45])).
% 1.59/0.58  fof(f99,plain,(
% 1.59/0.58    ( ! [X4,X5,X3] : (k1_xboole_0 = k7_relat_1(X3,X4) | ~r1_xboole_0(X4,X5) | ~v1_relat_1(X3) | ~r1_tarski(k1_relat_1(k7_relat_1(X3,X4)),X5) | ~v1_relat_1(k7_relat_1(X3,X4))) )),
% 1.59/0.58    inference(superposition,[],[f54,f47])).
% 1.59/0.58  fof(f47,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f23])).
% 1.59/0.58  fof(f23,plain,(
% 1.59/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.59/0.58    inference(flattening,[],[f22])).
% 1.59/0.58  fof(f22,plain,(
% 1.59/0.58    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.59/0.58    inference(ennf_transformation,[],[f14])).
% 1.59/0.58  fof(f14,axiom,(
% 1.59/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 1.59/0.58  fof(f54,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f26])).
% 1.59/0.58  fof(f26,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 1.59/0.58    inference(flattening,[],[f25])).
% 1.59/0.58  fof(f25,plain,(
% 1.59/0.58    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.59/0.58    inference(ennf_transformation,[],[f12])).
% 1.59/0.58  fof(f12,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
% 1.59/0.58  % SZS output end Proof for theBenchmark
% 1.59/0.58  % (23723)------------------------------
% 1.59/0.58  % (23723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (23723)Termination reason: Refutation
% 1.59/0.58  
% 1.59/0.58  % (23723)Memory used [KB]: 2046
% 1.59/0.58  % (23723)Time elapsed: 0.173 s
% 1.59/0.58  % (23723)------------------------------
% 1.59/0.58  % (23723)------------------------------
% 1.59/0.58  % (23713)Success in time 0.221 s
%------------------------------------------------------------------------------
