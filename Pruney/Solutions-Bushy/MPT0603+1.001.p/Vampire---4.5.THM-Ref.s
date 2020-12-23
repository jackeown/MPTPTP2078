%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0603+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:17 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   36 (  72 expanded)
%              Number of leaves         :    7 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :   72 ( 162 expanded)
%              Number of equality atoms :   22 (  53 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(subsumption_resolution,[],[f126,f29])).

fof(f29,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f21,f27])).

fof(f27,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unit_resulting_resolution,[],[f21,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f21,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f126,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f125,f37])).

fof(f37,plain,(
    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f33,f22])).

fof(f33,plain,(
    v1_xboole_0(k7_relat_1(sK2,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f18,f29,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc16_relat_1)).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    & r1_xboole_0(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
        & r1_xboole_0(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
      & r1_xboole_0(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_xboole_0(X0,X1)
         => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(f125,plain,(
    ~ v1_xboole_0(k7_relat_1(sK2,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f124,f57])).

fof(f57,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f19,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f19,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f124,plain,(
    ~ v1_xboole_0(k7_relat_1(sK2,k3_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f32,f119])).

fof(f119,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f18,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f32,plain,(
    ~ v1_xboole_0(k7_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f20,f22])).

fof(f20,plain,(
    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
