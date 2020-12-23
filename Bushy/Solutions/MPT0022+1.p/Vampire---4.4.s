%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t15_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:22 EDT 2019

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   37 (  59 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 ( 100 expanded)
%              Number of equality atoms :   28 (  62 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f64,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f47,f63])).

fof(f63,plain,(
    ~ spl2_0 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | ~ spl2_0 ),
    inference(subsumption_resolution,[],[f34,f54])).

fof(f54,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl2_0 ),
    inference(superposition,[],[f53,f36])).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f27,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t15_xboole_1.p',d2_xboole_0)).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t15_xboole_1.p',t1_boole)).

fof(f53,plain,
    ( k2_xboole_0(sK0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl2_0 ),
    inference(backward_demodulation,[],[f51,f35])).

fof(f35,plain,(
    k2_xboole_0(sK0,sK1) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f24,f27])).

fof(f24,plain,(
    k2_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_xboole_0 != sK0
    & k2_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 != X0
        & k2_xboole_0(X0,X1) = k1_xboole_0 )
   => ( k1_xboole_0 != sK0
      & k2_xboole_0(sK0,sK1) = k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != X0
      & k2_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = k1_xboole_0
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = k1_xboole_0
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t15_xboole_1.p',t15_xboole_1)).

fof(f51,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl2_0 ),
    inference(resolution,[],[f41,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t15_xboole_1.p',t6_boole)).

fof(f41,plain,
    ( v1_xboole_0(sK1)
    | ~ spl2_0 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_0
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f34,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f25,f27])).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f46])).

fof(f46,plain,
    ( $false
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f26,f44])).

fof(f44,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_3
  <=> ~ v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f26,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t15_xboole_1.p',dt_o_0_0_xboole_0)).

fof(f45,plain,
    ( spl2_0
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f38,f43,f40])).

fof(f38,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f32,f35])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t15_xboole_1.p',fc5_xboole_0)).
%------------------------------------------------------------------------------
