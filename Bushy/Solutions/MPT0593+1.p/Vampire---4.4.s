%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t197_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:57 EDT 2019

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   43 (  89 expanded)
%              Number of leaves         :    9 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  105 ( 309 expanded)
%              Number of equality atoms :   41 ( 159 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f60,f78])).

fof(f78,plain,(
    ~ spl3_0 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | ~ spl3_0 ),
    inference(subsumption_resolution,[],[f71,f68])).

fof(f68,plain,(
    o_0_0_xboole_0 = sK0 ),
    inference(resolution,[],[f64,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f38,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t197_relat_1.p',d2_xboole_0)).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t197_relat_1.p',t6_boole)).

fof(f64,plain,(
    v1_xboole_0(sK0) ),
    inference(global_subsumption,[],[f32,f37,f63])).

fof(f63,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f40,f48])).

fof(f48,plain,(
    k2_relat_1(sK0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f34,plain,(
    k2_relat_1(sK0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK0 != sK1
    & k2_relat_1(sK1) = k1_xboole_0
    & k2_relat_1(sK0) = k1_xboole_0
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & k2_relat_1(X1) = k1_xboole_0
            & k2_relat_1(X0) = k1_xboole_0
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & k2_relat_1(X1) = k1_xboole_0
          & k2_relat_1(sK0) = k1_xboole_0
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k2_relat_1(X1) = k1_xboole_0
          & k2_relat_1(X0) = k1_xboole_0
          & v1_relat_1(X1) )
     => ( sK1 != X0
        & k2_relat_1(sK1) = k1_xboole_0
        & k2_relat_1(X0) = k1_xboole_0
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k2_relat_1(X1) = k1_xboole_0
          & k2_relat_1(X0) = k1_xboole_0
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k2_relat_1(X1) = k1_xboole_0
          & k2_relat_1(X0) = k1_xboole_0
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( k2_relat_1(X1) = k1_xboole_0
                & k2_relat_1(X0) = k1_xboole_0 )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k2_relat_1(X1) = k1_xboole_0
              & k2_relat_1(X0) = k1_xboole_0 )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t197_relat_1.p',t197_relat_1)).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t197_relat_1.p',fc9_relat_1)).

fof(f37,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t197_relat_1.p',dt_o_0_0_xboole_0)).

fof(f32,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,
    ( o_0_0_xboole_0 != sK0
    | ~ spl3_0 ),
    inference(backward_demodulation,[],[f66,f36])).

fof(f36,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl3_0 ),
    inference(resolution,[],[f54,f49])).

fof(f54,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_0
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f60,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f37,f57])).

fof(f57,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_3
  <=> ~ v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f58,plain,
    ( spl3_0
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f51,f56,f53])).

fof(f51,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | v1_xboole_0(sK1) ),
    inference(global_subsumption,[],[f33,f50])).

fof(f50,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f40,f47])).

fof(f47,plain,(
    k2_relat_1(sK1) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f35,plain,(
    k2_relat_1(sK1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
