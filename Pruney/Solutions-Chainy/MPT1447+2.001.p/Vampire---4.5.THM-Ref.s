%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 912 expanded)
%              Number of leaves         :   19 ( 247 expanded)
%              Depth                    :   18
%              Number of atoms          :  965 (8391 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f422,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f76,f102,f185,f192,f198,f210,f277,f283,f301,f319,f340,f350,f394,f403,f421])).

fof(f421,plain,
    ( ~ spl2_2
    | spl2_3 ),
    inference(avatar_contradiction_clause,[],[f420])).

fof(f420,plain,
    ( $false
    | ~ spl2_2
    | spl2_3 ),
    inference(subsumption_resolution,[],[f410,f71])).

fof(f71,plain,
    ( ~ v13_lattices(sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl2_3
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f410,plain,
    ( v13_lattices(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f409,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ v15_lattices(k7_filter_1(sK0,sK1))
      | ~ v15_lattices(sK1)
      | ~ v15_lattices(sK0) )
    & ( v15_lattices(k7_filter_1(sK0,sK1))
      | ( v15_lattices(sK1)
        & v15_lattices(sK0) ) )
    & l3_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1)
    & l3_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v15_lattices(k7_filter_1(X0,X1))
              | ~ v15_lattices(X1)
              | ~ v15_lattices(X0) )
            & ( v15_lattices(k7_filter_1(X0,X1))
              | ( v15_lattices(X1)
                & v15_lattices(X0) ) )
            & l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v15_lattices(k7_filter_1(sK0,X1))
            | ~ v15_lattices(X1)
            | ~ v15_lattices(sK0) )
          & ( v15_lattices(k7_filter_1(sK0,X1))
            | ( v15_lattices(X1)
              & v15_lattices(sK0) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ( ~ v15_lattices(k7_filter_1(sK0,X1))
          | ~ v15_lattices(X1)
          | ~ v15_lattices(sK0) )
        & ( v15_lattices(k7_filter_1(sK0,X1))
          | ( v15_lattices(X1)
            & v15_lattices(sK0) ) )
        & l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ( ~ v15_lattices(k7_filter_1(sK0,sK1))
        | ~ v15_lattices(sK1)
        | ~ v15_lattices(sK0) )
      & ( v15_lattices(k7_filter_1(sK0,sK1))
        | ( v15_lattices(sK1)
          & v15_lattices(sK0) ) )
      & l3_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v15_lattices(k7_filter_1(X0,X1))
            | ~ v15_lattices(X1)
            | ~ v15_lattices(X0) )
          & ( v15_lattices(k7_filter_1(X0,X1))
            | ( v15_lattices(X1)
              & v15_lattices(X0) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v15_lattices(k7_filter_1(X0,X1))
            | ~ v15_lattices(X1)
            | ~ v15_lattices(X0) )
          & ( v15_lattices(k7_filter_1(X0,X1))
            | ( v15_lattices(X1)
              & v15_lattices(X0) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( v15_lattices(X1)
              & v15_lattices(X0) )
          <~> v15_lattices(k7_filter_1(X0,X1)) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( v15_lattices(X1)
              & v15_lattices(X0) )
          <~> v15_lattices(k7_filter_1(X0,X1)) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l3_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1) )
           => ( ( v15_lattices(X1)
                & v15_lattices(X0) )
            <=> v15_lattices(k7_filter_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( v15_lattices(X1)
              & v15_lattices(X0) )
          <=> v15_lattices(k7_filter_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_filter_1)).

fof(f409,plain,
    ( v2_struct_0(sK0)
    | v13_lattices(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f408,f35])).

fof(f35,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f408,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | v13_lattices(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f407,f36])).

fof(f36,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f407,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | v13_lattices(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f406,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f406,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | v13_lattices(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f405,f38])).

fof(f38,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f405,plain,
    ( ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | v13_lattices(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f352,f39])).

fof(f39,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f352,plain,
    ( ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | v13_lattices(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f63,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | v13_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f86,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_filter_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f85,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ~ v2_struct_0(k7_filter_1(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v3_lattices(k7_filter_1(X0,X1))
        & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_filter_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(resolution,[],[f52,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v15_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v14_lattices(X0)
          & v13_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_lattices)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v13_lattices(k7_filter_1(X0,X1))
      | v13_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v13_lattices(X1)
                & v13_lattices(X0) )
              | ~ v13_lattices(k7_filter_1(X0,X1)) )
            & ( v13_lattices(k7_filter_1(X0,X1))
              | ~ v13_lattices(X1)
              | ~ v13_lattices(X0) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v13_lattices(X1)
                & v13_lattices(X0) )
              | ~ v13_lattices(k7_filter_1(X0,X1)) )
            & ( v13_lattices(k7_filter_1(X0,X1))
              | ~ v13_lattices(X1)
              | ~ v13_lattices(X0) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_lattices(X1)
              & v13_lattices(X0) )
          <=> v13_lattices(k7_filter_1(X0,X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_lattices(X1)
              & v13_lattices(X0) )
          <=> v13_lattices(k7_filter_1(X0,X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( v13_lattices(X1)
              & v13_lattices(X0) )
          <=> v13_lattices(k7_filter_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_filter_1)).

fof(f63,plain,
    ( v15_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_2
  <=> v15_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f403,plain,
    ( ~ spl2_2
    | ~ spl2_14
    | spl2_15
    | spl2_16 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_14
    | spl2_15
    | spl2_16 ),
    inference(subsumption_resolution,[],[f401,f263])).

fof(f263,plain,
    ( l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl2_14
  <=> l3_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f401,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_2
    | spl2_15
    | spl2_16 ),
    inference(subsumption_resolution,[],[f400,f267])).

fof(f267,plain,
    ( ~ v2_struct_0(k7_filter_1(sK0,sK1))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl2_15
  <=> v2_struct_0(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f400,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_2
    | spl2_16 ),
    inference(subsumption_resolution,[],[f399,f63])).

fof(f399,plain,
    ( ~ v15_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | spl2_16 ),
    inference(resolution,[],[f272,f46])).

fof(f272,plain,
    ( ~ v13_lattices(k7_filter_1(sK0,sK1))
    | spl2_16 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl2_16
  <=> v13_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f394,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f379,f373])).

fof(f373,plain,
    ( ~ v13_lattices(sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f372,f39])).

fof(f372,plain,
    ( ~ v13_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f367,f37])).

fof(f367,plain,
    ( ~ v13_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f366,f125])).

fof(f125,plain,
    ( v14_lattices(sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl2_6
  <=> v14_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f366,plain,
    ( ~ v14_lattices(sK1)
    | ~ v13_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f365,f44])).

% (30535)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% (30528)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% (30527)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% (30536)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
fof(f44,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v13_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v14_lattices(X0)
      | ~ v13_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v14_lattices(X0)
      | ~ v13_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v14_lattices(X0)
          & v13_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v15_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_lattices)).

fof(f365,plain,
    ( ~ v15_lattices(sK1)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f351,f63])).

fof(f351,plain,
    ( ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v15_lattices(sK1)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f42,f59])).

fof(f59,plain,
    ( v15_lattices(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_1
  <=> v15_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f42,plain,
    ( ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v15_lattices(sK1)
    | ~ v15_lattices(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f379,plain,
    ( v13_lattices(sK1)
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f378,f34])).

fof(f378,plain,
    ( v13_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f377,f35])).

fof(f377,plain,
    ( v13_lattices(sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f376,f36])).

fof(f376,plain,
    ( v13_lattices(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f375,f37])).

fof(f375,plain,
    ( v13_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f374,f38])).

fof(f374,plain,
    ( v13_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f355,f39])).

fof(f355,plain,
    ( v13_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_16 ),
    inference(resolution,[],[f271,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v13_lattices(k7_filter_1(X0,X1))
      | v13_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f271,plain,
    ( v13_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f270])).

fof(f350,plain,(
    ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f348,f34])).

fof(f348,plain,
    ( v2_struct_0(sK0)
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f347,f36])).

fof(f347,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f346,f37])).

fof(f346,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f345,f39])).

fof(f345,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_15 ),
    inference(resolution,[],[f268,f54])).

fof(f268,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f266])).

fof(f340,plain,
    ( ~ spl2_3
    | spl2_16
    | ~ spl2_19 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | ~ spl2_3
    | spl2_16
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f338,f34])).

fof(f338,plain,
    ( v2_struct_0(sK0)
    | ~ spl2_3
    | spl2_16
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f337,f272])).

fof(f337,plain,
    ( v13_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f336,f36])).

fof(f336,plain,
    ( ~ l3_lattices(sK0)
    | v13_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f334,f70])).

fof(f70,plain,
    ( v13_lattices(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f334,plain,
    ( ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v13_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_19 ),
    inference(resolution,[],[f305,f35])).

fof(f305,plain,
    ( ! [X0] :
        ( ~ v10_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ l3_lattices(X0)
        | v13_lattices(k7_filter_1(X0,sK1))
        | v2_struct_0(X0) )
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f304,f37])).

fof(f304,plain,
    ( ! [X0] :
        ( v13_lattices(k7_filter_1(X0,sK1))
        | ~ v13_lattices(X0)
        | v2_struct_0(sK1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f303,f38])).

fof(f303,plain,
    ( ! [X0] :
        ( v13_lattices(k7_filter_1(X0,sK1))
        | ~ v13_lattices(X0)
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f302,f39])).

fof(f302,plain,
    ( ! [X0] :
        ( v13_lattices(k7_filter_1(X0,sK1))
        | ~ v13_lattices(X0)
        | ~ l3_lattices(sK1)
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_19 ),
    inference(resolution,[],[f294,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v13_lattices(X1)
      | v13_lattices(k7_filter_1(X0,X1))
      | ~ v13_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f294,plain,
    ( v13_lattices(sK1)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl2_19
  <=> v13_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f319,plain,
    ( ~ spl2_4
    | ~ spl2_6
    | spl2_17 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_6
    | spl2_17 ),
    inference(subsumption_resolution,[],[f317,f34])).

fof(f317,plain,
    ( v2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_6
    | spl2_17 ),
    inference(subsumption_resolution,[],[f316,f276])).

fof(f276,plain,
    ( ~ v14_lattices(k7_filter_1(sK0,sK1))
    | spl2_17 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl2_17
  <=> v14_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f316,plain,
    ( v14_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f315,f36])).

fof(f315,plain,
    ( ~ l3_lattices(sK0)
    | v14_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f313,f74])).

fof(f74,plain,
    ( v14_lattices(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_4
  <=> v14_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f313,plain,
    ( ~ v14_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v14_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f216,f35])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ v10_lattices(X0)
        | ~ v14_lattices(X0)
        | ~ l3_lattices(X0)
        | v14_lattices(k7_filter_1(X0,sK1))
        | v2_struct_0(X0) )
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f215,f37])).

fof(f215,plain,
    ( ! [X0] :
        ( v14_lattices(k7_filter_1(X0,sK1))
        | ~ v14_lattices(X0)
        | v2_struct_0(sK1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f214,f38])).

fof(f214,plain,
    ( ! [X0] :
        ( v14_lattices(k7_filter_1(X0,sK1))
        | ~ v14_lattices(X0)
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f213,f39])).

fof(f213,plain,
    ( ! [X0] :
        ( v14_lattices(k7_filter_1(X0,sK1))
        | ~ v14_lattices(X0)
        | ~ l3_lattices(sK1)
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl2_6 ),
    inference(resolution,[],[f125,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v14_lattices(X1)
      | v14_lattices(k7_filter_1(X0,X1))
      | ~ v14_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v14_lattices(X1)
                & v14_lattices(X0) )
              | ~ v14_lattices(k7_filter_1(X0,X1)) )
            & ( v14_lattices(k7_filter_1(X0,X1))
              | ~ v14_lattices(X1)
              | ~ v14_lattices(X0) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v14_lattices(X1)
                & v14_lattices(X0) )
              | ~ v14_lattices(k7_filter_1(X0,X1)) )
            & ( v14_lattices(k7_filter_1(X0,X1))
              | ~ v14_lattices(X1)
              | ~ v14_lattices(X0) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v14_lattices(X1)
              & v14_lattices(X0) )
          <=> v14_lattices(k7_filter_1(X0,X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v14_lattices(X1)
              & v14_lattices(X0) )
          <=> v14_lattices(k7_filter_1(X0,X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( v14_lattices(X1)
              & v14_lattices(X0) )
          <=> v14_lattices(k7_filter_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_filter_1)).

fof(f301,plain,
    ( spl2_2
    | spl2_19 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | spl2_2
    | spl2_19 ),
    inference(subsumption_resolution,[],[f299,f39])).

fof(f299,plain,
    ( ~ l3_lattices(sK1)
    | spl2_2
    | spl2_19 ),
    inference(subsumption_resolution,[],[f298,f37])).

fof(f298,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | spl2_2
    | spl2_19 ),
    inference(subsumption_resolution,[],[f297,f208])).

fof(f208,plain,
    ( v15_lattices(sK1)
    | spl2_2 ),
    inference(subsumption_resolution,[],[f41,f62])).

fof(f62,plain,
    ( ~ v15_lattices(k7_filter_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f41,plain,
    ( v15_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f297,plain,
    ( ~ v15_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | spl2_19 ),
    inference(resolution,[],[f295,f46])).

fof(f295,plain,
    ( ~ v13_lattices(sK1)
    | spl2_19 ),
    inference(avatar_component_clause,[],[f293])).

fof(f283,plain,(
    spl2_14 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | spl2_14 ),
    inference(subsumption_resolution,[],[f281,f34])).

fof(f281,plain,
    ( v2_struct_0(sK0)
    | spl2_14 ),
    inference(subsumption_resolution,[],[f280,f36])).

fof(f280,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl2_14 ),
    inference(subsumption_resolution,[],[f279,f37])).

fof(f279,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl2_14 ),
    inference(subsumption_resolution,[],[f278,f39])).

fof(f278,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl2_14 ),
    inference(resolution,[],[f264,f55])).

fof(f264,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | spl2_14 ),
    inference(avatar_component_clause,[],[f262])).

fof(f277,plain,
    ( ~ spl2_14
    | spl2_15
    | ~ spl2_16
    | ~ spl2_17
    | spl2_2 ),
    inference(avatar_split_clause,[],[f207,f61,f274,f270,f266,f262])).

fof(f207,plain,
    ( ~ v14_lattices(k7_filter_1(sK0,sK1))
    | ~ v13_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | spl2_2 ),
    inference(resolution,[],[f62,f44])).

fof(f210,plain,
    ( spl2_2
    | spl2_6 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | spl2_2
    | spl2_6 ),
    inference(subsumption_resolution,[],[f208,f130])).

fof(f130,plain,
    ( ~ v15_lattices(sK1)
    | spl2_6 ),
    inference(subsumption_resolution,[],[f129,f39])).

fof(f129,plain,
    ( ~ v15_lattices(sK1)
    | ~ l3_lattices(sK1)
    | spl2_6 ),
    inference(subsumption_resolution,[],[f128,f37])).

fof(f128,plain,
    ( ~ v15_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | spl2_6 ),
    inference(resolution,[],[f126,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v14_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f126,plain,
    ( ~ v14_lattices(sK1)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f198,plain,
    ( ~ spl2_1
    | spl2_3 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl2_1
    | spl2_3 ),
    inference(subsumption_resolution,[],[f187,f59])).

fof(f187,plain,
    ( ~ v15_lattices(sK0)
    | spl2_3 ),
    inference(subsumption_resolution,[],[f186,f36])).

fof(f186,plain,
    ( ~ v15_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl2_3 ),
    inference(subsumption_resolution,[],[f77,f34])).

fof(f77,plain,
    ( ~ v15_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl2_3 ),
    inference(resolution,[],[f71,f46])).

fof(f192,plain,
    ( ~ spl2_1
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | ~ spl2_1
    | spl2_4 ),
    inference(subsumption_resolution,[],[f190,f36])).

fof(f190,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl2_1
    | spl2_4 ),
    inference(subsumption_resolution,[],[f189,f34])).

fof(f189,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl2_1
    | spl2_4 ),
    inference(subsumption_resolution,[],[f188,f59])).

fof(f188,plain,
    ( ~ v15_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl2_4 ),
    inference(resolution,[],[f75,f47])).

fof(f75,plain,
    ( ~ v14_lattices(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f185,plain,
    ( ~ spl2_2
    | spl2_6 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl2_2
    | spl2_6 ),
    inference(subsumption_resolution,[],[f183,f126])).

fof(f183,plain,
    ( v14_lattices(sK1)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f182,f34])).

fof(f182,plain,
    ( v2_struct_0(sK0)
    | v14_lattices(sK1)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f181,f35])).

fof(f181,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | v14_lattices(sK1)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f180,f36])).

fof(f180,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | v14_lattices(sK1)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f179,f37])).

fof(f179,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | v14_lattices(sK1)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f178,f38])).

fof(f178,plain,
    ( ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | v14_lattices(sK1)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f176,f39])).

fof(f176,plain,
    ( ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | v14_lattices(sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f84,f63])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v15_lattices(k7_filter_1(X1,X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | v14_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f83,f55])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v14_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ v15_lattices(k7_filter_1(X1,X0))
      | ~ l3_lattices(k7_filter_1(X1,X0)) ) ),
    inference(subsumption_resolution,[],[f82,f54])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v14_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ v15_lattices(k7_filter_1(X1,X0))
      | v2_struct_0(k7_filter_1(X1,X0))
      | ~ l3_lattices(k7_filter_1(X1,X0)) ) ),
    inference(resolution,[],[f50,f47])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v14_lattices(k7_filter_1(X0,X1))
      | v14_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f102,plain,
    ( ~ spl2_2
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | ~ spl2_2
    | spl2_4 ),
    inference(subsumption_resolution,[],[f100,f75])).

fof(f100,plain,
    ( v14_lattices(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f99,f34])).

fof(f99,plain,
    ( v2_struct_0(sK0)
    | v14_lattices(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f98,f35])).

fof(f98,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | v14_lattices(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f97,f36])).

fof(f97,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | v14_lattices(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f96,f37])).

fof(f96,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | v14_lattices(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f95,f38])).

fof(f95,plain,
    ( ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | v14_lattices(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f93,f39])).

fof(f93,plain,
    ( ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | v14_lattices(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f81,f63])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | v14_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f80,f55])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v14_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f79,f54])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v14_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(resolution,[],[f49,f47])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v14_lattices(k7_filter_1(X0,X1))
      | v14_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_1 ),
    inference(avatar_split_clause,[],[f67,f57,f73,f69])).

fof(f67,plain,
    ( ~ v14_lattices(sK0)
    | ~ v13_lattices(sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f66,f36])).

fof(f66,plain,
    ( ~ v14_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f65,f34])).

fof(f65,plain,
    ( ~ v14_lattices(sK0)
    | ~ v13_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl2_1 ),
    inference(resolution,[],[f44,f58])).

fof(f58,plain,
    ( ~ v15_lattices(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f64,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f40,f61,f57])).

fof(f40,plain,
    ( v15_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:56:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (30534)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (30521)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (30521)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f422,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f64,f76,f102,f185,f192,f198,f210,f277,f283,f301,f319,f340,f350,f394,f403,f421])).
% 0.21/0.51  fof(f421,plain,(
% 0.21/0.51    ~spl2_2 | spl2_3),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f420])).
% 0.21/0.51  fof(f420,plain,(
% 0.21/0.51    $false | (~spl2_2 | spl2_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f410,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ~v13_lattices(sK0) | spl2_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    spl2_3 <=> v13_lattices(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.51  fof(f410,plain,(
% 0.21/0.51    v13_lattices(sK0) | ~spl2_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f409,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ((~v15_lattices(k7_filter_1(sK0,sK1)) | ~v15_lattices(sK1) | ~v15_lattices(sK0)) & (v15_lattices(k7_filter_1(sK0,sK1)) | (v15_lattices(sK1) & v15_lattices(sK0))) & l3_lattices(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1)) & l3_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((~v15_lattices(k7_filter_1(X0,X1)) | ~v15_lattices(X1) | ~v15_lattices(X0)) & (v15_lattices(k7_filter_1(X0,X1)) | (v15_lattices(X1) & v15_lattices(X0))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v15_lattices(k7_filter_1(sK0,X1)) | ~v15_lattices(X1) | ~v15_lattices(sK0)) & (v15_lattices(k7_filter_1(sK0,X1)) | (v15_lattices(X1) & v15_lattices(sK0))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ? [X1] : ((~v15_lattices(k7_filter_1(sK0,X1)) | ~v15_lattices(X1) | ~v15_lattices(sK0)) & (v15_lattices(k7_filter_1(sK0,X1)) | (v15_lattices(X1) & v15_lattices(sK0))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((~v15_lattices(k7_filter_1(sK0,sK1)) | ~v15_lattices(sK1) | ~v15_lattices(sK0)) & (v15_lattices(k7_filter_1(sK0,sK1)) | (v15_lattices(sK1) & v15_lattices(sK0))) & l3_lattices(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((~v15_lattices(k7_filter_1(X0,X1)) | ~v15_lattices(X1) | ~v15_lattices(X0)) & (v15_lattices(k7_filter_1(X0,X1)) | (v15_lattices(X1) & v15_lattices(X0))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (((~v15_lattices(k7_filter_1(X0,X1)) | (~v15_lattices(X1) | ~v15_lattices(X0))) & (v15_lattices(k7_filter_1(X0,X1)) | (v15_lattices(X1) & v15_lattices(X0)))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (((v15_lattices(X1) & v15_lattices(X0)) <~> v15_lattices(k7_filter_1(X0,X1))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (((v15_lattices(X1) & v15_lattices(X0)) <~> v15_lattices(k7_filter_1(X0,X1))) & (l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))) & (l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((v15_lattices(X1) & v15_lattices(X0)) <=> v15_lattices(k7_filter_1(X0,X1)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((v15_lattices(X1) & v15_lattices(X0)) <=> v15_lattices(k7_filter_1(X0,X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_filter_1)).
% 0.21/0.51  fof(f409,plain,(
% 0.21/0.51    v2_struct_0(sK0) | v13_lattices(sK0) | ~spl2_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f408,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    v10_lattices(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f408,plain,(
% 0.21/0.51    ~v10_lattices(sK0) | v2_struct_0(sK0) | v13_lattices(sK0) | ~spl2_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f407,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    l3_lattices(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f407,plain,(
% 0.21/0.51    ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | v13_lattices(sK0) | ~spl2_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f406,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ~v2_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f406,plain,(
% 0.21/0.51    v2_struct_0(sK1) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | v13_lattices(sK0) | ~spl2_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f405,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    v10_lattices(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f405,plain,(
% 0.21/0.51    ~v10_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | v13_lattices(sK0) | ~spl2_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f352,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    l3_lattices(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f352,plain,(
% 0.21/0.51    ~l3_lattices(sK1) | ~v10_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | v13_lattices(sK0) | ~spl2_2),
% 0.21/0.51    inference(resolution,[],[f63,f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v15_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | v13_lattices(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f86,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X1] : (l3_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : (l3_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : (l3_lattices(k7_filter_1(X0,X1)) | (~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1] : ((l3_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & ~v2_struct_0(X0)) => l3_lattices(k7_filter_1(X0,X1)))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : ((l3_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & ~v2_struct_0(X0)) => (l3_lattices(k7_filter_1(X0,X1)) & v3_lattices(k7_filter_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_filter_1)).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v13_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~v15_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(k7_filter_1(X0,X1))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f85,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_struct_0(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : (~v2_struct_0(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : (~v2_struct_0(k7_filter_1(X0,X1)) | (~l3_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0,X1] : ((l3_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & ~v2_struct_0(X0)) => ~v2_struct_0(k7_filter_1(X0,X1)))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : ((l3_lattices(X1) & ~v2_struct_0(X1) & l3_lattices(X0) & ~v2_struct_0(X0)) => (v3_lattices(k7_filter_1(X0,X1)) & ~v2_struct_0(k7_filter_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_filter_1)).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v13_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~v15_lattices(k7_filter_1(X0,X1)) | v2_struct_0(k7_filter_1(X0,X1)) | ~l3_lattices(k7_filter_1(X0,X1))) )),
% 0.21/0.51    inference(resolution,[],[f52,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0] : (v13_lattices(X0) | ~v15_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : ((v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0)) | ~v15_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (((v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0)) | (~v15_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (l3_lattices(X0) => ((v15_lattices(X0) & ~v2_struct_0(X0)) => (v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_lattices)).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v13_lattices(k7_filter_1(X0,X1)) | v13_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((((v13_lattices(X1) & v13_lattices(X0)) | ~v13_lattices(k7_filter_1(X0,X1))) & (v13_lattices(k7_filter_1(X0,X1)) | ~v13_lattices(X1) | ~v13_lattices(X0))) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((((v13_lattices(X1) & v13_lattices(X0)) | ~v13_lattices(k7_filter_1(X0,X1))) & (v13_lattices(k7_filter_1(X0,X1)) | (~v13_lattices(X1) | ~v13_lattices(X0)))) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v13_lattices(X1) & v13_lattices(X0)) <=> v13_lattices(k7_filter_1(X0,X1))) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v13_lattices(X1) & v13_lattices(X0)) <=> v13_lattices(k7_filter_1(X0,X1))) | (~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((v13_lattices(X1) & v13_lattices(X0)) <=> v13_lattices(k7_filter_1(X0,X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_filter_1)).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    v15_lattices(k7_filter_1(sK0,sK1)) | ~spl2_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl2_2 <=> v15_lattices(k7_filter_1(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.51  fof(f403,plain,(
% 0.21/0.51    ~spl2_2 | ~spl2_14 | spl2_15 | spl2_16),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f402])).
% 0.21/0.51  fof(f402,plain,(
% 0.21/0.51    $false | (~spl2_2 | ~spl2_14 | spl2_15 | spl2_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f401,f263])).
% 0.21/0.51  fof(f263,plain,(
% 0.21/0.51    l3_lattices(k7_filter_1(sK0,sK1)) | ~spl2_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f262])).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    spl2_14 <=> l3_lattices(k7_filter_1(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.51  fof(f401,plain,(
% 0.21/0.51    ~l3_lattices(k7_filter_1(sK0,sK1)) | (~spl2_2 | spl2_15 | spl2_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f400,f267])).
% 0.21/0.51  fof(f267,plain,(
% 0.21/0.51    ~v2_struct_0(k7_filter_1(sK0,sK1)) | spl2_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f266])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    spl2_15 <=> v2_struct_0(k7_filter_1(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.51  fof(f400,plain,(
% 0.21/0.51    v2_struct_0(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | (~spl2_2 | spl2_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f399,f63])).
% 0.21/0.51  fof(f399,plain,(
% 0.21/0.51    ~v15_lattices(k7_filter_1(sK0,sK1)) | v2_struct_0(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | spl2_16),
% 0.21/0.51    inference(resolution,[],[f272,f46])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    ~v13_lattices(k7_filter_1(sK0,sK1)) | spl2_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f270])).
% 0.21/0.51  fof(f270,plain,(
% 0.21/0.51    spl2_16 <=> v13_lattices(k7_filter_1(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.51  fof(f394,plain,(
% 0.21/0.51    ~spl2_1 | ~spl2_2 | ~spl2_6 | ~spl2_16),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f393])).
% 0.21/0.51  fof(f393,plain,(
% 0.21/0.51    $false | (~spl2_1 | ~spl2_2 | ~spl2_6 | ~spl2_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f379,f373])).
% 0.21/0.51  fof(f373,plain,(
% 0.21/0.51    ~v13_lattices(sK1) | (~spl2_1 | ~spl2_2 | ~spl2_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f372,f39])).
% 0.21/0.51  fof(f372,plain,(
% 0.21/0.51    ~v13_lattices(sK1) | ~l3_lattices(sK1) | (~spl2_1 | ~spl2_2 | ~spl2_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f367,f37])).
% 0.21/0.51  fof(f367,plain,(
% 0.21/0.51    ~v13_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK1) | (~spl2_1 | ~spl2_2 | ~spl2_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f366,f125])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    v14_lattices(sK1) | ~spl2_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f124])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    spl2_6 <=> v14_lattices(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.51  fof(f366,plain,(
% 0.21/0.51    ~v14_lattices(sK1) | ~v13_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK1) | (~spl2_1 | ~spl2_2)),
% 0.21/0.51    inference(resolution,[],[f365,f44])).
% 0.21/0.52  % (30535)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.52  % (30528)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.52  % (30527)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.53  % (30536)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0] : (v15_lattices(X0) | ~v14_lattices(X0) | ~v13_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : ((v15_lattices(X0) & ~v2_struct_0(X0)) | ~v14_lattices(X0) | ~v13_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (((v15_lattices(X0) & ~v2_struct_0(X0)) | (~v14_lattices(X0) | ~v13_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (l3_lattices(X0) => ((v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0)) => (v15_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_lattices)).
% 0.21/0.53  fof(f365,plain,(
% 0.21/0.53    ~v15_lattices(sK1) | (~spl2_1 | ~spl2_2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f351,f63])).
% 0.21/0.53  fof(f351,plain,(
% 0.21/0.53    ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v15_lattices(sK1) | ~spl2_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f42,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    v15_lattices(sK0) | ~spl2_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    spl2_1 <=> v15_lattices(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ~v15_lattices(k7_filter_1(sK0,sK1)) | ~v15_lattices(sK1) | ~v15_lattices(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f379,plain,(
% 0.21/0.53    v13_lattices(sK1) | ~spl2_16),
% 0.21/0.53    inference(subsumption_resolution,[],[f378,f34])).
% 0.21/0.53  fof(f378,plain,(
% 0.21/0.53    v13_lattices(sK1) | v2_struct_0(sK0) | ~spl2_16),
% 0.21/0.53    inference(subsumption_resolution,[],[f377,f35])).
% 0.21/0.53  fof(f377,plain,(
% 0.21/0.53    v13_lattices(sK1) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl2_16),
% 0.21/0.53    inference(subsumption_resolution,[],[f376,f36])).
% 0.21/0.53  fof(f376,plain,(
% 0.21/0.53    v13_lattices(sK1) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl2_16),
% 0.21/0.53    inference(subsumption_resolution,[],[f375,f37])).
% 0.21/0.53  fof(f375,plain,(
% 0.21/0.53    v13_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl2_16),
% 0.21/0.53    inference(subsumption_resolution,[],[f374,f38])).
% 0.21/0.53  fof(f374,plain,(
% 0.21/0.53    v13_lattices(sK1) | ~v10_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl2_16),
% 0.21/0.53    inference(subsumption_resolution,[],[f355,f39])).
% 0.21/0.53  fof(f355,plain,(
% 0.21/0.53    v13_lattices(sK1) | ~l3_lattices(sK1) | ~v10_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl2_16),
% 0.21/0.53    inference(resolution,[],[f271,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v13_lattices(k7_filter_1(X0,X1)) | v13_lattices(X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f271,plain,(
% 0.21/0.53    v13_lattices(k7_filter_1(sK0,sK1)) | ~spl2_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f270])).
% 0.21/0.53  fof(f350,plain,(
% 0.21/0.53    ~spl2_15),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f349])).
% 0.21/0.53  fof(f349,plain,(
% 0.21/0.53    $false | ~spl2_15),
% 0.21/0.53    inference(subsumption_resolution,[],[f348,f34])).
% 0.21/0.53  fof(f348,plain,(
% 0.21/0.53    v2_struct_0(sK0) | ~spl2_15),
% 0.21/0.53    inference(subsumption_resolution,[],[f347,f36])).
% 0.21/0.53  fof(f347,plain,(
% 0.21/0.53    ~l3_lattices(sK0) | v2_struct_0(sK0) | ~spl2_15),
% 0.21/0.53    inference(subsumption_resolution,[],[f346,f37])).
% 0.21/0.53  fof(f346,plain,(
% 0.21/0.53    v2_struct_0(sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~spl2_15),
% 0.21/0.53    inference(subsumption_resolution,[],[f345,f39])).
% 0.21/0.53  fof(f345,plain,(
% 0.21/0.53    ~l3_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~spl2_15),
% 0.21/0.53    inference(resolution,[],[f268,f54])).
% 0.21/0.53  fof(f268,plain,(
% 0.21/0.53    v2_struct_0(k7_filter_1(sK0,sK1)) | ~spl2_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f266])).
% 0.21/0.53  fof(f340,plain,(
% 0.21/0.53    ~spl2_3 | spl2_16 | ~spl2_19),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f339])).
% 0.21/0.53  fof(f339,plain,(
% 0.21/0.53    $false | (~spl2_3 | spl2_16 | ~spl2_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f338,f34])).
% 0.21/0.53  fof(f338,plain,(
% 0.21/0.53    v2_struct_0(sK0) | (~spl2_3 | spl2_16 | ~spl2_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f337,f272])).
% 0.21/0.53  fof(f337,plain,(
% 0.21/0.53    v13_lattices(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | (~spl2_3 | ~spl2_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f336,f36])).
% 0.21/0.53  fof(f336,plain,(
% 0.21/0.53    ~l3_lattices(sK0) | v13_lattices(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | (~spl2_3 | ~spl2_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f334,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    v13_lattices(sK0) | ~spl2_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f69])).
% 0.21/0.53  fof(f334,plain,(
% 0.21/0.53    ~v13_lattices(sK0) | ~l3_lattices(sK0) | v13_lattices(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~spl2_19),
% 0.21/0.53    inference(resolution,[],[f305,f35])).
% 0.21/0.53  fof(f305,plain,(
% 0.21/0.53    ( ! [X0] : (~v10_lattices(X0) | ~v13_lattices(X0) | ~l3_lattices(X0) | v13_lattices(k7_filter_1(X0,sK1)) | v2_struct_0(X0)) ) | ~spl2_19),
% 0.21/0.53    inference(subsumption_resolution,[],[f304,f37])).
% 0.21/0.53  fof(f304,plain,(
% 0.21/0.53    ( ! [X0] : (v13_lattices(k7_filter_1(X0,sK1)) | ~v13_lattices(X0) | v2_struct_0(sK1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) ) | ~spl2_19),
% 0.21/0.53    inference(subsumption_resolution,[],[f303,f38])).
% 0.21/0.53  fof(f303,plain,(
% 0.21/0.53    ( ! [X0] : (v13_lattices(k7_filter_1(X0,sK1)) | ~v13_lattices(X0) | ~v10_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) ) | ~spl2_19),
% 0.21/0.53    inference(subsumption_resolution,[],[f302,f39])).
% 0.21/0.53  fof(f302,plain,(
% 0.21/0.53    ( ! [X0] : (v13_lattices(k7_filter_1(X0,sK1)) | ~v13_lattices(X0) | ~l3_lattices(sK1) | ~v10_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) ) | ~spl2_19),
% 0.21/0.53    inference(resolution,[],[f294,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v13_lattices(X1) | v13_lattices(k7_filter_1(X0,X1)) | ~v13_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f294,plain,(
% 0.21/0.53    v13_lattices(sK1) | ~spl2_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f293])).
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    spl2_19 <=> v13_lattices(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.53  fof(f319,plain,(
% 0.21/0.53    ~spl2_4 | ~spl2_6 | spl2_17),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f318])).
% 0.21/0.53  fof(f318,plain,(
% 0.21/0.53    $false | (~spl2_4 | ~spl2_6 | spl2_17)),
% 0.21/0.53    inference(subsumption_resolution,[],[f317,f34])).
% 0.21/0.53  fof(f317,plain,(
% 0.21/0.53    v2_struct_0(sK0) | (~spl2_4 | ~spl2_6 | spl2_17)),
% 0.21/0.53    inference(subsumption_resolution,[],[f316,f276])).
% 0.21/0.53  fof(f276,plain,(
% 0.21/0.53    ~v14_lattices(k7_filter_1(sK0,sK1)) | spl2_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f274])).
% 0.21/0.53  fof(f274,plain,(
% 0.21/0.53    spl2_17 <=> v14_lattices(k7_filter_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.53  fof(f316,plain,(
% 0.21/0.53    v14_lattices(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | (~spl2_4 | ~spl2_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f315,f36])).
% 0.21/0.53  fof(f315,plain,(
% 0.21/0.53    ~l3_lattices(sK0) | v14_lattices(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | (~spl2_4 | ~spl2_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f313,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    v14_lattices(sK0) | ~spl2_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    spl2_4 <=> v14_lattices(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.53  fof(f313,plain,(
% 0.21/0.53    ~v14_lattices(sK0) | ~l3_lattices(sK0) | v14_lattices(k7_filter_1(sK0,sK1)) | v2_struct_0(sK0) | ~spl2_6),
% 0.21/0.53    inference(resolution,[],[f216,f35])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    ( ! [X0] : (~v10_lattices(X0) | ~v14_lattices(X0) | ~l3_lattices(X0) | v14_lattices(k7_filter_1(X0,sK1)) | v2_struct_0(X0)) ) | ~spl2_6),
% 0.21/0.53    inference(subsumption_resolution,[],[f215,f37])).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    ( ! [X0] : (v14_lattices(k7_filter_1(X0,sK1)) | ~v14_lattices(X0) | v2_struct_0(sK1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) ) | ~spl2_6),
% 0.21/0.53    inference(subsumption_resolution,[],[f214,f38])).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    ( ! [X0] : (v14_lattices(k7_filter_1(X0,sK1)) | ~v14_lattices(X0) | ~v10_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) ) | ~spl2_6),
% 0.21/0.53    inference(subsumption_resolution,[],[f213,f39])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    ( ! [X0] : (v14_lattices(k7_filter_1(X0,sK1)) | ~v14_lattices(X0) | ~l3_lattices(sK1) | ~v10_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) ) | ~spl2_6),
% 0.21/0.53    inference(resolution,[],[f125,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v14_lattices(X1) | v14_lattices(k7_filter_1(X0,X1)) | ~v14_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((((v14_lattices(X1) & v14_lattices(X0)) | ~v14_lattices(k7_filter_1(X0,X1))) & (v14_lattices(k7_filter_1(X0,X1)) | ~v14_lattices(X1) | ~v14_lattices(X0))) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((((v14_lattices(X1) & v14_lattices(X0)) | ~v14_lattices(k7_filter_1(X0,X1))) & (v14_lattices(k7_filter_1(X0,X1)) | (~v14_lattices(X1) | ~v14_lattices(X0)))) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v14_lattices(X1) & v14_lattices(X0)) <=> v14_lattices(k7_filter_1(X0,X1))) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v14_lattices(X1) & v14_lattices(X0)) <=> v14_lattices(k7_filter_1(X0,X1))) | (~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ((v14_lattices(X1) & v14_lattices(X0)) <=> v14_lattices(k7_filter_1(X0,X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_filter_1)).
% 0.21/0.53  fof(f301,plain,(
% 0.21/0.53    spl2_2 | spl2_19),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f300])).
% 0.21/0.53  fof(f300,plain,(
% 0.21/0.53    $false | (spl2_2 | spl2_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f299,f39])).
% 0.21/0.53  fof(f299,plain,(
% 0.21/0.53    ~l3_lattices(sK1) | (spl2_2 | spl2_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f298,f37])).
% 0.21/0.53  fof(f298,plain,(
% 0.21/0.53    v2_struct_0(sK1) | ~l3_lattices(sK1) | (spl2_2 | spl2_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f297,f208])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    v15_lattices(sK1) | spl2_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f41,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ~v15_lattices(k7_filter_1(sK0,sK1)) | spl2_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f61])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    v15_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f297,plain,(
% 0.21/0.53    ~v15_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK1) | spl2_19),
% 0.21/0.53    inference(resolution,[],[f295,f46])).
% 0.21/0.53  fof(f295,plain,(
% 0.21/0.53    ~v13_lattices(sK1) | spl2_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f293])).
% 0.21/0.53  fof(f283,plain,(
% 0.21/0.53    spl2_14),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f282])).
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    $false | spl2_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f281,f34])).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    v2_struct_0(sK0) | spl2_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f280,f36])).
% 0.21/0.53  fof(f280,plain,(
% 0.21/0.53    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl2_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f279,f37])).
% 0.21/0.53  fof(f279,plain,(
% 0.21/0.53    v2_struct_0(sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | spl2_14),
% 0.21/0.53    inference(subsumption_resolution,[],[f278,f39])).
% 0.21/0.53  fof(f278,plain,(
% 0.21/0.53    ~l3_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | spl2_14),
% 0.21/0.53    inference(resolution,[],[f264,f55])).
% 0.21/0.53  fof(f264,plain,(
% 0.21/0.53    ~l3_lattices(k7_filter_1(sK0,sK1)) | spl2_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f262])).
% 0.21/0.53  fof(f277,plain,(
% 0.21/0.53    ~spl2_14 | spl2_15 | ~spl2_16 | ~spl2_17 | spl2_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f207,f61,f274,f270,f266,f262])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    ~v14_lattices(k7_filter_1(sK0,sK1)) | ~v13_lattices(k7_filter_1(sK0,sK1)) | v2_struct_0(k7_filter_1(sK0,sK1)) | ~l3_lattices(k7_filter_1(sK0,sK1)) | spl2_2),
% 0.21/0.53    inference(resolution,[],[f62,f44])).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    spl2_2 | spl2_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f209])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    $false | (spl2_2 | spl2_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f208,f130])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ~v15_lattices(sK1) | spl2_6),
% 0.21/0.53    inference(subsumption_resolution,[],[f129,f39])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    ~v15_lattices(sK1) | ~l3_lattices(sK1) | spl2_6),
% 0.21/0.53    inference(subsumption_resolution,[],[f128,f37])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ~v15_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK1) | spl2_6),
% 0.21/0.53    inference(resolution,[],[f126,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0] : (v14_lattices(X0) | ~v15_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ~v14_lattices(sK1) | spl2_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f124])).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    ~spl2_1 | spl2_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f197])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    $false | (~spl2_1 | spl2_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f187,f59])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    ~v15_lattices(sK0) | spl2_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f186,f36])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    ~v15_lattices(sK0) | ~l3_lattices(sK0) | spl2_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f77,f34])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ~v15_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl2_3),
% 0.21/0.53    inference(resolution,[],[f71,f46])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    ~spl2_1 | spl2_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f191])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    $false | (~spl2_1 | spl2_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f190,f36])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    ~l3_lattices(sK0) | (~spl2_1 | spl2_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f189,f34])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    v2_struct_0(sK0) | ~l3_lattices(sK0) | (~spl2_1 | spl2_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f188,f59])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    ~v15_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl2_4),
% 0.21/0.53    inference(resolution,[],[f75,f47])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ~v14_lattices(sK0) | spl2_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f73])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    ~spl2_2 | spl2_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f184])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    $false | (~spl2_2 | spl2_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f183,f126])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    v14_lattices(sK1) | ~spl2_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f182,f34])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    v2_struct_0(sK0) | v14_lattices(sK1) | ~spl2_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f181,f35])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    ~v10_lattices(sK0) | v2_struct_0(sK0) | v14_lattices(sK1) | ~spl2_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f180,f36])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | v14_lattices(sK1) | ~spl2_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f179,f37])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    v2_struct_0(sK1) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | v14_lattices(sK1) | ~spl2_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f178,f38])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    ~v10_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | v14_lattices(sK1) | ~spl2_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f176,f39])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    ~l3_lattices(sK1) | ~v10_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | v14_lattices(sK1) | ~spl2_2),
% 0.21/0.53    inference(resolution,[],[f84,f63])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v15_lattices(k7_filter_1(X1,X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | v14_lattices(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f83,f55])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v14_lattices(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~v15_lattices(k7_filter_1(X1,X0)) | ~l3_lattices(k7_filter_1(X1,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f82,f54])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v14_lattices(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~v15_lattices(k7_filter_1(X1,X0)) | v2_struct_0(k7_filter_1(X1,X0)) | ~l3_lattices(k7_filter_1(X1,X0))) )),
% 0.21/0.53    inference(resolution,[],[f50,f47])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v14_lattices(k7_filter_1(X0,X1)) | v14_lattices(X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ~spl2_2 | spl2_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f101])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    $false | (~spl2_2 | spl2_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f100,f75])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    v14_lattices(sK0) | ~spl2_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f99,f34])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    v2_struct_0(sK0) | v14_lattices(sK0) | ~spl2_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f98,f35])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ~v10_lattices(sK0) | v2_struct_0(sK0) | v14_lattices(sK0) | ~spl2_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f97,f36])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | v14_lattices(sK0) | ~spl2_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f96,f37])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    v2_struct_0(sK1) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | v14_lattices(sK0) | ~spl2_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f95,f38])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ~v10_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | v14_lattices(sK0) | ~spl2_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f93,f39])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ~l3_lattices(sK1) | ~v10_lattices(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | v14_lattices(sK0) | ~spl2_2),
% 0.21/0.53    inference(resolution,[],[f81,f63])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v15_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | v14_lattices(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f80,f55])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v14_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~v15_lattices(k7_filter_1(X0,X1)) | ~l3_lattices(k7_filter_1(X0,X1))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f79,f54])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v14_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~v15_lattices(k7_filter_1(X0,X1)) | v2_struct_0(k7_filter_1(X0,X1)) | ~l3_lattices(k7_filter_1(X0,X1))) )),
% 0.21/0.53    inference(resolution,[],[f49,f47])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v14_lattices(k7_filter_1(X0,X1)) | v14_lattices(X0) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ~spl2_3 | ~spl2_4 | spl2_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f67,f57,f73,f69])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ~v14_lattices(sK0) | ~v13_lattices(sK0) | spl2_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f66,f36])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ~v14_lattices(sK0) | ~v13_lattices(sK0) | ~l3_lattices(sK0) | spl2_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f65,f34])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ~v14_lattices(sK0) | ~v13_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl2_1),
% 0.21/0.53    inference(resolution,[],[f44,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ~v15_lattices(sK0) | spl2_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f57])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    spl2_1 | spl2_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f40,f61,f57])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    v15_lattices(k7_filter_1(sK0,sK1)) | v15_lattices(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (30521)------------------------------
% 0.21/0.53  % (30521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30521)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (30521)Memory used [KB]: 5500
% 0.21/0.53  % (30521)Time elapsed: 0.091 s
% 0.21/0.53  % (30521)------------------------------
% 0.21/0.53  % (30521)------------------------------
% 0.21/0.53  % (30520)Success in time 0.175 s
%------------------------------------------------------------------------------
