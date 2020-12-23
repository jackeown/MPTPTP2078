%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1452+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:21 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :  277 (1400 expanded)
%              Number of leaves         :   27 ( 400 expanded)
%              Depth                    :   25
%              Number of atoms          : 2009 (29236 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4657,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3004,f3026,f3030,f3070,f3119,f3241,f3317,f4154,f4402,f4406,f4408,f4410,f4412,f4455,f4457,f4532,f4640,f4654,f4656])).

fof(f4656,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19
    | spl4_102 ),
    inference(avatar_contradiction_clause,[],[f4655])).

fof(f4655,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19
    | spl4_102 ),
    inference(subsumption_resolution,[],[f4572,f4555])).

fof(f4555,plain,
    ( v11_lattices(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f4554,f2842])).

fof(f2842,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2824])).

fof(f2824,plain,
    ( ( ~ l3_lattices(k7_filter_1(sK0,sK1))
      | ~ v17_lattices(k7_filter_1(sK0,sK1))
      | ~ v10_lattices(k7_filter_1(sK0,sK1))
      | v2_struct_0(k7_filter_1(sK0,sK1))
      | ~ l3_lattices(sK1)
      | ~ v17_lattices(sK1)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1)
      | ~ l3_lattices(sK0)
      | ~ v17_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & ( ( l3_lattices(k7_filter_1(sK0,sK1))
        & v17_lattices(k7_filter_1(sK0,sK1))
        & v10_lattices(k7_filter_1(sK0,sK1))
        & ~ v2_struct_0(k7_filter_1(sK0,sK1)) )
      | ( l3_lattices(sK1)
        & v17_lattices(sK1)
        & v10_lattices(sK1)
        & ~ v2_struct_0(sK1)
        & l3_lattices(sK0)
        & v17_lattices(sK0)
        & v10_lattices(sK0)
        & ~ v2_struct_0(sK0) ) )
    & l3_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1)
    & l3_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2821,f2823,f2822])).

fof(f2822,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ l3_lattices(k7_filter_1(X0,X1))
              | ~ v17_lattices(k7_filter_1(X0,X1))
              | ~ v10_lattices(k7_filter_1(X0,X1))
              | v2_struct_0(k7_filter_1(X0,X1))
              | ~ l3_lattices(X1)
              | ~ v17_lattices(X1)
              | ~ v10_lattices(X1)
              | v2_struct_0(X1)
              | ~ l3_lattices(X0)
              | ~ v17_lattices(X0)
              | ~ v10_lattices(X0)
              | v2_struct_0(X0) )
            & ( ( l3_lattices(k7_filter_1(X0,X1))
                & v17_lattices(k7_filter_1(X0,X1))
                & v10_lattices(k7_filter_1(X0,X1))
                & ~ v2_struct_0(k7_filter_1(X0,X1)) )
              | ( l3_lattices(X1)
                & v17_lattices(X1)
                & v10_lattices(X1)
                & ~ v2_struct_0(X1)
                & l3_lattices(X0)
                & v17_lattices(X0)
                & v10_lattices(X0)
                & ~ v2_struct_0(X0) ) )
            & l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ l3_lattices(k7_filter_1(sK0,X1))
            | ~ v17_lattices(k7_filter_1(sK0,X1))
            | ~ v10_lattices(k7_filter_1(sK0,X1))
            | v2_struct_0(k7_filter_1(sK0,X1))
            | ~ l3_lattices(X1)
            | ~ v17_lattices(X1)
            | ~ v10_lattices(X1)
            | v2_struct_0(X1)
            | ~ l3_lattices(sK0)
            | ~ v17_lattices(sK0)
            | ~ v10_lattices(sK0)
            | v2_struct_0(sK0) )
          & ( ( l3_lattices(k7_filter_1(sK0,X1))
              & v17_lattices(k7_filter_1(sK0,X1))
              & v10_lattices(k7_filter_1(sK0,X1))
              & ~ v2_struct_0(k7_filter_1(sK0,X1)) )
            | ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(sK0)
              & v17_lattices(sK0)
              & v10_lattices(sK0)
              & ~ v2_struct_0(sK0) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2823,plain,
    ( ? [X1] :
        ( ( ~ l3_lattices(k7_filter_1(sK0,X1))
          | ~ v17_lattices(k7_filter_1(sK0,X1))
          | ~ v10_lattices(k7_filter_1(sK0,X1))
          | v2_struct_0(k7_filter_1(sK0,X1))
          | ~ l3_lattices(X1)
          | ~ v17_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1)
          | ~ l3_lattices(sK0)
          | ~ v17_lattices(sK0)
          | ~ v10_lattices(sK0)
          | v2_struct_0(sK0) )
        & ( ( l3_lattices(k7_filter_1(sK0,X1))
            & v17_lattices(k7_filter_1(sK0,X1))
            & v10_lattices(k7_filter_1(sK0,X1))
            & ~ v2_struct_0(k7_filter_1(sK0,X1)) )
          | ( l3_lattices(X1)
            & v17_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1)
            & l3_lattices(sK0)
            & v17_lattices(sK0)
            & v10_lattices(sK0)
            & ~ v2_struct_0(sK0) ) )
        & l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ( ~ l3_lattices(k7_filter_1(sK0,sK1))
        | ~ v17_lattices(k7_filter_1(sK0,sK1))
        | ~ v10_lattices(k7_filter_1(sK0,sK1))
        | v2_struct_0(k7_filter_1(sK0,sK1))
        | ~ l3_lattices(sK1)
        | ~ v17_lattices(sK1)
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1)
        | ~ l3_lattices(sK0)
        | ~ v17_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
      & ( ( l3_lattices(k7_filter_1(sK0,sK1))
          & v17_lattices(k7_filter_1(sK0,sK1))
          & v10_lattices(k7_filter_1(sK0,sK1))
          & ~ v2_struct_0(k7_filter_1(sK0,sK1)) )
        | ( l3_lattices(sK1)
          & v17_lattices(sK1)
          & v10_lattices(sK1)
          & ~ v2_struct_0(sK1)
          & l3_lattices(sK0)
          & v17_lattices(sK0)
          & v10_lattices(sK0)
          & ~ v2_struct_0(sK0) ) )
      & l3_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f2821,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ l3_lattices(k7_filter_1(X0,X1))
            | ~ v17_lattices(k7_filter_1(X0,X1))
            | ~ v10_lattices(k7_filter_1(X0,X1))
            | v2_struct_0(k7_filter_1(X0,X1))
            | ~ l3_lattices(X1)
            | ~ v17_lattices(X1)
            | ~ v10_lattices(X1)
            | v2_struct_0(X1)
            | ~ l3_lattices(X0)
            | ~ v17_lattices(X0)
            | ~ v10_lattices(X0)
            | v2_struct_0(X0) )
          & ( ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) )
            | ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2820])).

fof(f2820,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ l3_lattices(k7_filter_1(X0,X1))
            | ~ v17_lattices(k7_filter_1(X0,X1))
            | ~ v10_lattices(k7_filter_1(X0,X1))
            | v2_struct_0(k7_filter_1(X0,X1))
            | ~ l3_lattices(X1)
            | ~ v17_lattices(X1)
            | ~ v10_lattices(X1)
            | v2_struct_0(X1)
            | ~ l3_lattices(X0)
            | ~ v17_lattices(X0)
            | ~ v10_lattices(X0)
            | v2_struct_0(X0) )
          & ( ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) )
            | ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2769])).

fof(f2769,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <~> ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2768])).

fof(f2768,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <~> ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2743])).

fof(f2743,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l3_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1) )
           => ( ( l3_lattices(X1)
                & v17_lattices(X1)
                & v10_lattices(X1)
                & ~ v2_struct_0(X1)
                & l3_lattices(X0)
                & v17_lattices(X0)
                & v10_lattices(X0)
                & ~ v2_struct_0(X0) )
            <=> ( l3_lattices(k7_filter_1(X0,X1))
                & v17_lattices(k7_filter_1(X0,X1))
                & v10_lattices(k7_filter_1(X0,X1))
                & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f2742])).

fof(f2742,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v17_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v17_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_filter_1)).

fof(f4554,plain,
    ( v11_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f4553,f2843])).

fof(f2843,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f2824])).

fof(f4553,plain,
    ( v11_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f4552,f2844])).

fof(f2844,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f2824])).

fof(f4552,plain,
    ( v11_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f4551,f2845])).

fof(f2845,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f2824])).

fof(f4551,plain,
    ( v11_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f4550,f2846])).

fof(f2846,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f2824])).

fof(f4550,plain,
    ( v11_lattices(sK0)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f4549,f2847])).

fof(f2847,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f2824])).

fof(f4549,plain,
    ( v11_lattices(sK0)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f4548,f3044])).

fof(f3044,plain,
    ( ~ v2_struct_0(k7_filter_1(sK0,sK1))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f3042])).

fof(f3042,plain,
    ( spl4_12
  <=> v2_struct_0(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f4548,plain,
    ( v11_lattices(sK0)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f4547,f2998])).

fof(f2998,plain,
    ( v10_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f2997])).

fof(f2997,plain,
    ( spl4_7
  <=> v10_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f4547,plain,
    ( v11_lattices(sK0)
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f4469,f3008])).

fof(f3008,plain,
    ( l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f3006])).

fof(f3006,plain,
    ( spl4_9
  <=> l3_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f4469,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(sK0)
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_19 ),
    inference(resolution,[],[f3113,f2905])).

fof(f2905,plain,(
    ! [X0,X1] :
      ( ~ v11_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v11_lattices(X0)
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2834])).

fof(f2834,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( l3_lattices(X1)
                & v11_lattices(X1)
                & v10_lattices(X1)
                & ~ v2_struct_0(X1)
                & l3_lattices(X0)
                & v11_lattices(X0)
                & v10_lattices(X0)
                & ~ v2_struct_0(X0) )
              | ~ l3_lattices(k7_filter_1(X0,X1))
              | ~ v11_lattices(k7_filter_1(X0,X1))
              | ~ v10_lattices(k7_filter_1(X0,X1))
              | v2_struct_0(k7_filter_1(X0,X1)) )
            & ( ( l3_lattices(k7_filter_1(X0,X1))
                & v11_lattices(k7_filter_1(X0,X1))
                & v10_lattices(k7_filter_1(X0,X1))
                & ~ v2_struct_0(k7_filter_1(X0,X1)) )
              | ~ l3_lattices(X1)
              | ~ v11_lattices(X1)
              | ~ v10_lattices(X1)
              | v2_struct_0(X1)
              | ~ l3_lattices(X0)
              | ~ v11_lattices(X0)
              | ~ v10_lattices(X0)
              | v2_struct_0(X0) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2833])).

fof(f2833,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( l3_lattices(X1)
                & v11_lattices(X1)
                & v10_lattices(X1)
                & ~ v2_struct_0(X1)
                & l3_lattices(X0)
                & v11_lattices(X0)
                & v10_lattices(X0)
                & ~ v2_struct_0(X0) )
              | ~ l3_lattices(k7_filter_1(X0,X1))
              | ~ v11_lattices(k7_filter_1(X0,X1))
              | ~ v10_lattices(k7_filter_1(X0,X1))
              | v2_struct_0(k7_filter_1(X0,X1)) )
            & ( ( l3_lattices(k7_filter_1(X0,X1))
                & v11_lattices(k7_filter_1(X0,X1))
                & v10_lattices(k7_filter_1(X0,X1))
                & ~ v2_struct_0(k7_filter_1(X0,X1)) )
              | ~ l3_lattices(X1)
              | ~ v11_lattices(X1)
              | ~ v10_lattices(X1)
              | v2_struct_0(X1)
              | ~ l3_lattices(X0)
              | ~ v11_lattices(X0)
              | ~ v10_lattices(X0)
              | v2_struct_0(X0) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2789])).

fof(f2789,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v11_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v11_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2788])).

fof(f2788,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v11_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v11_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2728])).

fof(f2728,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( l3_lattices(X1)
              & v11_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v11_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_filter_1)).

fof(f3113,plain,
    ( v11_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f3111])).

fof(f3111,plain,
    ( spl4_19
  <=> v11_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f4572,plain,
    ( ~ v11_lattices(sK0)
    | spl4_102 ),
    inference(avatar_component_clause,[],[f4571])).

fof(f4571,plain,
    ( spl4_102
  <=> v11_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).

fof(f4654,plain,
    ( ~ spl4_20
    | spl4_22 ),
    inference(avatar_contradiction_clause,[],[f4653])).

fof(f4653,plain,
    ( $false
    | ~ spl4_20
    | spl4_22 ),
    inference(subsumption_resolution,[],[f4561,f3214])).

fof(f3214,plain,
    ( ~ v15_lattices(sK0)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f3212])).

fof(f3212,plain,
    ( spl4_22
  <=> v15_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f4561,plain,
    ( v15_lattices(sK0)
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f4560,f2842])).

fof(f4560,plain,
    ( v15_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f4559,f2843])).

fof(f4559,plain,
    ( v15_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f4558,f2844])).

fof(f4558,plain,
    ( v15_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f4557,f2845])).

fof(f4557,plain,
    ( v15_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f4556,f2846])).

fof(f4556,plain,
    ( v15_lattices(sK0)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f4155,f2847])).

fof(f4155,plain,
    ( v15_lattices(sK0)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_20 ),
    inference(resolution,[],[f3118,f2897])).

fof(f2897,plain,(
    ! [X0,X1] :
      ( ~ v15_lattices(k7_filter_1(X0,X1))
      | v15_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2832])).

fof(f2832,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v15_lattices(X1)
                & v15_lattices(X0) )
              | ~ v15_lattices(k7_filter_1(X0,X1)) )
            & ( v15_lattices(k7_filter_1(X0,X1))
              | ~ v15_lattices(X1)
              | ~ v15_lattices(X0) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2831])).

fof(f2831,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v15_lattices(X1)
                & v15_lattices(X0) )
              | ~ v15_lattices(k7_filter_1(X0,X1)) )
            & ( v15_lattices(k7_filter_1(X0,X1))
              | ~ v15_lattices(X1)
              | ~ v15_lattices(X0) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2787])).

fof(f2787,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v15_lattices(X1)
              & v15_lattices(X0) )
          <=> v15_lattices(k7_filter_1(X0,X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2786])).

fof(f2786,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v15_lattices(X1)
              & v15_lattices(X0) )
          <=> v15_lattices(k7_filter_1(X0,X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2735])).

fof(f2735,axiom,(
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

fof(f3118,plain,
    ( v15_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f3116])).

fof(f3116,plain,
    ( spl4_20
  <=> v15_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f4640,plain,
    ( ~ spl4_102
    | ~ spl4_22
    | spl4_2
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f4639,f3121,f3116,f3042,f3006,f2997,f2977,f3212,f4571])).

fof(f2977,plain,
    ( spl4_2
  <=> v17_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f3121,plain,
    ( spl4_21
  <=> v16_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f4639,plain,
    ( ~ v15_lattices(sK0)
    | ~ v11_lattices(sK0)
    | spl4_2
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4638,f2844])).

fof(f4638,plain,
    ( ~ v15_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl4_2
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4637,f2842])).

fof(f4637,plain,
    ( ~ v15_lattices(sK0)
    | ~ v11_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_2
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4633,f2979])).

fof(f2979,plain,
    ( ~ v17_lattices(sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f2977])).

fof(f4633,plain,
    ( v17_lattices(sK0)
    | ~ v15_lattices(sK0)
    | ~ v11_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(resolution,[],[f4546,f2951])).

fof(f2951,plain,(
    ! [X0] :
      ( ~ v16_lattices(X0)
      | v17_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2817])).

fof(f2817,plain,(
    ! [X0] :
      ( ( v17_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f2816])).

fof(f2816,plain,(
    ! [X0] :
      ( ( v17_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2015])).

fof(f2015,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v17_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_lattices)).

fof(f4546,plain,
    ( v16_lattices(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4545,f2842])).

fof(f4545,plain,
    ( v16_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4544,f2843])).

fof(f4544,plain,
    ( v16_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4543,f2844])).

fof(f4543,plain,
    ( v16_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4542,f2845])).

fof(f4542,plain,
    ( v16_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4541,f2846])).

fof(f4541,plain,
    ( v16_lattices(sK0)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4540,f2847])).

fof(f4540,plain,
    ( v16_lattices(sK0)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4539,f3044])).

fof(f4539,plain,
    ( v16_lattices(sK0)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4538,f2998])).

fof(f4538,plain,
    ( v16_lattices(sK0)
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_9
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4537,f3118])).

fof(f4537,plain,
    ( v16_lattices(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_9
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4496,f3008])).

fof(f4496,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK0)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_21 ),
    inference(resolution,[],[f3123,f2919])).

fof(f2919,plain,(
    ! [X0,X1] :
      ( ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v16_lattices(X0)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2836])).

fof(f2836,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( l3_lattices(X1)
                & v16_lattices(X1)
                & v15_lattices(X1)
                & v10_lattices(X1)
                & ~ v2_struct_0(X1)
                & l3_lattices(X0)
                & v16_lattices(X0)
                & v15_lattices(X0)
                & v10_lattices(X0)
                & ~ v2_struct_0(X0) )
              | ~ l3_lattices(k7_filter_1(X0,X1))
              | ~ v16_lattices(k7_filter_1(X0,X1))
              | ~ v15_lattices(k7_filter_1(X0,X1))
              | ~ v10_lattices(k7_filter_1(X0,X1))
              | v2_struct_0(k7_filter_1(X0,X1)) )
            & ( ( l3_lattices(k7_filter_1(X0,X1))
                & v16_lattices(k7_filter_1(X0,X1))
                & v15_lattices(k7_filter_1(X0,X1))
                & v10_lattices(k7_filter_1(X0,X1))
                & ~ v2_struct_0(k7_filter_1(X0,X1)) )
              | ~ l3_lattices(X1)
              | ~ v16_lattices(X1)
              | ~ v15_lattices(X1)
              | ~ v10_lattices(X1)
              | v2_struct_0(X1)
              | ~ l3_lattices(X0)
              | ~ v16_lattices(X0)
              | ~ v15_lattices(X0)
              | ~ v10_lattices(X0)
              | v2_struct_0(X0) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2835])).

fof(f2835,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( l3_lattices(X1)
                & v16_lattices(X1)
                & v15_lattices(X1)
                & v10_lattices(X1)
                & ~ v2_struct_0(X1)
                & l3_lattices(X0)
                & v16_lattices(X0)
                & v15_lattices(X0)
                & v10_lattices(X0)
                & ~ v2_struct_0(X0) )
              | ~ l3_lattices(k7_filter_1(X0,X1))
              | ~ v16_lattices(k7_filter_1(X0,X1))
              | ~ v15_lattices(k7_filter_1(X0,X1))
              | ~ v10_lattices(k7_filter_1(X0,X1))
              | v2_struct_0(k7_filter_1(X0,X1)) )
            & ( ( l3_lattices(k7_filter_1(X0,X1))
                & v16_lattices(k7_filter_1(X0,X1))
                & v15_lattices(k7_filter_1(X0,X1))
                & v10_lattices(k7_filter_1(X0,X1))
                & ~ v2_struct_0(k7_filter_1(X0,X1)) )
              | ~ l3_lattices(X1)
              | ~ v16_lattices(X1)
              | ~ v15_lattices(X1)
              | ~ v10_lattices(X1)
              | v2_struct_0(X1)
              | ~ l3_lattices(X0)
              | ~ v16_lattices(X0)
              | ~ v15_lattices(X0)
              | ~ v10_lattices(X0)
              | v2_struct_0(X0) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2791])).

fof(f2791,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v16_lattices(X1)
              & v15_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v16_lattices(X0)
              & v15_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v16_lattices(k7_filter_1(X0,X1))
              & v15_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2790])).

fof(f2790,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( l3_lattices(X1)
              & v16_lattices(X1)
              & v15_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v16_lattices(X0)
              & v15_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v16_lattices(k7_filter_1(X0,X1))
              & v15_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2741])).

fof(f2741,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( l3_lattices(X1)
              & v16_lattices(X1)
              & v15_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v16_lattices(X0)
              & v15_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
          <=> ( l3_lattices(k7_filter_1(X0,X1))
              & v16_lattices(k7_filter_1(X0,X1))
              & v15_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_filter_1)).

fof(f3123,plain,
    ( v16_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f3121])).

fof(f4532,plain,
    ( spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(avatar_contradiction_clause,[],[f4531])).

fof(f4531,plain,
    ( $false
    | spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4530,f2847])).

fof(f4530,plain,
    ( ~ l3_lattices(sK1)
    | spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4529,f2845])).

fof(f4529,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4528,f4482])).

fof(f4482,plain,
    ( v11_lattices(sK1)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f4481,f2842])).

fof(f4481,plain,
    ( v11_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f4480,f2843])).

fof(f4480,plain,
    ( v11_lattices(sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f4479,f2844])).

fof(f4479,plain,
    ( v11_lattices(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f4478,f2845])).

fof(f4478,plain,
    ( v11_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f4477,f2846])).

fof(f4477,plain,
    ( v11_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f4476,f2847])).

fof(f4476,plain,
    ( v11_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f4475,f3044])).

fof(f4475,plain,
    ( v11_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f4474,f2998])).

fof(f4474,plain,
    ( v11_lattices(sK1)
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f4470,f3008])).

fof(f4470,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v11_lattices(sK1)
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_19 ),
    inference(resolution,[],[f3113,f2909])).

fof(f2909,plain,(
    ! [X0,X1] :
      ( ~ v11_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v11_lattices(X1)
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2834])).

fof(f4528,plain,
    ( ~ v11_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4527,f4418])).

fof(f4418,plain,
    ( v15_lattices(sK1)
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f4417,f2842])).

fof(f4417,plain,
    ( v15_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f4416,f2843])).

fof(f4416,plain,
    ( v15_lattices(sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f4415,f2844])).

fof(f4415,plain,
    ( v15_lattices(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f4414,f2845])).

fof(f4414,plain,
    ( v15_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f4413,f2846])).

fof(f4413,plain,
    ( v15_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f4156,f2847])).

fof(f4156,plain,
    ( v15_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_20 ),
    inference(resolution,[],[f3118,f2898])).

fof(f2898,plain,(
    ! [X0,X1] :
      ( ~ v15_lattices(k7_filter_1(X0,X1))
      | v15_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2832])).

fof(f4527,plain,
    ( ~ v15_lattices(sK1)
    | ~ v11_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4523,f2991])).

fof(f2991,plain,
    ( ~ v17_lattices(sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f2989])).

fof(f2989,plain,
    ( spl4_5
  <=> v17_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f4523,plain,
    ( v17_lattices(sK1)
    | ~ v15_lattices(sK1)
    | ~ v11_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(resolution,[],[f4513,f2951])).

fof(f4513,plain,
    ( v16_lattices(sK1)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4512,f2842])).

fof(f4512,plain,
    ( v16_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4511,f2843])).

fof(f4511,plain,
    ( v16_lattices(sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4510,f2844])).

fof(f4510,plain,
    ( v16_lattices(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4509,f2845])).

fof(f4509,plain,
    ( v16_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4508,f2846])).

fof(f4508,plain,
    ( v16_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4507,f2847])).

fof(f4507,plain,
    ( v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_12
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4506,f3044])).

fof(f4506,plain,
    ( v16_lattices(sK1)
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4505,f2998])).

fof(f4505,plain,
    ( v16_lattices(sK1)
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_9
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4504,f3118])).

fof(f4504,plain,
    ( v16_lattices(sK1)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_9
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f4498,f3008])).

fof(f4498,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v16_lattices(sK1)
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_21 ),
    inference(resolution,[],[f3123,f2924])).

fof(f2924,plain,(
    ! [X0,X1] :
      ( ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | v16_lattices(X1)
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2836])).

fof(f4457,plain,
    ( ~ spl4_9
    | spl4_21
    | ~ spl4_8
    | spl4_12 ),
    inference(avatar_split_clause,[],[f4456,f3042,f3001,f3121,f3006])).

fof(f3001,plain,
    ( spl4_8
  <=> v17_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f4456,plain,
    ( v16_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_8
    | spl4_12 ),
    inference(subsumption_resolution,[],[f4435,f3044])).

fof(f4435,plain,
    ( v16_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_8 ),
    inference(resolution,[],[f3002,f2955])).

fof(f2955,plain,(
    ! [X0] :
      ( ~ v17_lattices(X0)
      | v16_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2819])).

fof(f2819,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f2818])).

fof(f2818,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2014])).

fof(f2014,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_lattices)).

fof(f3002,plain,
    ( v17_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f3001])).

fof(f4455,plain,
    ( ~ spl4_9
    | spl4_19
    | ~ spl4_8
    | spl4_12 ),
    inference(avatar_split_clause,[],[f4454,f3042,f3001,f3111,f3006])).

fof(f4454,plain,
    ( v11_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_8
    | spl4_12 ),
    inference(subsumption_resolution,[],[f4433,f3044])).

fof(f4433,plain,
    ( v11_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_8 ),
    inference(resolution,[],[f3002,f2953])).

fof(f2953,plain,(
    ! [X0] :
      ( ~ v17_lattices(X0)
      | v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2819])).

fof(f4412,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f4411])).

fof(f4411,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f2975,f2842])).

fof(f2975,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f2973])).

fof(f2973,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f4410,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f4409])).

fof(f4409,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f2995,f2847])).

fof(f2995,plain,
    ( ~ l3_lattices(sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f2993])).

fof(f2993,plain,
    ( spl4_6
  <=> l3_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f4408,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f4407])).

fof(f4407,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f2987,f2845])).

fof(f2987,plain,
    ( v2_struct_0(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f2985])).

fof(f2985,plain,
    ( spl4_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f4406,plain,
    ( ~ spl4_9
    | spl4_8
    | ~ spl4_2
    | ~ spl4_5
    | spl4_12
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f4405,f3116,f3042,f2989,f2977,f3001,f3006])).

fof(f4405,plain,
    ( v17_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5
    | spl4_12
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f4404,f3044])).

fof(f4404,plain,
    ( v17_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f4403,f3325])).

fof(f3325,plain,
    ( v11_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f3324,f2845])).

fof(f3324,plain,
    ( v2_struct_0(sK1)
    | v11_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f3323,f2846])).

fof(f3323,plain,
    ( ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | v11_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f3319,f2847])).

fof(f3319,plain,
    ( ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | v11_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f3201,f3192])).

fof(f3192,plain,
    ( v11_lattices(sK1)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f3191,f2847])).

fof(f3191,plain,
    ( v11_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f3170,f2845])).

fof(f3170,plain,
    ( v11_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl4_5 ),
    inference(resolution,[],[f2990,f2953])).

fof(f2990,plain,
    ( v17_lattices(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f2989])).

fof(f3201,plain,
    ( ! [X0] :
        ( ~ v11_lattices(X0)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | v11_lattices(k7_filter_1(sK0,X0)) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f3200,f2842])).

fof(f3200,plain,
    ( ! [X0] :
        ( ~ l3_lattices(X0)
        | ~ v11_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | v11_lattices(k7_filter_1(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f3199,f2843])).

fof(f3199,plain,
    ( ! [X0] :
        ( ~ l3_lattices(X0)
        | ~ v11_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | v11_lattices(k7_filter_1(sK0,X0))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f3197,f2844])).

fof(f3197,plain,
    ( ! [X0] :
        ( ~ l3_lattices(X0)
        | ~ v11_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | ~ l3_lattices(sK0)
        | v11_lattices(k7_filter_1(sK0,X0))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f3159,f2958])).

fof(f2958,plain,(
    ! [X0,X1] :
      ( ~ v11_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v11_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v11_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f2901])).

fof(f2901,plain,(
    ! [X0,X1] :
      ( v11_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v11_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2834])).

fof(f3159,plain,
    ( v11_lattices(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f3158,f2844])).

fof(f3158,plain,
    ( v11_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f3137,f2842])).

fof(f3137,plain,
    ( v11_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f2978,f2953])).

fof(f2978,plain,
    ( v17_lattices(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f2977])).

fof(f4403,plain,
    ( v17_lattices(k7_filter_1(sK0,sK1))
    | ~ v11_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f4130,f3118])).

fof(f4130,plain,
    ( v17_lattices(k7_filter_1(sK0,sK1))
    | ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v11_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f4099,f2951])).

fof(f4099,plain,
    ( v16_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f4098,f2845])).

fof(f4098,plain,
    ( v2_struct_0(sK1)
    | v16_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f4097,f2846])).

fof(f4097,plain,
    ( ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | v16_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f4096,f3194])).

fof(f3194,plain,
    ( v15_lattices(sK1)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f3193,f2847])).

fof(f3193,plain,
    ( v15_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f3171,f2845])).

fof(f3171,plain,
    ( v15_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl4_5 ),
    inference(resolution,[],[f2990,f2954])).

fof(f2954,plain,(
    ! [X0] :
      ( ~ v17_lattices(X0)
      | v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2819])).

fof(f4096,plain,
    ( ~ v15_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | v16_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f4091,f2847])).

fof(f4091,plain,
    ( ~ l3_lattices(sK1)
    | ~ v15_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | v16_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f3253,f3196])).

fof(f3196,plain,
    ( v16_lattices(sK1)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f3195,f2847])).

fof(f3195,plain,
    ( v16_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f3172,f2845])).

fof(f3172,plain,
    ( v16_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1)
    | ~ spl4_5 ),
    inference(resolution,[],[f2990,f2955])).

fof(f3253,plain,
    ( ! [X1] :
        ( ~ v16_lattices(X1)
        | ~ l3_lattices(X1)
        | ~ v15_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | v16_lattices(k7_filter_1(sK0,X1)) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f3252,f2842])).

fof(f3252,plain,
    ( ! [X1] :
        ( ~ l3_lattices(X1)
        | ~ v16_lattices(X1)
        | ~ v15_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | v16_lattices(k7_filter_1(sK0,X1))
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f3251,f2843])).

fof(f3251,plain,
    ( ! [X1] :
        ( ~ l3_lattices(X1)
        | ~ v16_lattices(X1)
        | ~ v15_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | v16_lattices(k7_filter_1(sK0,X1))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f3250,f3161])).

fof(f3161,plain,
    ( v15_lattices(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f3160,f2844])).

fof(f3160,plain,
    ( v15_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f3138,f2842])).

fof(f3138,plain,
    ( v15_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f2978,f2954])).

fof(f3250,plain,
    ( ! [X1] :
        ( ~ l3_lattices(X1)
        | ~ v16_lattices(X1)
        | ~ v15_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | v16_lattices(k7_filter_1(sK0,X1))
        | ~ v15_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f3248,f2844])).

fof(f3248,plain,
    ( ! [X1] :
        ( ~ l3_lattices(X1)
        | ~ v16_lattices(X1)
        | ~ v15_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(sK0)
        | v16_lattices(k7_filter_1(sK0,X1))
        | ~ v15_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f3163,f2962])).

fof(f2962,plain,(
    ! [X0,X1] :
      ( ~ v16_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v16_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f2914])).

fof(f2914,plain,(
    ! [X0,X1] :
      ( v16_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2836])).

fof(f3163,plain,
    ( v16_lattices(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f3162,f2844])).

fof(f3162,plain,
    ( v16_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f3139,f2842])).

fof(f3139,plain,
    ( v16_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f2978,f2955])).

fof(f4402,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f4401])).

fof(f4401,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f4400,f2842])).

fof(f4400,plain,
    ( v2_struct_0(sK0)
    | spl4_9 ),
    inference(subsumption_resolution,[],[f4399,f2844])).

fof(f4399,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_9 ),
    inference(subsumption_resolution,[],[f4398,f2845])).

fof(f4398,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_9 ),
    inference(subsumption_resolution,[],[f4397,f2847])).

fof(f4397,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_9 ),
    inference(resolution,[],[f3007,f2883])).

fof(f2883,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2775])).

fof(f2775,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2774])).

fof(f2774,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2759])).

fof(f2759,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f2622])).

fof(f2622,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_filter_1)).

fof(f3007,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f3006])).

fof(f4154,plain,
    ( ~ spl4_2
    | ~ spl4_5
    | spl4_20 ),
    inference(avatar_contradiction_clause,[],[f4153])).

fof(f4153,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_5
    | spl4_20 ),
    inference(subsumption_resolution,[],[f4152,f2842])).

fof(f4152,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_5
    | spl4_20 ),
    inference(subsumption_resolution,[],[f4151,f2843])).

fof(f4151,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_5
    | spl4_20 ),
    inference(subsumption_resolution,[],[f4150,f2844])).

fof(f4150,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_5
    | spl4_20 ),
    inference(subsumption_resolution,[],[f4149,f3161])).

fof(f4149,plain,
    ( ~ v15_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_5
    | spl4_20 ),
    inference(resolution,[],[f3117,f3262])).

fof(f3262,plain,
    ( ! [X0] :
        ( v15_lattices(k7_filter_1(X0,sK1))
        | ~ v15_lattices(X0)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f3261,f2845])).

fof(f3261,plain,
    ( ! [X0] :
        ( v15_lattices(k7_filter_1(X0,sK1))
        | ~ v15_lattices(X0)
        | v2_struct_0(sK1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f3260,f2846])).

fof(f3260,plain,
    ( ! [X0] :
        ( v15_lattices(k7_filter_1(X0,sK1))
        | ~ v15_lattices(X0)
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f3259,f2847])).

fof(f3259,plain,
    ( ! [X0] :
        ( v15_lattices(k7_filter_1(X0,sK1))
        | ~ v15_lattices(X0)
        | ~ l3_lattices(sK1)
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1)
        | ~ l3_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
    | ~ spl4_5 ),
    inference(resolution,[],[f3194,f2896])).

fof(f2896,plain,(
    ! [X0,X1] :
      ( ~ v15_lattices(X1)
      | v15_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2832])).

fof(f3117,plain,
    ( ~ v15_lattices(k7_filter_1(sK0,sK1))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f3116])).

fof(f3317,plain,(
    ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f3316])).

fof(f3316,plain,
    ( $false
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f3315,f2842])).

fof(f3315,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f3314,f2844])).

fof(f3314,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f3313,f2845])).

fof(f3313,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f3292,f2847])).

fof(f3292,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_12 ),
    inference(resolution,[],[f3043,f2884])).

fof(f2884,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2777])).

fof(f2777,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2776])).

fof(f2776,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2760])).

fof(f2760,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ~ v2_struct_0(k7_filter_1(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f2638])).

fof(f2638,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v3_lattices(k7_filter_1(X0,X1))
        & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_filter_1)).

fof(f3043,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f3042])).

fof(f3241,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f3240])).

fof(f3240,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f3239,f2842])).

fof(f3239,plain,
    ( v2_struct_0(sK0)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f3238,f2843])).

fof(f3238,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f3237,f2844])).

fof(f3237,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f3236,f2845])).

fof(f3236,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f3235,f2846])).

fof(f3235,plain,
    ( ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f3204,f2847])).

fof(f3204,plain,
    ( ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_7 ),
    inference(resolution,[],[f2999,f2882])).

fof(f2882,plain,(
    ! [X0,X1] :
      ( v10_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2773])).

fof(f2773,plain,(
    ! [X0,X1] :
      ( v10_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2772])).

fof(f2772,plain,(
    ! [X0,X1] :
      ( v10_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2758])).

fof(f2758,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => v10_lattices(k7_filter_1(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f2641])).

fof(f2641,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v10_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_filter_1)).

fof(f2999,plain,
    ( ~ v10_lattices(k7_filter_1(sK0,sK1))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f2997])).

fof(f3119,plain,
    ( ~ spl4_9
    | spl4_12
    | spl4_20
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f3078,f3001,f3116,f3042,f3006])).

fof(f3078,plain,
    ( v15_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_8 ),
    inference(resolution,[],[f3002,f2954])).

fof(f3070,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f3069])).

fof(f3069,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f2983,f2844])).

fof(f2983,plain,
    ( ~ l3_lattices(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f2981])).

fof(f2981,plain,
    ( spl4_3
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f3030,plain,
    ( spl4_2
    | spl4_8 ),
    inference(avatar_split_clause,[],[f2866,f3001,f2977])).

fof(f2866,plain,
    ( v17_lattices(k7_filter_1(sK0,sK1))
    | v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f2824])).

fof(f3026,plain,
    ( spl4_5
    | spl4_8 ),
    inference(avatar_split_clause,[],[f2870,f3001,f2989])).

fof(f2870,plain,
    ( v17_lattices(k7_filter_1(sK0,sK1))
    | v17_lattices(sK1) ),
    inference(cnf_transformation,[],[f2824])).

fof(f3004,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f2971,f3001,f2997,f2993,f2989,f2985,f2981,f2977,f2973])).

fof(f2971,plain,
    ( ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2970,f2884])).

fof(f2970,plain,
    ( ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2969,f2883])).

fof(f2969,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2968,f2929])).

fof(f2929,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(k7_filter_1(X0,X1))
      | v10_lattices(X0)
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2797])).

fof(f2797,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1)
            & l3_lattices(X0)
            & v10_lattices(X0)
            & ~ v2_struct_0(X0) )
          | ~ l3_lattices(k7_filter_1(X0,X1))
          | ~ v10_lattices(k7_filter_1(X0,X1))
          | v2_struct_0(k7_filter_1(X0,X1))
          | ~ l3_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2796])).

fof(f2796,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1)
            & l3_lattices(X0)
            & v10_lattices(X0)
            & ~ v2_struct_0(X0) )
          | ~ l3_lattices(k7_filter_1(X0,X1))
          | ~ v10_lattices(k7_filter_1(X0,X1))
          | v2_struct_0(k7_filter_1(X0,X1))
          | ~ l3_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2722])).

fof(f2722,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( l3_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) )
           => ( l3_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_filter_1)).

fof(f2968,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2880,f2932])).

fof(f2932,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(k7_filter_1(X0,X1))
      | v10_lattices(X1)
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2797])).

fof(f2880,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ v17_lattices(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2824])).
%------------------------------------------------------------------------------
