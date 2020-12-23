%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1452+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  146 (2685 expanded)
%              Number of leaves         :   21 ( 786 expanded)
%              Depth                    :   14
%              Number of atoms          : 1048 (63443 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f945,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f170,f180,f184,f196,f200,f242,f588,f590,f592,f594,f596,f764,f766,f768,f770,f942,f944])).

fof(f944,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f943])).

fof(f943,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f137,f40])).

fof(f40,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).

fof(f31,plain,
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

fof(f32,plain,
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f137,plain,
    ( ~ l3_lattices(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl2_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f942,plain,
    ( spl2_7
    | spl2_9
    | ~ spl2_11 ),
    inference(avatar_contradiction_clause,[],[f941])).

fof(f941,plain,
    ( $false
    | spl2_7
    | spl2_9
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f910,f695])).

fof(f695,plain,
    ( v11_lattices(sK1)
    | spl2_9
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f38,f39,f40,f41,f42,f43,f156,f219,f215,f635,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v11_lattices(X1)
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | ~ v11_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f635,plain,
    ( v11_lattices(k7_filter_1(sK0,sK1))
    | spl2_9
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f215,f156,f164,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_lattices)).

fof(f164,plain,
    ( v17_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl2_11
  <=> v17_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f215,plain,(
    l3_lattices(k7_filter_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f38,f40,f41,f43,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f219,plain,(
    v10_lattices(k7_filter_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f38,f39,f40,f41,f42,f43,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v10_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v10_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v10_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => v10_lattices(k7_filter_1(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
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

fof(f156,plain,
    ( ~ v2_struct_0(k7_filter_1(sK0,sK1))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl2_9
  <=> v2_struct_0(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f43,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f42,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f39,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f910,plain,
    ( ~ v11_lattices(sK1)
    | spl2_7
    | spl2_9
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f43,f41,f149,f661,f662,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v17_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v17_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v17_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v17_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_lattices)).

fof(f662,plain,
    ( v15_lattices(sK1)
    | spl2_9
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f38,f39,f40,f41,f42,f43,f156,f219,f633,f215,f634,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v15_lattices(X1)
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

% (18933)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f634,plain,
    ( v15_lattices(k7_filter_1(sK0,sK1))
    | spl2_9
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f215,f156,f164,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f633,plain,
    ( v16_lattices(k7_filter_1(sK0,sK1))
    | spl2_9
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f215,f156,f164,f82])).

fof(f82,plain,(
    ! [X0] :
      ( v16_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f661,plain,
    ( v16_lattices(sK1)
    | spl2_9
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f38,f39,f40,f41,f42,f43,f156,f219,f633,f215,f634,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v16_lattices(X1)
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f149,plain,
    ( ~ v17_lattices(sK1)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl2_7
  <=> v17_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f770,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f769])).

fof(f769,plain,
    ( $false
    | spl2_8 ),
    inference(subsumption_resolution,[],[f153,f43])).

fof(f153,plain,
    ( ~ l3_lattices(sK1)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl2_8
  <=> l3_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f768,plain,(
    ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f767])).

fof(f767,plain,
    ( $false
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f141,f41])).

fof(f141,plain,
    ( v2_struct_0(sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl2_5
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f766,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f765])).

fof(f765,plain,
    ( $false
    | spl2_6 ),
    inference(subsumption_resolution,[],[f145,f42])).

fof(f145,plain,
    ( ~ v10_lattices(sK1)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl2_6
  <=> v10_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f764,plain,
    ( spl2_3
    | spl2_9
    | ~ spl2_11 ),
    inference(avatar_contradiction_clause,[],[f763])).

fof(f763,plain,
    ( $false
    | spl2_3
    | spl2_9
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f722,f696])).

fof(f696,plain,
    ( v11_lattices(sK0)
    | spl2_9
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f38,f39,f40,f41,f42,f43,f156,f219,f215,f635,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v11_lattices(X0)
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | ~ v11_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f722,plain,
    ( ~ v11_lattices(sK0)
    | spl2_3
    | spl2_9
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f40,f38,f133,f663,f664,f78])).

fof(f664,plain,
    ( v15_lattices(sK0)
    | spl2_9
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f38,f39,f40,f41,f42,f43,f156,f219,f633,f215,f634,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v15_lattices(X0)
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f663,plain,
    ( v16_lattices(sK0)
    | spl2_9
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f38,f39,f40,f41,f42,f43,f156,f219,f633,f215,f634,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v16_lattices(X0)
      | ~ l3_lattices(k7_filter_1(X0,X1))
      | ~ v16_lattices(k7_filter_1(X0,X1))
      | ~ v15_lattices(k7_filter_1(X0,X1))
      | ~ v10_lattices(k7_filter_1(X0,X1))
      | v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f133,plain,
    ( ~ v17_lattices(sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl2_3
  <=> v17_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f596,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f595])).

fof(f595,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f129,f39])).

fof(f129,plain,
    ( ~ v10_lattices(sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl2_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f594,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f125,f38])).

fof(f125,plain,
    ( v2_struct_0(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl2_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f592,plain,(
    spl2_12 ),
    inference(avatar_contradiction_clause,[],[f591])).

fof(f591,plain,
    ( $false
    | spl2_12 ),
    inference(subsumption_resolution,[],[f169,f215])).

fof(f169,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | spl2_12 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl2_12
  <=> l3_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f590,plain,
    ( ~ spl2_3
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f589])).

fof(f589,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f157,f273])).

fof(f273,plain,
    ( ~ v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f38,f39,f205,f207,f40,f41,f42,f206,f43,f208,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
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
    inference(cnf_transformation,[],[f35])).

fof(f208,plain,
    ( v16_lattices(sK1)
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f43,f41,f148,f82])).

fof(f148,plain,
    ( v17_lattices(sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f147])).

fof(f206,plain,
    ( v15_lattices(sK1)
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f43,f41,f148,f81])).

fof(f207,plain,
    ( v16_lattices(sK0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f40,f38,f132,f82])).

fof(f132,plain,
    ( v17_lattices(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f131])).

fof(f205,plain,
    ( v15_lattices(sK0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f40,f38,f132,f81])).

fof(f157,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f155])).

fof(f588,plain,
    ( ~ spl2_3
    | ~ spl2_7
    | spl2_9
    | spl2_11 ),
    inference(avatar_contradiction_clause,[],[f587])).

fof(f587,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_7
    | spl2_9
    | spl2_11 ),
    inference(subsumption_resolution,[],[f586,f285])).

fof(f285,plain,
    ( v16_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f38,f39,f205,f207,f40,f41,f42,f206,f43,f208,f120])).

fof(f120,plain,(
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
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f586,plain,
    ( ~ v16_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_7
    | spl2_9
    | spl2_11 ),
    inference(unit_resulting_resolution,[],[f215,f156,f253,f165,f281,f78])).

fof(f281,plain,
    ( v15_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f38,f39,f205,f207,f40,f41,f42,f206,f43,f208,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( v15_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v15_lattices(k7_filter_1(X0,X1))
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
    inference(cnf_transformation,[],[f35])).

fof(f165,plain,
    ( ~ v17_lattices(k7_filter_1(sK0,sK1))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f163])).

fof(f253,plain,
    ( v11_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f38,f39,f203,f40,f41,f42,f204,f43,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v11_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v11_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f204,plain,
    ( v11_lattices(sK1)
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f43,f41,f148,f80])).

fof(f203,plain,
    ( v11_lattices(sK0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f40,f38,f132,f80])).

fof(f242,plain,(
    spl2_10 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | spl2_10 ),
    inference(subsumption_resolution,[],[f219,f161])).

fof(f161,plain,
    ( ~ v10_lattices(k7_filter_1(sK0,sK1))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl2_10
  <=> v10_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f200,plain,
    ( spl2_3
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f46,f155,f131])).

fof(f46,plain,
    ( ~ v2_struct_0(k7_filter_1(sK0,sK1))
    | v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f196,plain,
    ( spl2_7
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f50,f155,f147])).

fof(f50,plain,
    ( ~ v2_struct_0(k7_filter_1(sK0,sK1))
    | v17_lattices(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f184,plain,
    ( spl2_3
    | spl2_11 ),
    inference(avatar_split_clause,[],[f62,f163,f131])).

fof(f62,plain,
    ( v17_lattices(k7_filter_1(sK0,sK1))
    | v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f180,plain,
    ( spl2_7
    | spl2_11 ),
    inference(avatar_split_clause,[],[f66,f163,f147])).

fof(f66,plain,
    ( v17_lattices(k7_filter_1(sK0,sK1))
    | v17_lattices(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f170,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | spl2_9
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f76,f167,f163,f159,f155,f151,f147,f143,f139,f135,f131,f127,f123])).

fof(f76,plain,
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
    inference(cnf_transformation,[],[f33])).

%------------------------------------------------------------------------------
