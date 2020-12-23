%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1452+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:42 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_4531)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    ! [X1,X0] :
      ( ( sP2(X1,X0)
      <=> ( l3_lattices(k7_filter_1(X0,X1))
          & v16_lattices(k7_filter_1(X0,X1))
          & v15_lattices(k7_filter_1(X0,X1))
          & v10_lattices(k7_filter_1(X0,X1))
          & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f90,plain,(
    ! [X1,X0] :
      ( ( ( sP2(X1,X0)
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
          | ~ sP2(X1,X0) ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f68])).

fof(f91,plain,(
    ! [X1,X0] :
      ( ( ( sP2(X1,X0)
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
          | ~ sP2(X1,X0) ) )
      | ~ sP3(X1,X0) ) ),
    inference(flattening,[],[f90])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ( ( sP2(X0,X1)
          | ~ l3_lattices(k7_filter_1(X1,X0))
          | ~ v16_lattices(k7_filter_1(X1,X0))
          | ~ v15_lattices(k7_filter_1(X1,X0))
          | ~ v10_lattices(k7_filter_1(X1,X0))
          | v2_struct_0(k7_filter_1(X1,X0)) )
        & ( ( l3_lattices(k7_filter_1(X1,X0))
            & v16_lattices(k7_filter_1(X1,X0))
            & v15_lattices(k7_filter_1(X1,X0))
            & v10_lattices(k7_filter_1(X1,X0))
            & ~ v2_struct_0(k7_filter_1(X1,X0)) )
          | ~ sP2(X0,X1) ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f91])).

fof(f145,plain,(
    ! [X0,X1] :
      ( v10_lattices(k7_filter_1(X1,X0))
      | ~ sP2(X0,X1)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f67,plain,(
    ! [X1,X0] :
      ( sP2(X1,X0)
    <=> ( l3_lattices(X1)
        & v16_lattices(X1)
        & v15_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & v16_lattices(X0)
        & v15_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f93,plain,(
    ! [X1,X0] :
      ( ( sP2(X1,X0)
        | ~ l3_lattices(X1)
        | ~ v16_lattices(X1)
        | ~ v15_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v16_lattices(X0)
        | ~ v15_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & ( ( l3_lattices(X1)
          & v16_lattices(X1)
          & v15_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1)
          & l3_lattices(X0)
          & v16_lattices(X0)
          & v15_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
        | ~ sP2(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f94,plain,(
    ! [X1,X0] :
      ( ( sP2(X1,X0)
        | ~ l3_lattices(X1)
        | ~ v16_lattices(X1)
        | ~ v15_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v16_lattices(X0)
        | ~ v15_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & ( ( l3_lattices(X1)
          & v16_lattices(X1)
          & v15_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1)
          & l3_lattices(X0)
          & v16_lattices(X0)
          & v15_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
        | ~ sP2(X1,X0) ) ) ),
    inference(flattening,[],[f93])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ l3_lattices(X0)
        | ~ v16_lattices(X0)
        | ~ v15_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | ~ l3_lattices(X1)
        | ~ v16_lattices(X1)
        | ~ v15_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1) )
      & ( ( l3_lattices(X0)
          & v16_lattices(X0)
          & v15_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0)
          & l3_lattices(X1)
          & v16_lattices(X1)
          & v15_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f94])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f151,plain,(
    ! [X0,X1] :
      ( v10_lattices(X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f154,plain,(
    ! [X0,X1] :
      ( l3_lattices(X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f156,plain,(
    ! [X0,X1] :
      ( v10_lattices(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f159,plain,(
    ! [X0,X1] :
      ( l3_lattices(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v10_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => v10_lattices(k7_filter_1(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v10_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v10_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v10_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f96,plain,(
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
    inference(nnf_transformation,[],[f63])).

fof(f97,plain,(
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
    inference(flattening,[],[f96])).

fof(f99,plain,(
    ! [X0] :
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
     => ( ( ~ l3_lattices(k7_filter_1(X0,sK12))
          | ~ v17_lattices(k7_filter_1(X0,sK12))
          | ~ v10_lattices(k7_filter_1(X0,sK12))
          | v2_struct_0(k7_filter_1(X0,sK12))
          | ~ l3_lattices(sK12)
          | ~ v17_lattices(sK12)
          | ~ v10_lattices(sK12)
          | v2_struct_0(sK12)
          | ~ l3_lattices(X0)
          | ~ v17_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0) )
        & ( ( l3_lattices(k7_filter_1(X0,sK12))
            & v17_lattices(k7_filter_1(X0,sK12))
            & v10_lattices(k7_filter_1(X0,sK12))
            & ~ v2_struct_0(k7_filter_1(X0,sK12)) )
          | ( l3_lattices(sK12)
            & v17_lattices(sK12)
            & v10_lattices(sK12)
            & ~ v2_struct_0(sK12)
            & l3_lattices(X0)
            & v17_lattices(X0)
            & v10_lattices(X0)
            & ~ v2_struct_0(X0) ) )
        & l3_lattices(sK12)
        & v10_lattices(sK12)
        & ~ v2_struct_0(sK12) ) ) ),
    introduced(choice_axiom,[])).

fof(f98,plain,
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
          ( ( ~ l3_lattices(k7_filter_1(sK11,X1))
            | ~ v17_lattices(k7_filter_1(sK11,X1))
            | ~ v10_lattices(k7_filter_1(sK11,X1))
            | v2_struct_0(k7_filter_1(sK11,X1))
            | ~ l3_lattices(X1)
            | ~ v17_lattices(X1)
            | ~ v10_lattices(X1)
            | v2_struct_0(X1)
            | ~ l3_lattices(sK11)
            | ~ v17_lattices(sK11)
            | ~ v10_lattices(sK11)
            | v2_struct_0(sK11) )
          & ( ( l3_lattices(k7_filter_1(sK11,X1))
              & v17_lattices(k7_filter_1(sK11,X1))
              & v10_lattices(k7_filter_1(sK11,X1))
              & ~ v2_struct_0(k7_filter_1(sK11,X1)) )
            | ( l3_lattices(X1)
              & v17_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(sK11)
              & v17_lattices(sK11)
              & v10_lattices(sK11)
              & ~ v2_struct_0(sK11) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(sK11)
      & v10_lattices(sK11)
      & ~ v2_struct_0(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f100,plain,
    ( ( ~ l3_lattices(k7_filter_1(sK11,sK12))
      | ~ v17_lattices(k7_filter_1(sK11,sK12))
      | ~ v10_lattices(k7_filter_1(sK11,sK12))
      | v2_struct_0(k7_filter_1(sK11,sK12))
      | ~ l3_lattices(sK12)
      | ~ v17_lattices(sK12)
      | ~ v10_lattices(sK12)
      | v2_struct_0(sK12)
      | ~ l3_lattices(sK11)
      | ~ v17_lattices(sK11)
      | ~ v10_lattices(sK11)
      | v2_struct_0(sK11) )
    & ( ( l3_lattices(k7_filter_1(sK11,sK12))
        & v17_lattices(k7_filter_1(sK11,sK12))
        & v10_lattices(k7_filter_1(sK11,sK12))
        & ~ v2_struct_0(k7_filter_1(sK11,sK12)) )
      | ( l3_lattices(sK12)
        & v17_lattices(sK12)
        & v10_lattices(sK12)
        & ~ v2_struct_0(sK12)
        & l3_lattices(sK11)
        & v17_lattices(sK11)
        & v10_lattices(sK11)
        & ~ v2_struct_0(sK11) ) )
    & l3_lattices(sK12)
    & v10_lattices(sK12)
    & ~ v2_struct_0(sK12)
    & l3_lattices(sK11)
    & v10_lattices(sK11)
    & ~ v2_struct_0(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f97,f99,f98])).

fof(f200,plain,
    ( ~ l3_lattices(k7_filter_1(sK11,sK12))
    | ~ v17_lattices(k7_filter_1(sK11,sK12))
    | ~ v10_lattices(k7_filter_1(sK11,sK12))
    | v2_struct_0(k7_filter_1(sK11,sK12))
    | ~ l3_lattices(sK12)
    | ~ v17_lattices(sK12)
    | ~ v10_lattices(sK12)
    | v2_struct_0(sK12)
    | ~ l3_lattices(sK11)
    | ~ v17_lattices(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11) ),
    inference(cnf_transformation,[],[f100])).

fof(f162,plain,(
    ~ v2_struct_0(sK11) ),
    inference(cnf_transformation,[],[f100])).

fof(f163,plain,(
    v10_lattices(sK11) ),
    inference(cnf_transformation,[],[f100])).

fof(f164,plain,(
    l3_lattices(sK11) ),
    inference(cnf_transformation,[],[f100])).

fof(f165,plain,(
    ~ v2_struct_0(sK12) ),
    inference(cnf_transformation,[],[f100])).

fof(f166,plain,(
    v10_lattices(sK12) ),
    inference(cnf_transformation,[],[f100])).

fof(f167,plain,(
    l3_lattices(sK12) ),
    inference(cnf_transformation,[],[f100])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v17_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ( v17_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0] :
      ( ( v17_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f48])).

fof(f106,plain,(
    ! [X0] :
      ( v17_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X1,X0)
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f61,f68,f67])).

fof(f161,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f149,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | ~ l3_lattices(k7_filter_1(X1,X0))
      | ~ v16_lattices(k7_filter_1(X1,X0))
      | ~ v15_lattices(k7_filter_1(X1,X0))
      | ~ v10_lattices(k7_filter_1(X1,X0))
      | v2_struct_0(k7_filter_1(X1,X0))
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v3_lattices(k7_filter_1(X0,X1))
        & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ~ v2_struct_0(k7_filter_1(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f53,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f108,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f64,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( l3_lattices(X1)
        & v11_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f87,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ~ l3_lattices(X1)
        | ~ v11_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v11_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & ( ( l3_lattices(X1)
          & v11_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1)
          & l3_lattices(X0)
          & v11_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f64])).

fof(f88,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ~ l3_lattices(X1)
        | ~ v11_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1)
        | ~ l3_lattices(X0)
        | ~ v11_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & ( ( l3_lattices(X1)
          & v11_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1)
          & l3_lattices(X0)
          & v11_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f87])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ l3_lattices(X0)
        | ~ v11_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0)
        | ~ l3_lattices(X1)
        | ~ v11_lattices(X1)
        | ~ v10_lattices(X1)
        | v2_struct_0(X1) )
      & ( ( l3_lattices(X0)
          & v11_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0)
          & l3_lattices(X1)
          & v11_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f88])).

fof(f142,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X1)
      | ~ v11_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
      <=> ( l3_lattices(k7_filter_1(X0,X1))
          & v11_lattices(k7_filter_1(X0,X1))
          & v10_lattices(k7_filter_1(X0,X1))
          & ~ v2_struct_0(k7_filter_1(X0,X1)) ) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f84,plain,(
    ! [X1,X0] :
      ( ( ( sP0(X1,X0)
          | ~ l3_lattices(k7_filter_1(X0,X1))
          | ~ v11_lattices(k7_filter_1(X0,X1))
          | ~ v10_lattices(k7_filter_1(X0,X1))
          | v2_struct_0(k7_filter_1(X0,X1)) )
        & ( ( l3_lattices(k7_filter_1(X0,X1))
            & v11_lattices(k7_filter_1(X0,X1))
            & v10_lattices(k7_filter_1(X0,X1))
            & ~ v2_struct_0(k7_filter_1(X0,X1)) )
          | ~ sP0(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f85,plain,(
    ! [X1,X0] :
      ( ( ( sP0(X1,X0)
          | ~ l3_lattices(k7_filter_1(X0,X1))
          | ~ v11_lattices(k7_filter_1(X0,X1))
          | ~ v10_lattices(k7_filter_1(X0,X1))
          | v2_struct_0(k7_filter_1(X0,X1)) )
        & ( ( l3_lattices(k7_filter_1(X0,X1))
            & v11_lattices(k7_filter_1(X0,X1))
            & v10_lattices(k7_filter_1(X0,X1))
            & ~ v2_struct_0(k7_filter_1(X0,X1)) )
          | ~ sP0(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(flattening,[],[f84])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( ( sP0(X0,X1)
          | ~ l3_lattices(k7_filter_1(X1,X0))
          | ~ v11_lattices(k7_filter_1(X1,X0))
          | ~ v10_lattices(k7_filter_1(X1,X0))
          | v2_struct_0(k7_filter_1(X1,X0)) )
        & ( ( l3_lattices(k7_filter_1(X1,X0))
            & v11_lattices(k7_filter_1(X1,X0))
            & v10_lattices(k7_filter_1(X1,X0))
            & ~ v2_struct_0(k7_filter_1(X1,X0)) )
          | ~ sP0(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f85])).

fof(f131,plain,(
    ! [X0,X1] :
      ( v11_lattices(k7_filter_1(X1,X0))
      | ~ sP0(X0,X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f59,f65,f64])).

fof(f143,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f135,plain,(
    ! [X0,X1] :
      ( v10_lattices(X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f137,plain,(
    ! [X0,X1] :
      ( l3_lattices(X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f139,plain,(
    ! [X0,X1] :
      ( v10_lattices(X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f141,plain,(
    ! [X0,X1] :
      ( l3_lattices(X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f194,plain,
    ( l3_lattices(k7_filter_1(sK11,sK12))
    | v17_lattices(sK11) ),
    inference(cnf_transformation,[],[f100])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f46])).

fof(f104,plain,(
    ! [X0] :
      ( v16_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f170,plain,
    ( ~ v2_struct_0(k7_filter_1(sK11,sK12))
    | v17_lattices(sK11) ),
    inference(cnf_transformation,[],[f100])).

fof(f186,plain,
    ( v17_lattices(k7_filter_1(sK11,sK12))
    | v17_lattices(sK11) ),
    inference(cnf_transformation,[],[f100])).

fof(f103,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f160,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v15_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X1)
      | ~ v16_lattices(X1)
      | ~ v15_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f147,plain,(
    ! [X0,X1] :
      ( v16_lattices(k7_filter_1(X1,X0))
      | ~ sP2(X0,X1)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f198,plain,
    ( l3_lattices(k7_filter_1(sK11,sK12))
    | v17_lattices(sK12) ),
    inference(cnf_transformation,[],[f100])).

fof(f174,plain,
    ( ~ v2_struct_0(k7_filter_1(sK11,sK12))
    | v17_lattices(sK12) ),
    inference(cnf_transformation,[],[f100])).

fof(f190,plain,
    ( v17_lattices(k7_filter_1(sK11,sK12))
    | v17_lattices(sK12) ),
    inference(cnf_transformation,[],[f100])).

fof(f146,plain,(
    ! [X0,X1] :
      ( v15_lattices(k7_filter_1(X1,X0))
      | ~ sP2(X0,X1)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f102,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f133,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ l3_lattices(k7_filter_1(X1,X0))
      | ~ v11_lattices(k7_filter_1(X1,X0))
      | ~ v10_lattices(k7_filter_1(X1,X0))
      | v2_struct_0(k7_filter_1(X1,X0))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f140,plain,(
    ! [X0,X1] :
      ( v11_lattices(X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f136,plain,(
    ! [X0,X1] :
      ( v11_lattices(X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f152,plain,(
    ! [X0,X1] :
      ( v15_lattices(X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f157,plain,(
    ! [X0,X1] :
      ( v15_lattices(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f153,plain,(
    ! [X0,X1] :
      ( v16_lattices(X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f158,plain,(
    ! [X0,X1] :
      ( v16_lattices(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_47,plain,
    ( ~ sP3(X0,X1)
    | ~ sP2(X0,X1)
    | v10_lattices(k7_filter_1(X1,X0)) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_59,plain,
    ( ~ sP2(X0,X1)
    | ~ v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_58,plain,
    ( ~ sP2(X0,X1)
    | v10_lattices(X1) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_55,plain,
    ( ~ sP2(X0,X1)
    | l3_lattices(X1) ),
    inference(cnf_transformation,[],[f154])).

cnf(c_54,plain,
    ( ~ sP2(X0,X1)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f155])).

cnf(c_53,plain,
    ( ~ sP2(X0,X1)
    | v10_lattices(X0) ),
    inference(cnf_transformation,[],[f156])).

cnf(c_50,plain,
    ( ~ sP2(X0,X1)
    | l3_lattices(X0) ),
    inference(cnf_transformation,[],[f159])).

cnf(c_10,plain,
    ( ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | v10_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_611,plain,
    ( ~ sP2(X0,X1)
    | v10_lattices(k7_filter_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_47,c_59,c_58,c_55,c_54,c_53,c_50,c_10])).

cnf(c_2274,plain,
    ( ~ sP2(X0_55,X1_55)
    | v10_lattices(k7_filter_1(X1_55,X0_55)) ),
    inference(subtyping,[status(esa)],[c_611])).

cnf(c_3409,plain,
    ( sP2(X0_55,X1_55) != iProver_top
    | v10_lattices(k7_filter_1(X1_55,X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2274])).

cnf(c_61,negated_conjecture,
    ( ~ v10_lattices(k7_filter_1(sK11,sK12))
    | ~ v10_lattices(sK12)
    | ~ v10_lattices(sK11)
    | ~ l3_lattices(k7_filter_1(sK11,sK12))
    | ~ l3_lattices(sK12)
    | ~ l3_lattices(sK11)
    | v2_struct_0(k7_filter_1(sK11,sK12))
    | v2_struct_0(sK12)
    | v2_struct_0(sK11)
    | ~ v17_lattices(k7_filter_1(sK11,sK12))
    | ~ v17_lattices(sK12)
    | ~ v17_lattices(sK11) ),
    inference(cnf_transformation,[],[f200])).

cnf(c_99,negated_conjecture,
    ( ~ v2_struct_0(sK11) ),
    inference(cnf_transformation,[],[f162])).

cnf(c_98,negated_conjecture,
    ( v10_lattices(sK11) ),
    inference(cnf_transformation,[],[f163])).

cnf(c_97,negated_conjecture,
    ( l3_lattices(sK11) ),
    inference(cnf_transformation,[],[f164])).

cnf(c_96,negated_conjecture,
    ( ~ v2_struct_0(sK12) ),
    inference(cnf_transformation,[],[f165])).

cnf(c_95,negated_conjecture,
    ( v10_lattices(sK12) ),
    inference(cnf_transformation,[],[f166])).

cnf(c_94,negated_conjecture,
    ( l3_lattices(sK12) ),
    inference(cnf_transformation,[],[f167])).

cnf(c_587,negated_conjecture,
    ( ~ v10_lattices(k7_filter_1(sK11,sK12))
    | ~ l3_lattices(k7_filter_1(sK11,sK12))
    | v2_struct_0(k7_filter_1(sK11,sK12))
    | ~ v17_lattices(k7_filter_1(sK11,sK12))
    | ~ v17_lattices(sK12)
    | ~ v17_lattices(sK11) ),
    inference(global_propositional_subsumption,[status(thm)],[c_61,c_99,c_98,c_97,c_96,c_95,c_94])).

cnf(c_2276,negated_conjecture,
    ( ~ v10_lattices(k7_filter_1(sK11,sK12))
    | ~ l3_lattices(k7_filter_1(sK11,sK12))
    | v2_struct_0(k7_filter_1(sK11,sK12))
    | ~ v17_lattices(k7_filter_1(sK11,sK12))
    | ~ v17_lattices(sK12)
    | ~ v17_lattices(sK11) ),
    inference(subtyping,[status(esa)],[c_587])).

cnf(c_3407,plain,
    ( v10_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | l3_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | v2_struct_0(k7_filter_1(sK11,sK12)) = iProver_top
    | v17_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | v17_lattices(sK12) != iProver_top
    | v17_lattices(sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2276])).

cnf(c_6631,plain,
    ( sP2(sK12,sK11) != iProver_top
    | l3_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | v2_struct_0(k7_filter_1(sK11,sK12)) = iProver_top
    | v17_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | v17_lattices(sK12) != iProver_top
    | v17_lattices(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_3409,c_3407])).

cnf(c_100,plain,
    ( v2_struct_0(sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99])).

cnf(c_101,plain,
    ( v10_lattices(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_98])).

cnf(c_102,plain,
    ( l3_lattices(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_97])).

cnf(c_103,plain,
    ( v2_struct_0(sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_96])).

cnf(c_104,plain,
    ( v10_lattices(sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_95])).

cnf(c_105,plain,
    ( l3_lattices(sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_94])).

cnf(c_589,plain,
    ( v10_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | l3_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | v2_struct_0(k7_filter_1(sK11,sK12)) = iProver_top
    | v17_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | v17_lattices(sK12) != iProver_top
    | v17_lattices(sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_4,plain,
    ( ~ v11_lattices(X0)
    | ~ v15_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | v17_lattices(X0)
    | ~ v16_lattices(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2324,plain,
    ( ~ v11_lattices(X0_55)
    | ~ v15_lattices(X0_55)
    | ~ l3_lattices(X0_55)
    | v2_struct_0(X0_55)
    | v17_lattices(X0_55)
    | ~ v16_lattices(X0_55) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3970,plain,
    ( ~ v11_lattices(k7_filter_1(sK11,sK12))
    | ~ v15_lattices(k7_filter_1(sK11,sK12))
    | ~ l3_lattices(k7_filter_1(sK11,sK12))
    | v2_struct_0(k7_filter_1(sK11,sK12))
    | v17_lattices(k7_filter_1(sK11,sK12))
    | ~ v16_lattices(k7_filter_1(sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_2324])).

cnf(c_3971,plain,
    ( v11_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | v15_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | l3_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | v2_struct_0(k7_filter_1(sK11,sK12)) = iProver_top
    | v17_lattices(k7_filter_1(sK11,sK12)) = iProver_top
    | v16_lattices(k7_filter_1(sK11,sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3970])).

cnf(c_60,plain,
    ( sP3(X0,X1)
    | ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f161])).

cnf(c_43,plain,
    ( ~ sP3(X0,X1)
    | sP2(X0,X1)
    | ~ v10_lattices(k7_filter_1(X1,X0))
    | ~ v15_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(k7_filter_1(X1,X0))
    | ~ v16_lattices(k7_filter_1(X1,X0)) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_1100,plain,
    ( sP2(X0,X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ v10_lattices(k7_filter_1(X1,X0))
    | ~ v15_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k7_filter_1(X1,X0))
    | ~ v16_lattices(k7_filter_1(X1,X0)) ),
    inference(resolution,[status(thm)],[c_60,c_43])).

cnf(c_1104,plain,
    ( ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | sP2(X0,X1)
    | ~ v15_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k7_filter_1(X1,X0))
    | ~ v16_lattices(k7_filter_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1100,c_60,c_43,c_10])).

cnf(c_1105,plain,
    ( sP2(X0,X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ v15_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k7_filter_1(X1,X0))
    | ~ v16_lattices(k7_filter_1(X1,X0)) ),
    inference(renaming,[status(thm)],[c_1104])).

cnf(c_9,plain,
    ( ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k7_filter_1(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_7,plain,
    ( ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | l3_lattices(k7_filter_1(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1132,plain,
    ( sP2(X0,X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ v15_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v16_lattices(k7_filter_1(X1,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1105,c_9,c_7])).

cnf(c_2270,plain,
    ( sP2(X0_55,X1_55)
    | ~ v10_lattices(X0_55)
    | ~ v10_lattices(X1_55)
    | ~ v15_lattices(k7_filter_1(X1_55,X0_55))
    | ~ l3_lattices(X1_55)
    | ~ l3_lattices(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | ~ v16_lattices(k7_filter_1(X1_55,X0_55)) ),
    inference(subtyping,[status(esa)],[c_1132])).

cnf(c_4014,plain,
    ( sP2(sK12,sK11)
    | ~ v10_lattices(sK12)
    | ~ v10_lattices(sK11)
    | ~ v15_lattices(k7_filter_1(sK11,sK12))
    | ~ l3_lattices(sK12)
    | ~ l3_lattices(sK11)
    | v2_struct_0(sK12)
    | v2_struct_0(sK11)
    | ~ v16_lattices(k7_filter_1(sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_2270])).

cnf(c_4015,plain,
    ( sP2(sK12,sK11) = iProver_top
    | v10_lattices(sK12) != iProver_top
    | v10_lattices(sK11) != iProver_top
    | v15_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | l3_lattices(sK12) != iProver_top
    | l3_lattices(sK11) != iProver_top
    | v2_struct_0(sK12) = iProver_top
    | v2_struct_0(sK11) = iProver_top
    | v16_lattices(k7_filter_1(sK11,sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4014])).

cnf(c_2322,plain,
    ( ~ l3_lattices(X0_55)
    | ~ l3_lattices(X1_55)
    | l3_lattices(k7_filter_1(X0_55,X1_55))
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_4050,plain,
    ( l3_lattices(k7_filter_1(sK11,sK12))
    | ~ l3_lattices(sK12)
    | ~ l3_lattices(sK11)
    | v2_struct_0(sK12)
    | v2_struct_0(sK11) ),
    inference(instantiation,[status(thm)],[c_2322])).

cnf(c_4051,plain,
    ( l3_lattices(k7_filter_1(sK11,sK12)) = iProver_top
    | l3_lattices(sK12) != iProver_top
    | l3_lattices(sK11) != iProver_top
    | v2_struct_0(sK12) = iProver_top
    | v2_struct_0(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4050])).

cnf(c_33,plain,
    ( sP0(X0,X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ v11_lattices(X0)
    | ~ v11_lattices(X1)
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_30,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X0,X1)
    | v11_lattices(k7_filter_1(X1,X0)) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_42,plain,
    ( sP1(X0,X1)
    | ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_41,plain,
    ( ~ sP0(X0,X1)
    | ~ v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_40,plain,
    ( ~ sP0(X0,X1)
    | v10_lattices(X1) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_38,plain,
    ( ~ sP0(X0,X1)
    | l3_lattices(X1) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_37,plain,
    ( ~ sP0(X0,X1)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_36,plain,
    ( ~ sP0(X0,X1)
    | v10_lattices(X0) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_34,plain,
    ( ~ sP0(X0,X1)
    | l3_lattices(X0) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_664,plain,
    ( ~ sP0(X0,X1)
    | v11_lattices(k7_filter_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_42,c_41,c_40,c_38,c_37,c_36,c_34])).

cnf(c_1236,plain,
    ( ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | ~ v11_lattices(X1)
    | ~ v11_lattices(X0)
    | v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_33,c_664])).

cnf(c_2267,plain,
    ( ~ v10_lattices(X0_55)
    | ~ v10_lattices(X1_55)
    | ~ v11_lattices(X1_55)
    | ~ v11_lattices(X0_55)
    | v11_lattices(k7_filter_1(X1_55,X0_55))
    | ~ l3_lattices(X1_55)
    | ~ l3_lattices(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_1236])).

cnf(c_4178,plain,
    ( ~ v10_lattices(sK12)
    | ~ v10_lattices(sK11)
    | v11_lattices(k7_filter_1(sK11,sK12))
    | ~ v11_lattices(sK12)
    | ~ v11_lattices(sK11)
    | ~ l3_lattices(sK12)
    | ~ l3_lattices(sK11)
    | v2_struct_0(sK12)
    | v2_struct_0(sK11) ),
    inference(instantiation,[status(thm)],[c_2267])).

cnf(c_4179,plain,
    ( v10_lattices(sK12) != iProver_top
    | v10_lattices(sK11) != iProver_top
    | v11_lattices(k7_filter_1(sK11,sK12)) = iProver_top
    | v11_lattices(sK12) != iProver_top
    | v11_lattices(sK11) != iProver_top
    | l3_lattices(sK12) != iProver_top
    | l3_lattices(sK11) != iProver_top
    | v2_struct_0(sK12) = iProver_top
    | v2_struct_0(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4178])).

cnf(c_67,negated_conjecture,
    ( l3_lattices(k7_filter_1(sK11,sK12))
    | v17_lattices(sK11) ),
    inference(cnf_transformation,[],[f194])).

cnf(c_2289,negated_conjecture,
    ( l3_lattices(k7_filter_1(sK11,sK12))
    | v17_lattices(sK11) ),
    inference(subtyping,[status(esa)],[c_67])).

cnf(c_3394,plain,
    ( l3_lattices(k7_filter_1(sK11,sK12)) = iProver_top
    | v17_lattices(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2289])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v17_lattices(X0)
    | v16_lattices(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2327,plain,
    ( ~ l3_lattices(X0_55)
    | v2_struct_0(X0_55)
    | ~ v17_lattices(X0_55)
    | v16_lattices(X0_55) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3356,plain,
    ( l3_lattices(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v17_lattices(X0_55) != iProver_top
    | v16_lattices(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2327])).

cnf(c_3991,plain,
    ( v2_struct_0(k7_filter_1(sK11,sK12)) = iProver_top
    | v17_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | v17_lattices(sK11) = iProver_top
    | v16_lattices(k7_filter_1(sK11,sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3394,c_3356])).

cnf(c_91,negated_conjecture,
    ( ~ v2_struct_0(k7_filter_1(sK11,sK12))
    | v17_lattices(sK11) ),
    inference(cnf_transformation,[],[f170])).

cnf(c_108,plain,
    ( v2_struct_0(k7_filter_1(sK11,sK12)) != iProver_top
    | v17_lattices(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_91])).

cnf(c_75,negated_conjecture,
    ( v17_lattices(k7_filter_1(sK11,sK12))
    | v17_lattices(sK11) ),
    inference(cnf_transformation,[],[f186])).

cnf(c_124,plain,
    ( v17_lattices(k7_filter_1(sK11,sK12)) = iProver_top
    | v17_lattices(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_75])).

cnf(c_4464,plain,
    ( v17_lattices(sK11) = iProver_top
    | v16_lattices(k7_filter_1(sK11,sK12)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3991,c_108,c_124])).

cnf(c_2282,negated_conjecture,
    ( l3_lattices(sK12) ),
    inference(subtyping,[status(esa)],[c_94])).

cnf(c_3401,plain,
    ( l3_lattices(sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2282])).

cnf(c_3919,plain,
    ( v2_struct_0(sK12) = iProver_top
    | v17_lattices(sK12) != iProver_top
    | v16_lattices(sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_3401,c_3356])).

cnf(c_2279,negated_conjecture,
    ( l3_lattices(sK11) ),
    inference(subtyping,[status(esa)],[c_97])).

cnf(c_3404,plain,
    ( l3_lattices(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2279])).

cnf(c_3920,plain,
    ( v2_struct_0(sK11) = iProver_top
    | v17_lattices(sK11) != iProver_top
    | v16_lattices(sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_3404,c_3356])).

cnf(c_1,plain,
    ( v15_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v17_lattices(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2326,plain,
    ( v15_lattices(X0_55)
    | ~ l3_lattices(X0_55)
    | v2_struct_0(X0_55)
    | ~ v17_lattices(X0_55) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3357,plain,
    ( v15_lattices(X0_55) = iProver_top
    | l3_lattices(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v17_lattices(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2326])).

cnf(c_4098,plain,
    ( v15_lattices(sK12) = iProver_top
    | v2_struct_0(sK12) = iProver_top
    | v17_lattices(sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_3401,c_3357])).

cnf(c_4099,plain,
    ( v15_lattices(sK11) = iProver_top
    | v2_struct_0(sK11) = iProver_top
    | v17_lattices(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_3404,c_3357])).

cnf(c_49,plain,
    ( sP2(X0,X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ v15_lattices(X0)
    | ~ v15_lattices(X1)
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v16_lattices(X0)
    | ~ v16_lattices(X1) ),
    inference(cnf_transformation,[],[f160])).

cnf(c_2301,plain,
    ( sP2(X0_55,X1_55)
    | ~ v10_lattices(X0_55)
    | ~ v10_lattices(X1_55)
    | ~ v15_lattices(X0_55)
    | ~ v15_lattices(X1_55)
    | ~ l3_lattices(X1_55)
    | ~ l3_lattices(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | ~ v16_lattices(X0_55)
    | ~ v16_lattices(X1_55) ),
    inference(subtyping,[status(esa)],[c_49])).

cnf(c_4144,plain,
    ( sP2(sK12,sK11)
    | ~ v10_lattices(sK12)
    | ~ v10_lattices(sK11)
    | ~ v15_lattices(sK12)
    | ~ v15_lattices(sK11)
    | ~ l3_lattices(sK12)
    | ~ l3_lattices(sK11)
    | v2_struct_0(sK12)
    | v2_struct_0(sK11)
    | ~ v16_lattices(sK12)
    | ~ v16_lattices(sK11) ),
    inference(instantiation,[status(thm)],[c_2301])).

cnf(c_4146,plain,
    ( sP2(sK12,sK11) = iProver_top
    | v10_lattices(sK12) != iProver_top
    | v10_lattices(sK11) != iProver_top
    | v15_lattices(sK12) != iProver_top
    | v15_lattices(sK11) != iProver_top
    | l3_lattices(sK12) != iProver_top
    | l3_lattices(sK11) != iProver_top
    | v2_struct_0(sK12) = iProver_top
    | v2_struct_0(sK11) = iProver_top
    | v16_lattices(sK12) != iProver_top
    | v16_lattices(sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4144])).

cnf(c_45,plain,
    ( ~ sP3(X0,X1)
    | ~ sP2(X0,X1)
    | v16_lattices(k7_filter_1(X1,X0)) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_625,plain,
    ( ~ sP2(X0,X1)
    | v16_lattices(k7_filter_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_45,c_60,c_59,c_58,c_55,c_54,c_53,c_50])).

cnf(c_2272,plain,
    ( ~ sP2(X0_55,X1_55)
    | v16_lattices(k7_filter_1(X1_55,X0_55)) ),
    inference(subtyping,[status(esa)],[c_625])).

cnf(c_4342,plain,
    ( ~ sP2(sK12,sK11)
    | v16_lattices(k7_filter_1(sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_2272])).

cnf(c_4343,plain,
    ( sP2(sK12,sK11) != iProver_top
    | v16_lattices(k7_filter_1(sK11,sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4342])).

cnf(c_63,negated_conjecture,
    ( l3_lattices(k7_filter_1(sK11,sK12))
    | v17_lattices(sK12) ),
    inference(cnf_transformation,[],[f198])).

cnf(c_2290,negated_conjecture,
    ( l3_lattices(k7_filter_1(sK11,sK12))
    | v17_lattices(sK12) ),
    inference(subtyping,[status(esa)],[c_63])).

cnf(c_3393,plain,
    ( l3_lattices(k7_filter_1(sK11,sK12)) = iProver_top
    | v17_lattices(sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2290])).

cnf(c_3986,plain,
    ( v2_struct_0(k7_filter_1(sK11,sK12)) = iProver_top
    | v17_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | v17_lattices(sK12) = iProver_top
    | v16_lattices(k7_filter_1(sK11,sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3393,c_3356])).

cnf(c_87,negated_conjecture,
    ( ~ v2_struct_0(k7_filter_1(sK11,sK12))
    | v17_lattices(sK12) ),
    inference(cnf_transformation,[],[f174])).

cnf(c_112,plain,
    ( v2_struct_0(k7_filter_1(sK11,sK12)) != iProver_top
    | v17_lattices(sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_87])).

cnf(c_71,negated_conjecture,
    ( v17_lattices(k7_filter_1(sK11,sK12))
    | v17_lattices(sK12) ),
    inference(cnf_transformation,[],[f190])).

cnf(c_128,plain,
    ( v17_lattices(k7_filter_1(sK11,sK12)) = iProver_top
    | v17_lattices(sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_4374,plain,
    ( v17_lattices(sK12) = iProver_top
    | v16_lattices(k7_filter_1(sK11,sK12)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3986,c_112,c_128])).

cnf(c_4468,plain,
    ( v16_lattices(k7_filter_1(sK11,sK12)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4464,c_100,c_101,c_102,c_103,c_104,c_105,c_3919,c_3920,c_4098,c_4099,c_4146,c_4343,c_4374])).

cnf(c_2319,plain,
    ( ~ v10_lattices(X0_55)
    | ~ v10_lattices(X1_55)
    | v10_lattices(k7_filter_1(X1_55,X0_55))
    | ~ l3_lattices(X1_55)
    | ~ l3_lattices(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_4529,plain,
    ( v10_lattices(k7_filter_1(sK11,sK12))
    | ~ v10_lattices(sK12)
    | ~ v10_lattices(sK11)
    | ~ l3_lattices(sK12)
    | ~ l3_lattices(sK11)
    | v2_struct_0(sK12)
    | v2_struct_0(sK11) ),
    inference(instantiation,[status(thm)],[c_2319])).

cnf(c_4533,plain,
    ( v10_lattices(k7_filter_1(sK11,sK12)) = iProver_top
    | v10_lattices(sK12) != iProver_top
    | v10_lattices(sK11) != iProver_top
    | l3_lattices(sK12) != iProver_top
    | l3_lattices(sK11) != iProver_top
    | v2_struct_0(sK12) = iProver_top
    | v2_struct_0(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4529])).

cnf(c_4097,plain,
    ( v15_lattices(k7_filter_1(sK11,sK12)) = iProver_top
    | v2_struct_0(k7_filter_1(sK11,sK12)) = iProver_top
    | v17_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | v17_lattices(sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_3393,c_3357])).

cnf(c_46,plain,
    ( ~ sP3(X0,X1)
    | ~ sP2(X0,X1)
    | v15_lattices(k7_filter_1(X1,X0)) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_618,plain,
    ( ~ sP2(X0,X1)
    | v15_lattices(k7_filter_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_46,c_60,c_59,c_58,c_55,c_54,c_53,c_50])).

cnf(c_2273,plain,
    ( ~ sP2(X0_55,X1_55)
    | v15_lattices(k7_filter_1(X1_55,X0_55)) ),
    inference(subtyping,[status(esa)],[c_618])).

cnf(c_4220,plain,
    ( ~ sP2(sK12,sK11)
    | v15_lattices(k7_filter_1(sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_2273])).

cnf(c_4221,plain,
    ( sP2(sK12,sK11) != iProver_top
    | v15_lattices(k7_filter_1(sK11,sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4220])).

cnf(c_4096,plain,
    ( v15_lattices(k7_filter_1(sK11,sK12)) = iProver_top
    | v2_struct_0(k7_filter_1(sK11,sK12)) = iProver_top
    | v17_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | v17_lattices(sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_3394,c_3357])).

cnf(c_4474,plain,
    ( v15_lattices(k7_filter_1(sK11,sK12)) = iProver_top
    | v17_lattices(sK11) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4096,c_100,c_101,c_102,c_103,c_104,c_105,c_108,c_112,c_124,c_128,c_3919,c_3920,c_4097,c_4098,c_4099,c_4146,c_4221])).

cnf(c_4536,plain,
    ( v15_lattices(k7_filter_1(sK11,sK12)) = iProver_top
    | v17_lattices(sK12) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4097,c_100,c_101,c_102,c_103,c_104,c_105,c_108,c_112,c_124,c_128,c_3919,c_3920,c_4096,c_4098,c_4099,c_4146,c_4221])).

cnf(c_4540,plain,
    ( v15_lattices(k7_filter_1(sK11,sK12)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4536,c_100,c_101,c_102,c_103,c_104,c_105,c_108,c_112,c_124,c_128,c_3919,c_3920,c_4096,c_4097,c_4098,c_4099,c_4146,c_4221])).

cnf(c_2,plain,
    ( v11_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v17_lattices(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2325,plain,
    ( v11_lattices(X0_55)
    | ~ l3_lattices(X0_55)
    | v2_struct_0(X0_55)
    | ~ v17_lattices(X0_55) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3358,plain,
    ( v11_lattices(X0_55) = iProver_top
    | l3_lattices(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v17_lattices(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2325])).

cnf(c_4555,plain,
    ( v11_lattices(sK12) = iProver_top
    | v2_struct_0(sK12) = iProver_top
    | v17_lattices(sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_3401,c_3358])).

cnf(c_3889,plain,
    ( v11_lattices(k7_filter_1(sK11,sK12))
    | ~ l3_lattices(k7_filter_1(sK11,sK12))
    | v2_struct_0(k7_filter_1(sK11,sK12))
    | ~ v17_lattices(k7_filter_1(sK11,sK12)) ),
    inference(instantiation,[status(thm)],[c_2325])).

cnf(c_3890,plain,
    ( v11_lattices(k7_filter_1(sK11,sK12)) = iProver_top
    | l3_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | v2_struct_0(k7_filter_1(sK11,sK12)) = iProver_top
    | v17_lattices(k7_filter_1(sK11,sK12)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3889])).

cnf(c_28,plain,
    ( ~ sP1(X0,X1)
    | sP0(X0,X1)
    | ~ v10_lattices(k7_filter_1(X1,X0))
    | ~ v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(k7_filter_1(X1,X0)) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_1049,plain,
    ( sP0(X0,X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ v10_lattices(k7_filter_1(X1,X0))
    | ~ v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k7_filter_1(X1,X0)) ),
    inference(resolution,[status(thm)],[c_42,c_28])).

cnf(c_1053,plain,
    ( ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | sP0(X0,X1)
    | ~ v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k7_filter_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1049,c_10])).

cnf(c_1054,plain,
    ( sP0(X0,X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | ~ l3_lattices(k7_filter_1(X1,X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(k7_filter_1(X1,X0)) ),
    inference(renaming,[status(thm)],[c_1053])).

cnf(c_1079,plain,
    ( sP0(X0,X1)
    | ~ v10_lattices(X1)
    | ~ v10_lattices(X0)
    | ~ v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X0)
    | ~ l3_lattices(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1054,c_9,c_7])).

cnf(c_35,plain,
    ( ~ sP0(X0,X1)
    | v11_lattices(X0) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_1204,plain,
    ( ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | v11_lattices(X0)
    | ~ v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_1079,c_35])).

cnf(c_2268,plain,
    ( ~ v10_lattices(X0_55)
    | ~ v10_lattices(X1_55)
    | v11_lattices(X0_55)
    | ~ v11_lattices(k7_filter_1(X1_55,X0_55))
    | ~ l3_lattices(X1_55)
    | ~ l3_lattices(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_1204])).

cnf(c_3978,plain,
    ( ~ v10_lattices(sK12)
    | ~ v10_lattices(sK11)
    | ~ v11_lattices(k7_filter_1(sK11,sK12))
    | v11_lattices(sK12)
    | ~ l3_lattices(sK12)
    | ~ l3_lattices(sK11)
    | v2_struct_0(sK12)
    | v2_struct_0(sK11) ),
    inference(instantiation,[status(thm)],[c_2268])).

cnf(c_3979,plain,
    ( v10_lattices(sK12) != iProver_top
    | v10_lattices(sK11) != iProver_top
    | v11_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | v11_lattices(sK12) = iProver_top
    | l3_lattices(sK12) != iProver_top
    | l3_lattices(sK11) != iProver_top
    | v2_struct_0(sK12) = iProver_top
    | v2_struct_0(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3978])).

cnf(c_4800,plain,
    ( v11_lattices(sK12) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4555,c_100,c_101,c_102,c_103,c_104,c_105,c_112,c_128,c_3890,c_3979,c_4051])).

cnf(c_4556,plain,
    ( v11_lattices(sK11) = iProver_top
    | v2_struct_0(sK11) = iProver_top
    | v17_lattices(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_3404,c_3358])).

cnf(c_39,plain,
    ( ~ sP0(X0,X1)
    | v11_lattices(X1) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_1172,plain,
    ( ~ v10_lattices(X0)
    | ~ v10_lattices(X1)
    | v11_lattices(X1)
    | ~ v11_lattices(k7_filter_1(X1,X0))
    | ~ l3_lattices(X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_1079,c_39])).

cnf(c_2269,plain,
    ( ~ v10_lattices(X0_55)
    | ~ v10_lattices(X1_55)
    | v11_lattices(X1_55)
    | ~ v11_lattices(k7_filter_1(X1_55,X0_55))
    | ~ l3_lattices(X1_55)
    | ~ l3_lattices(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_1172])).

cnf(c_3977,plain,
    ( ~ v10_lattices(sK12)
    | ~ v10_lattices(sK11)
    | ~ v11_lattices(k7_filter_1(sK11,sK12))
    | v11_lattices(sK11)
    | ~ l3_lattices(sK12)
    | ~ l3_lattices(sK11)
    | v2_struct_0(sK12)
    | v2_struct_0(sK11) ),
    inference(instantiation,[status(thm)],[c_2269])).

cnf(c_3981,plain,
    ( v10_lattices(sK12) != iProver_top
    | v10_lattices(sK11) != iProver_top
    | v11_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | v11_lattices(sK11) = iProver_top
    | l3_lattices(sK12) != iProver_top
    | l3_lattices(sK11) != iProver_top
    | v2_struct_0(sK12) = iProver_top
    | v2_struct_0(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3977])).

cnf(c_4553,plain,
    ( v11_lattices(k7_filter_1(sK11,sK12)) = iProver_top
    | v2_struct_0(k7_filter_1(sK11,sK12)) = iProver_top
    | v17_lattices(k7_filter_1(sK11,sK12)) != iProver_top
    | v17_lattices(sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_3394,c_3358])).

cnf(c_4806,plain,
    ( v11_lattices(sK11) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4556,c_100,c_101,c_102,c_103,c_104,c_105,c_108,c_124,c_3981,c_4553])).

cnf(c_3359,plain,
    ( v11_lattices(X0_55) != iProver_top
    | v15_lattices(X0_55) != iProver_top
    | l3_lattices(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v17_lattices(X0_55) = iProver_top
    | v16_lattices(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2324])).

cnf(c_5091,plain,
    ( v11_lattices(sK12) != iProver_top
    | v15_lattices(sK12) != iProver_top
    | v2_struct_0(sK12) = iProver_top
    | v17_lattices(sK12) = iProver_top
    | v16_lattices(sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_3401,c_3359])).

cnf(c_5242,plain,
    ( v15_lattices(sK12) != iProver_top
    | v17_lattices(sK12) = iProver_top
    | v16_lattices(sK12) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5091,c_100,c_101,c_102,c_103,c_104,c_105,c_112,c_128,c_3890,c_3979,c_4051,c_4555])).

cnf(c_5092,plain,
    ( v11_lattices(sK11) != iProver_top
    | v15_lattices(sK11) != iProver_top
    | v2_struct_0(sK11) = iProver_top
    | v17_lattices(sK11) = iProver_top
    | v16_lattices(sK11) != iProver_top ),
    inference(superposition,[status(thm)],[c_3404,c_3359])).

cnf(c_57,plain,
    ( ~ sP2(X0,X1)
    | v15_lattices(X1) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_2293,plain,
    ( ~ sP2(X0_55,X1_55)
    | v15_lattices(X1_55) ),
    inference(subtyping,[status(esa)],[c_57])).

cnf(c_5235,plain,
    ( ~ sP2(sK12,sK11)
    | v15_lattices(sK11) ),
    inference(instantiation,[status(thm)],[c_2293])).

cnf(c_5236,plain,
    ( sP2(sK12,sK11) != iProver_top
    | v15_lattices(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5235])).

cnf(c_5250,plain,
    ( v17_lattices(sK11) = iProver_top
    | v16_lattices(sK11) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5092,c_100,c_101,c_102,c_103,c_104,c_105,c_108,c_112,c_124,c_128,c_3919,c_3920,c_3981,c_4015,c_4096,c_4097,c_4098,c_4099,c_4146,c_4221,c_4343,c_4374,c_4464,c_4553,c_4556,c_5236])).

cnf(c_52,plain,
    ( ~ sP2(X0,X1)
    | v15_lattices(X0) ),
    inference(cnf_transformation,[],[f157])).

cnf(c_2298,plain,
    ( ~ sP2(X0_55,X1_55)
    | v15_lattices(X0_55) ),
    inference(subtyping,[status(esa)],[c_52])).

cnf(c_5274,plain,
    ( ~ sP2(sK12,sK11)
    | v15_lattices(sK12) ),
    inference(instantiation,[status(thm)],[c_2298])).

cnf(c_5275,plain,
    ( sP2(sK12,sK11) != iProver_top
    | v15_lattices(sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5274])).

cnf(c_56,plain,
    ( ~ sP2(X0,X1)
    | v16_lattices(X1) ),
    inference(cnf_transformation,[],[f153])).

cnf(c_2294,plain,
    ( ~ sP2(X0_55,X1_55)
    | v16_lattices(X1_55) ),
    inference(subtyping,[status(esa)],[c_56])).

cnf(c_6398,plain,
    ( ~ sP2(sK12,sK11)
    | v16_lattices(sK11) ),
    inference(instantiation,[status(thm)],[c_2294])).

cnf(c_6399,plain,
    ( sP2(sK12,sK11) != iProver_top
    | v16_lattices(sK11) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6398])).

cnf(c_51,plain,
    ( ~ sP2(X0,X1)
    | v16_lattices(X0) ),
    inference(cnf_transformation,[],[f158])).

cnf(c_2299,plain,
    ( ~ sP2(X0_55,X1_55)
    | v16_lattices(X0_55) ),
    inference(subtyping,[status(esa)],[c_51])).

cnf(c_6411,plain,
    ( ~ sP2(sK12,sK11)
    | v16_lattices(sK12) ),
    inference(instantiation,[status(thm)],[c_2299])).

cnf(c_6412,plain,
    ( sP2(sK12,sK11) != iProver_top
    | v16_lattices(sK12) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6411])).

cnf(c_6740,plain,
    ( v2_struct_0(k7_filter_1(sK11,sK12)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6631,c_100,c_101,c_102,c_103,c_104,c_105,c_108,c_112,c_124,c_128,c_589,c_3890,c_3919,c_3920,c_3971,c_3979,c_3981,c_4015,c_4051,c_4096,c_4097,c_4098,c_4099,c_4146,c_4179,c_4221,c_4343,c_4374,c_4464,c_4531,c_4553,c_4555,c_4556,c_5242,c_5250,c_5275,c_6399,c_6412])).

cnf(c_2320,plain,
    ( ~ l3_lattices(X0_55)
    | ~ l3_lattices(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | ~ v2_struct_0(k7_filter_1(X0_55,X1_55)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3363,plain,
    ( l3_lattices(X0_55) != iProver_top
    | l3_lattices(X1_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(k7_filter_1(X1_55,X0_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2320])).

cnf(c_6747,plain,
    ( l3_lattices(sK12) != iProver_top
    | l3_lattices(sK11) != iProver_top
    | v2_struct_0(sK12) = iProver_top
    | v2_struct_0(sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_6740,c_3363])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6747,c_105,c_103,c_102,c_100])).


%------------------------------------------------------------------------------
