%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 306 expanded)
%              Number of leaves         :   17 (  98 expanded)
%              Depth                    :   18
%              Number of atoms          :  516 (1612 expanded)
%              Number of equality atoms :   50 ( 252 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f375,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f290,f298,f304,f312,f344,f360,f374])).

fof(f374,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f373])).

fof(f373,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f372,f41])).

fof(f41,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,X1),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v17_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,X1),X1)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattices)).

fof(f372,plain,
    ( ~ l3_lattices(sK0)
    | spl3_6 ),
    inference(subsumption_resolution,[],[f371,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f371,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl3_6 ),
    inference(subsumption_resolution,[],[f368,f40])).

fof(f40,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f368,plain,
    ( ~ v17_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl3_6 ),
    inference(resolution,[],[f343,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v16_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_lattices)).

fof(f343,plain,
    ( ~ v16_lattices(sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl3_6
  <=> v16_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f360,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f359])).

fof(f359,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f358,f41])).

fof(f358,plain,
    ( ~ l3_lattices(sK0)
    | spl3_5 ),
    inference(subsumption_resolution,[],[f357,f38])).

fof(f357,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl3_5 ),
    inference(subsumption_resolution,[],[f354,f40])).

fof(f354,plain,
    ( ~ v17_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl3_5 ),
    inference(resolution,[],[f339,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f339,plain,
    ( ~ v11_lattices(sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl3_5
  <=> v11_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f344,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f328,f287,f283,f341,f337])).

fof(f283,plain,
    ( spl3_3
  <=> m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f287,plain,
    ( spl3_4
  <=> sQ2_eqProxy(k2_lattices(sK0,k7_lattices(sK0,sK1),sK1),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f328,plain,
    ( ~ v16_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f327,f42])).

fof(f42,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f327,plain,
    ( ~ v16_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f326,f38])).

fof(f326,plain,
    ( ~ v16_lattices(sK0)
    | ~ v11_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f325,f39])).

fof(f39,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f325,plain,
    ( ~ v16_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f322,f41])).

fof(f322,plain,
    ( ~ l3_lattices(sK0)
    | ~ v16_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_3
    | spl3_4 ),
    inference(resolution,[],[f321,f170])).

fof(f170,plain,(
    ! [X0,X1] :
      ( r2_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f96,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_lattices(X0,X2,X1)
      | k7_lattices(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_lattices(X0,X1) = X2
                  | ~ r2_lattices(X0,X2,X1) )
                & ( r2_lattices(X0,X2,X1)
                  | k7_lattices(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l3_lattices(X0)
          | ~ v16_lattices(X0)
          | ~ v11_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_lattices(X0,X1) = X2
              <=> r2_lattices(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l3_lattices(X0)
          | ~ v16_lattices(X0)
          | ~ v11_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_lattices(X0,X1) = X2
              <=> r2_lattices(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l3_lattices(X0)
          | ~ v16_lattices(X0)
          | ~ v11_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( ( l3_lattices(X0)
              & v16_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k7_lattices(X0,X1) = X2
                <=> r2_lattices(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattices)).

fof(f321,plain,
    ( ~ r2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f320,f38])).

fof(f320,plain,
    ( ~ r2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | v2_struct_0(sK0)
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f319,f41])).

fof(f319,plain,
    ( ~ r2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f318,f284])).

fof(f284,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f283])).

fof(f318,plain,
    ( ~ r2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl3_4 ),
    inference(subsumption_resolution,[],[f315,f42])).

fof(f315,plain,
    ( ~ r2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl3_4 ),
    inference(resolution,[],[f289,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( sQ2_eqProxy(k2_lattices(X0,X1,X2),k5_lattices(X0))
      | ~ r2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f54,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( sQ2_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = k5_lattices(X0)
      | ~ r2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattices(X0,X1,X2)
                  | k5_lattices(X0) != k2_lattices(X0,X2,X1)
                  | k2_lattices(X0,X1,X2) != k5_lattices(X0)
                  | k6_lattices(X0) != k1_lattices(X0,X2,X1)
                  | k1_lattices(X0,X1,X2) != k6_lattices(X0) )
                & ( ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
                    & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                    & k6_lattices(X0) = k1_lattices(X0,X2,X1)
                    & k1_lattices(X0,X1,X2) = k6_lattices(X0) )
                  | ~ r2_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattices(X0,X1,X2)
                  | k5_lattices(X0) != k2_lattices(X0,X2,X1)
                  | k2_lattices(X0,X1,X2) != k5_lattices(X0)
                  | k6_lattices(X0) != k1_lattices(X0,X2,X1)
                  | k1_lattices(X0,X1,X2) != k6_lattices(X0) )
                & ( ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
                    & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                    & k6_lattices(X0) = k1_lattices(X0,X2,X1)
                    & k1_lattices(X0,X1,X2) = k6_lattices(X0) )
                  | ~ r2_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_lattices(X0,X1,X2)
              <=> ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
                  & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                  & k6_lattices(X0) = k1_lattices(X0,X2,X1)
                  & k1_lattices(X0,X1,X2) = k6_lattices(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_lattices(X0,X1,X2)
              <=> ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
                  & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                  & k6_lattices(X0) = k1_lattices(X0,X2,X1)
                  & k1_lattices(X0,X1,X2) = k6_lattices(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_lattices(X0,X1,X2)
              <=> ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
                  & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                  & k6_lattices(X0) = k1_lattices(X0,X2,X1)
                  & k1_lattices(X0,X1,X2) = k6_lattices(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_lattices)).

fof(f289,plain,
    ( ~ sQ2_eqProxy(k2_lattices(sK0,k7_lattices(sK0,sK1),sK1),k5_lattices(sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f287])).

fof(f312,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f310,f38])).

fof(f310,plain,
    ( v2_struct_0(sK0)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f309,f41])).

fof(f309,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f306,f42])).

fof(f306,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl3_3 ),
    inference(resolution,[],[f285,f57])).

fof(f285,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f283])).

fof(f304,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f301,f41])).

fof(f301,plain,
    ( ~ l3_lattices(sK0)
    | spl3_2 ),
    inference(resolution,[],[f281,f44])).

fof(f44,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f281,plain,
    ( ~ l1_lattices(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl3_2
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f298,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f296,f41])).

fof(f296,plain,
    ( ~ l3_lattices(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f295,f38])).

fof(f295,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f292,f39])).

fof(f292,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl3_1 ),
    inference(resolution,[],[f277,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f277,plain,
    ( ~ v6_lattices(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl3_1
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f290,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f116,f287,f283,f279,f275])).

fof(f116,plain,
    ( ~ sQ2_eqProxy(k2_lattices(sK0,k7_lattices(sK0,sK1),sK1),k5_lattices(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f115,f38])).

fof(f115,plain,
    ( ~ sQ2_eqProxy(k2_lattices(sK0,k7_lattices(sK0,sK1),sK1),k5_lattices(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f114,f42])).

fof(f114,plain,
    ( ~ sQ2_eqProxy(k2_lattices(sK0,k7_lattices(sK0,sK1),sK1),k5_lattices(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f105,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sQ2_eqProxy(k2_lattices(X0,X1,X2),k4_lattices(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f58,f60])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f105,plain,(
    ! [X3] :
      ( ~ sQ2_eqProxy(X3,k4_lattices(sK0,k7_lattices(sK0,sK1),sK1))
      | ~ sQ2_eqProxy(X3,k5_lattices(sK0)) ) ),
    inference(resolution,[],[f100,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( sQ2_eqProxy(X1,X0)
      | ~ sQ2_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f60])).

fof(f100,plain,(
    ! [X0] :
      ( ~ sQ2_eqProxy(k5_lattices(sK0),X0)
      | ~ sQ2_eqProxy(X0,k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)) ) ),
    inference(resolution,[],[f95,f61])).

fof(f61,plain,(
    ~ sQ2_eqProxy(k5_lattices(sK0),k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)) ),
    inference(equality_proxy_replacement,[],[f43,f60])).

fof(f43,plain,(
    k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( sQ2_eqProxy(X0,X2)
      | ~ sQ2_eqProxy(X1,X2)
      | ~ sQ2_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:21:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.45  % (9404)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (9412)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.46  % (9401)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (9409)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (9409)Refutation not found, incomplete strategy% (9409)------------------------------
% 0.21/0.47  % (9409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (9409)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (9409)Memory used [KB]: 1663
% 0.21/0.47  % (9409)Time elapsed: 0.053 s
% 0.21/0.47  % (9409)------------------------------
% 0.21/0.47  % (9409)------------------------------
% 0.21/0.47  % (9410)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (9401)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f375,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f290,f298,f304,f312,f344,f360,f374])).
% 0.21/0.48  fof(f374,plain,(
% 0.21/0.48    spl3_6),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f373])).
% 0.21/0.48  fof(f373,plain,(
% 0.21/0.48    $false | spl3_6),
% 0.21/0.48    inference(subsumption_resolution,[],[f372,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    l3_lattices(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    (k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f33,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,X1),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,X1),X1) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ? [X1] : (k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,X1),X1) & m1_subset_1(X1,u1_struct_0(sK0))) => (k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,X1),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,X1),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattices)).
% 0.21/0.48  fof(f372,plain,(
% 0.21/0.48    ~l3_lattices(sK0) | spl3_6),
% 0.21/0.48    inference(subsumption_resolution,[],[f371,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f371,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~l3_lattices(sK0) | spl3_6),
% 0.21/0.48    inference(subsumption_resolution,[],[f368,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v17_lattices(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f368,plain,(
% 0.21/0.48    ~v17_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl3_6),
% 0.21/0.48    inference(resolution,[],[f343,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0] : (v16_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : ((v16_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (((v16_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | (~v17_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v16_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_lattices)).
% 0.21/0.48  fof(f343,plain,(
% 0.21/0.48    ~v16_lattices(sK0) | spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f341])).
% 0.21/0.48  fof(f341,plain,(
% 0.21/0.48    spl3_6 <=> v16_lattices(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f360,plain,(
% 0.21/0.48    spl3_5),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f359])).
% 0.21/0.48  fof(f359,plain,(
% 0.21/0.48    $false | spl3_5),
% 0.21/0.48    inference(subsumption_resolution,[],[f358,f41])).
% 0.21/0.48  fof(f358,plain,(
% 0.21/0.48    ~l3_lattices(sK0) | spl3_5),
% 0.21/0.48    inference(subsumption_resolution,[],[f357,f38])).
% 0.21/0.48  fof(f357,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~l3_lattices(sK0) | spl3_5),
% 0.21/0.48    inference(subsumption_resolution,[],[f354,f40])).
% 0.21/0.48  fof(f354,plain,(
% 0.21/0.48    ~v17_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl3_5),
% 0.21/0.48    inference(resolution,[],[f339,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0] : (v11_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f339,plain,(
% 0.21/0.48    ~v11_lattices(sK0) | spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f337])).
% 0.21/0.48  fof(f337,plain,(
% 0.21/0.48    spl3_5 <=> v11_lattices(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f344,plain,(
% 0.21/0.48    ~spl3_5 | ~spl3_6 | ~spl3_3 | spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f328,f287,f283,f341,f337])).
% 0.21/0.48  fof(f283,plain,(
% 0.21/0.48    spl3_3 <=> m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f287,plain,(
% 0.21/0.48    spl3_4 <=> sQ2_eqProxy(k2_lattices(sK0,k7_lattices(sK0,sK1),sK1),k5_lattices(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f328,plain,(
% 0.21/0.48    ~v16_lattices(sK0) | ~v11_lattices(sK0) | (~spl3_3 | spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f327,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f327,plain,(
% 0.21/0.48    ~v16_lattices(sK0) | ~v11_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl3_3 | spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f326,f38])).
% 0.21/0.48  fof(f326,plain,(
% 0.21/0.48    ~v16_lattices(sK0) | ~v11_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl3_3 | spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f325,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    v10_lattices(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f325,plain,(
% 0.21/0.48    ~v16_lattices(sK0) | ~v11_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl3_3 | spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f322,f41])).
% 0.21/0.48  fof(f322,plain,(
% 0.21/0.48    ~l3_lattices(sK0) | ~v16_lattices(sK0) | ~v11_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl3_3 | spl3_4)),
% 0.21/0.48    inference(resolution,[],[f321,f170])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_lattices(X0,k7_lattices(X0,X1),X1) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f96,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_lattices(X0,X2,X1) | k7_lattices(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((k7_lattices(X0,X1) = X2 | ~r2_lattices(X0,X2,X1)) & (r2_lattices(X0,X2,X1) | k7_lattices(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((k7_lattices(X0,X1) = X2 <=> r2_lattices(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((! [X2] : ((k7_lattices(X0,X1) = X2 <=> r2_lattices(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v16_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ((l3_lattices(X0) & v16_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k7_lattices(X0,X1) = X2 <=> r2_lattices(X0,X2,X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattices)).
% 0.21/0.48  fof(f321,plain,(
% 0.21/0.48    ~r2_lattices(sK0,k7_lattices(sK0,sK1),sK1) | (~spl3_3 | spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f320,f38])).
% 0.21/0.48  fof(f320,plain,(
% 0.21/0.48    ~r2_lattices(sK0,k7_lattices(sK0,sK1),sK1) | v2_struct_0(sK0) | (~spl3_3 | spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f319,f41])).
% 0.21/0.48  fof(f319,plain,(
% 0.21/0.48    ~r2_lattices(sK0,k7_lattices(sK0,sK1),sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (~spl3_3 | spl3_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f318,f284])).
% 0.21/0.48  fof(f284,plain,(
% 0.21/0.48    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f283])).
% 0.21/0.48  fof(f318,plain,(
% 0.21/0.48    ~r2_lattices(sK0,k7_lattices(sK0,sK1),sK1) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | spl3_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f315,f42])).
% 0.21/0.48  fof(f315,plain,(
% 0.21/0.48    ~r2_lattices(sK0,k7_lattices(sK0,sK1),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | spl3_4),
% 0.21/0.48    inference(resolution,[],[f289,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sQ2_eqProxy(k2_lattices(X0,X1,X2),k5_lattices(X0)) | ~r2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f54,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ! [X1,X0] : (sQ2_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = k5_lattices(X0) | ~r2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_lattices(X0,X1,X2) | k5_lattices(X0) != k2_lattices(X0,X2,X1) | k2_lattices(X0,X1,X2) != k5_lattices(X0) | k6_lattices(X0) != k1_lattices(X0,X2,X1) | k1_lattices(X0,X1,X2) != k6_lattices(X0)) & ((k5_lattices(X0) = k2_lattices(X0,X2,X1) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k6_lattices(X0) = k1_lattices(X0,X2,X1) & k1_lattices(X0,X1,X2) = k6_lattices(X0)) | ~r2_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_lattices(X0,X1,X2) | (k5_lattices(X0) != k2_lattices(X0,X2,X1) | k2_lattices(X0,X1,X2) != k5_lattices(X0) | k6_lattices(X0) != k1_lattices(X0,X2,X1) | k1_lattices(X0,X1,X2) != k6_lattices(X0))) & ((k5_lattices(X0) = k2_lattices(X0,X2,X1) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k6_lattices(X0) = k1_lattices(X0,X2,X1) & k1_lattices(X0,X1,X2) = k6_lattices(X0)) | ~r2_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_lattices(X0,X1,X2) <=> (k5_lattices(X0) = k2_lattices(X0,X2,X1) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k6_lattices(X0) = k1_lattices(X0,X2,X1) & k1_lattices(X0,X1,X2) = k6_lattices(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_lattices(X0,X1,X2) <=> (k5_lattices(X0) = k2_lattices(X0,X2,X1) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k6_lattices(X0) = k1_lattices(X0,X2,X1) & k1_lattices(X0,X1,X2) = k6_lattices(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattices(X0,X1,X2) <=> (k5_lattices(X0) = k2_lattices(X0,X2,X1) & k2_lattices(X0,X1,X2) = k5_lattices(X0) & k6_lattices(X0) = k1_lattices(X0,X2,X1) & k1_lattices(X0,X1,X2) = k6_lattices(X0))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_lattices)).
% 0.21/0.48  fof(f289,plain,(
% 0.21/0.48    ~sQ2_eqProxy(k2_lattices(sK0,k7_lattices(sK0,sK1),sK1),k5_lattices(sK0)) | spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f287])).
% 0.21/0.48  fof(f312,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f311])).
% 0.21/0.48  fof(f311,plain,(
% 0.21/0.48    $false | spl3_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f310,f38])).
% 0.21/0.48  fof(f310,plain,(
% 0.21/0.48    v2_struct_0(sK0) | spl3_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f309,f41])).
% 0.21/0.48  fof(f309,plain,(
% 0.21/0.48    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl3_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f306,f42])).
% 0.21/0.48  fof(f306,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | spl3_3),
% 0.21/0.48    inference(resolution,[],[f285,f57])).
% 0.21/0.48  fof(f285,plain,(
% 0.21/0.48    ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f283])).
% 0.21/0.48  fof(f304,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f303])).
% 0.21/0.48  fof(f303,plain,(
% 0.21/0.48    $false | spl3_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f301,f41])).
% 0.21/0.48  fof(f301,plain,(
% 0.21/0.48    ~l3_lattices(sK0) | spl3_2),
% 0.21/0.48    inference(resolution,[],[f281,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.48  fof(f281,plain,(
% 0.21/0.48    ~l1_lattices(sK0) | spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f279])).
% 0.21/0.48  fof(f279,plain,(
% 0.21/0.48    spl3_2 <=> l1_lattices(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f298,plain,(
% 0.21/0.48    spl3_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f297])).
% 0.21/0.48  fof(f297,plain,(
% 0.21/0.48    $false | spl3_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f296,f41])).
% 0.21/0.48  fof(f296,plain,(
% 0.21/0.48    ~l3_lattices(sK0) | spl3_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f295,f38])).
% 0.21/0.48  fof(f295,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~l3_lattices(sK0) | spl3_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f292,f39])).
% 0.21/0.48  fof(f292,plain,(
% 0.21/0.48    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl3_1),
% 0.21/0.48    inference(resolution,[],[f277,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : ((v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (((v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.48  fof(f277,plain,(
% 0.21/0.48    ~v6_lattices(sK0) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f275])).
% 0.21/0.48  fof(f275,plain,(
% 0.21/0.48    spl3_1 <=> v6_lattices(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f290,plain,(
% 0.21/0.48    ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f116,f287,f283,f279,f275])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ~sQ2_eqProxy(k2_lattices(sK0,k7_lattices(sK0,sK1),sK1),k5_lattices(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f115,f38])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ~sQ2_eqProxy(k2_lattices(sK0,k7_lattices(sK0,sK1),sK1),k5_lattices(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f114,f42])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ~sQ2_eqProxy(k2_lattices(sK0,k7_lattices(sK0,sK1),sK1),k5_lattices(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f105,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sQ2_eqProxy(k2_lattices(X0,X1,X2),k4_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f58,f60])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X3] : (~sQ2_eqProxy(X3,k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)) | ~sQ2_eqProxy(X3,k5_lattices(sK0))) )),
% 0.21/0.48    inference(resolution,[],[f100,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ2_eqProxy(X1,X0) | ~sQ2_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f60])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X0] : (~sQ2_eqProxy(k5_lattices(sK0),X0) | ~sQ2_eqProxy(X0,k4_lattices(sK0,k7_lattices(sK0,sK1),sK1))) )),
% 0.21/0.48    inference(resolution,[],[f95,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ~sQ2_eqProxy(k5_lattices(sK0),k4_lattices(sK0,k7_lattices(sK0,sK1),sK1))),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f43,f60])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sQ2_eqProxy(X0,X2) | ~sQ2_eqProxy(X1,X2) | ~sQ2_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f60])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (9401)------------------------------
% 0.21/0.48  % (9401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9401)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (9401)Memory used [KB]: 6396
% 0.21/0.48  % (9401)Time elapsed: 0.066 s
% 0.21/0.48  % (9401)------------------------------
% 0.21/0.48  % (9401)------------------------------
% 0.21/0.48  % (9395)Success in time 0.118 s
%------------------------------------------------------------------------------
