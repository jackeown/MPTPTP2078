%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattices__t54_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:03 EDT 2019

% Result     : Theorem 2.43s
% Output     : Refutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  217 ( 507 expanded)
%              Number of leaves         :   43 ( 155 expanded)
%              Depth                    :   14
%              Number of atoms          :  965 (2602 expanded)
%              Number of equality atoms :   41 ( 183 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2644,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f178,f479,f481,f729,f1065,f1077,f1493,f1495,f1497,f1499,f1507,f1615,f1628,f1965,f2046,f2118,f2121,f2129,f2281,f2482,f2520,f2526,f2618,f2639])).

fof(f2639,plain,
    ( spl14_2
    | ~ spl14_231
    | ~ spl14_99
    | spl14_333 ),
    inference(avatar_split_clause,[],[f2637,f2616,f1063,f1934,f2613])).

fof(f2613,plain,
    ( spl14_2
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f1934,plain,
    ( spl14_231
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_231])])).

fof(f1063,plain,
    ( spl14_99
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_99])])).

fof(f2616,plain,
    ( spl14_333
  <=> ~ m1_subset_1(sK9(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_333])])).

fof(f2637,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = sK1
    | ~ spl14_333 ),
    inference(resolution,[],[f2617,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',t8_subset_1)).

fof(f2617,plain,
    ( ~ m1_subset_1(sK9(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl14_333 ),
    inference(avatar_component_clause,[],[f2616])).

fof(f2618,plain,
    ( ~ spl14_231
    | spl14_2
    | ~ spl14_333
    | ~ spl14_96
    | ~ spl14_312 ),
    inference(avatar_split_clause,[],[f2593,f2518,f1060,f2616,f2613,f1934])).

fof(f1060,plain,
    ( spl14_96
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = X0
        | ~ r2_hidden(sK9(u1_struct_0(sK0),X0,u1_struct_0(sK0)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_96])])).

fof(f2518,plain,
    ( spl14_312
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_312])])).

fof(f2593,plain,
    ( ~ m1_subset_1(sK9(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl14_96
    | ~ spl14_312 ),
    inference(resolution,[],[f2519,f1061])).

fof(f1061,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK9(u1_struct_0(sK0),X0,u1_struct_0(sK0)),X0)
        | u1_struct_0(sK0) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl14_96 ),
    inference(avatar_component_clause,[],[f1060])).

fof(f2519,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl14_312 ),
    inference(avatar_component_clause,[],[f2518])).

fof(f2526,plain,(
    spl14_311 ),
    inference(avatar_contradiction_clause,[],[f2521])).

fof(f2521,plain,
    ( $false
    | ~ spl14_311 ),
    inference(resolution,[],[f2516,f96])).

fof(f96,plain,(
    v19_lattices(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_struct_0(X0) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v19_lattices(X1,X0)
          & v18_lattices(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_struct_0(X0) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v19_lattices(X1,X0)
          & v18_lattices(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v19_lattices(X1,X0)
              & v18_lattices(X1,X0)
              & ~ v1_xboole_0(X1) )
           => k2_struct_0(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v19_lattices(X1,X0)
            & v18_lattices(X1,X0)
            & ~ v1_xboole_0(X1) )
         => k2_struct_0(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',t54_lattices)).

fof(f2516,plain,
    ( ~ v19_lattices(sK1,sK0)
    | ~ spl14_311 ),
    inference(avatar_component_clause,[],[f2515])).

fof(f2515,plain,
    ( spl14_311
  <=> ~ v19_lattices(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_311])])).

fof(f2520,plain,
    ( ~ spl14_311
    | ~ spl14_253
    | ~ spl14_231
    | spl14_312
    | ~ spl14_192
    | ~ spl14_304 ),
    inference(avatar_split_clause,[],[f2513,f2479,f1505,f2518,f1934,f2037,f2515])).

fof(f2037,plain,
    ( spl14_253
  <=> ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_253])])).

fof(f1505,plain,
    ( spl14_192
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k4_lattices(sK0,X0,X1),X2)
        | ~ v19_lattices(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_192])])).

fof(f2479,plain,
    ( spl14_304
  <=> ! [X0] :
        ( r2_hidden(k4_lattices(sK0,X0,sK7(sK1)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_304])])).

fof(f2513,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0))
        | ~ v19_lattices(sK1,sK0) )
    | ~ spl14_192
    | ~ spl14_304 ),
    inference(duplicate_literal_removal,[],[f2503])).

fof(f2503,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0))
        | ~ v19_lattices(sK1,sK0) )
    | ~ spl14_192
    | ~ spl14_304 ),
    inference(resolution,[],[f2480,f1762])).

fof(f1762,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(k4_lattices(sK0,X4,X3),X5)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r2_hidden(X4,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ v19_lattices(X5,sK0) )
    | ~ spl14_192 ),
    inference(duplicate_literal_removal,[],[f1759])).

fof(f1759,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X4,X5)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k4_lattices(sK0,X4,X3),X5)
        | ~ v19_lattices(X5,sK0) )
    | ~ spl14_192 ),
    inference(resolution,[],[f1757,f1506])).

fof(f1506,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(k4_lattices(sK0,X0,X1),X2)
        | ~ v19_lattices(X2,sK0) )
    | ~ spl14_192 ),
    inference(avatar_component_clause,[],[f1505])).

fof(f1757,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f99,f101,f1756])).

fof(f1756,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f820,f100])).

fof(f100,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f820,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(global_subsumption,[],[f109,f819])).

fof(f819,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f818])).

fof(f818,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f152,f113])).

fof(f113,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',cc1_lattices)).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',dt_k4_lattices)).

fof(f109,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',dt_l3_lattices)).

fof(f101,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f99,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f2480,plain,
    ( ! [X0] :
        ( r2_hidden(k4_lattices(sK0,X0,sK7(sK1)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl14_304 ),
    inference(avatar_component_clause,[],[f2479])).

fof(f2482,plain,
    ( ~ spl14_253
    | spl14_304
    | ~ spl14_254 ),
    inference(avatar_split_clause,[],[f2475,f2040,f2479,f2037])).

fof(f2040,plain,
    ( spl14_254
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(k4_lattices(sK0,sK7(sK1),X1),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_254])])).

fof(f2475,plain,
    ( ! [X1] :
        ( r2_hidden(k4_lattices(sK0,X1,sK7(sK1)),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0)) )
    | ~ spl14_254 ),
    inference(duplicate_literal_removal,[],[f2474])).

fof(f2474,plain,
    ( ! [X1] :
        ( r2_hidden(k4_lattices(sK0,X1,sK7(sK1)),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0)) )
    | ~ spl14_254 ),
    inference(superposition,[],[f2041,f1967])).

fof(f1967,plain,(
    ! [X0,X1] :
      ( k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f99,f101,f1966])).

fof(f1966,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f1189,f100])).

fof(f1189,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(global_subsumption,[],[f109,f1188])).

fof(f1188,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f1187])).

fof(f1187,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f154,f113])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',commutativity_k4_lattices)).

fof(f2041,plain,
    ( ! [X1] :
        ( r2_hidden(k4_lattices(sK0,sK7(sK1),X1),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl14_254 ),
    inference(avatar_component_clause,[],[f2040])).

fof(f2281,plain,(
    spl14_253 ),
    inference(avatar_contradiction_clause,[],[f2278])).

fof(f2278,plain,
    ( $false
    | ~ spl14_253 ),
    inference(resolution,[],[f2038,f286])).

fof(f286,plain,(
    m1_subset_1(sK7(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f281,f97])).

fof(f97,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f281,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | m1_subset_1(sK7(sK1),X0) ) ),
    inference(resolution,[],[f156,f185])).

fof(f185,plain,(
    r2_hidden(sK7(sK1),sK1) ),
    inference(resolution,[],[f182,f136])).

fof(f136,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',existence_m1_subset_1)).

fof(f182,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f139,f94])).

fof(f94,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f139,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',t2_subset)).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',t4_subset)).

fof(f2038,plain,
    ( ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0))
    | ~ spl14_253 ),
    inference(avatar_component_clause,[],[f2037])).

fof(f2129,plain,
    ( ~ spl14_1
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f2128,f170,f167])).

fof(f167,plain,
    ( spl14_1
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f170,plain,
    ( spl14_3
  <=> u1_struct_0(sK0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f2128,plain,
    ( u1_struct_0(sK0) != sK1
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f98,f117])).

fof(f117,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',d3_struct_0)).

fof(f98,plain,(
    k2_struct_0(sK0) != sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f2121,plain,
    ( ~ spl14_231
    | spl14_232
    | ~ spl14_210 ),
    inference(avatar_split_clause,[],[f2120,f1626,f1937,f1934])).

fof(f1937,plain,
    ( spl14_232
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(k4_lattices(sK0,X0,X1),sK1)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_232])])).

fof(f1626,plain,
    ( spl14_210
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k4_lattices(sK0,X0,X1),X2)
        | ~ v18_lattices(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_210])])).

fof(f2120,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k4_lattices(sK0,X0,X1),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl14_210 ),
    inference(resolution,[],[f95,f1763])).

fof(f1763,plain,
    ( ! [X2,X0,X1] :
        ( ~ v18_lattices(X2,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k4_lattices(sK0,X1,X0),X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl14_210 ),
    inference(duplicate_literal_removal,[],[f1758])).

fof(f1758,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k4_lattices(sK0,X1,X0),X2)
        | ~ v18_lattices(X2,sK0) )
    | ~ spl14_210 ),
    inference(resolution,[],[f1757,f1627])).

fof(f1627,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k4_lattices(sK0,X0,X1),X2)
        | ~ v18_lattices(X2,sK0) )
    | ~ spl14_210 ),
    inference(avatar_component_clause,[],[f1626])).

fof(f95,plain,(
    v18_lattices(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f2118,plain,(
    ~ spl14_256 ),
    inference(avatar_contradiction_clause,[],[f2116])).

fof(f2116,plain,
    ( $false
    | ~ spl14_256 ),
    inference(resolution,[],[f2051,f102])).

fof(f102,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',fc1_xboole_0)).

fof(f2051,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl14_256 ),
    inference(backward_demodulation,[],[f2045,f94])).

fof(f2045,plain,
    ( k1_xboole_0 = sK1
    | ~ spl14_256 ),
    inference(avatar_component_clause,[],[f2044])).

fof(f2044,plain,
    ( spl14_256
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_256])])).

fof(f2046,plain,
    ( spl14_256
    | ~ spl14_253
    | spl14_254
    | ~ spl14_232 ),
    inference(avatar_split_clause,[],[f2025,f1937,f2040,f2037,f2044])).

fof(f2025,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | r2_hidden(k4_lattices(sK0,sK7(sK1),X5),sK1)
        | ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0))
        | k1_xboole_0 = sK1 )
    | ~ spl14_232 ),
    inference(resolution,[],[f1938,f207])).

fof(f207,plain,(
    ! [X4] :
      ( r2_hidden(sK7(X4),X4)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f184,f136])).

fof(f184,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,X5)
      | r2_hidden(X4,X5)
      | k1_xboole_0 = X5 ) ),
    inference(resolution,[],[f139,f108])).

fof(f108,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',t6_boole)).

fof(f1938,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(k4_lattices(sK0,X0,X1),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl14_232 ),
    inference(avatar_component_clause,[],[f1937])).

fof(f1965,plain,(
    spl14_231 ),
    inference(avatar_contradiction_clause,[],[f1963])).

fof(f1963,plain,
    ( $false
    | ~ spl14_231 ),
    inference(resolution,[],[f1935,f97])).

fof(f1935,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl14_231 ),
    inference(avatar_component_clause,[],[f1934])).

fof(f1628,plain,
    ( spl14_38
    | ~ spl14_41
    | ~ spl14_187
    | ~ spl14_189
    | spl14_210
    | ~ spl14_208 ),
    inference(avatar_split_clause,[],[f1624,f1613,f1626,f1488,f1485,f456,f453])).

fof(f453,plain,
    ( spl14_38
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_38])])).

fof(f456,plain,
    ( spl14_41
  <=> ~ l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_41])])).

fof(f1485,plain,
    ( spl14_187
  <=> ~ v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_187])])).

fof(f1488,plain,
    ( spl14_189
  <=> ~ v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_189])])).

fof(f1613,plain,
    ( spl14_208
  <=> ! [X9,X7,X8] :
        ( ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X7,X8)
        | ~ v18_lattices(X9,sK0)
        | r2_hidden(X7,X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r2_hidden(X8,X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_208])])).

fof(f1624,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
        | ~ v18_lattices(X2,sK0)
        | r2_hidden(k4_lattices(sK0,X0,X1),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X2)
        | ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl14_208 ),
    inference(duplicate_literal_removal,[],[f1621])).

fof(f1621,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
        | ~ v18_lattices(X2,sK0)
        | r2_hidden(k4_lattices(sK0,X0,X1),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X2)
        | ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl14_208 ),
    inference(resolution,[],[f1614,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',t23_lattices)).

fof(f1614,plain,
    ( ! [X8,X7,X9] :
        ( ~ r1_lattices(sK0,X7,X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ v18_lattices(X9,sK0)
        | r2_hidden(X7,X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r2_hidden(X8,X9) )
    | ~ spl14_208 ),
    inference(avatar_component_clause,[],[f1613])).

fof(f1615,plain,
    ( ~ spl14_185
    | ~ spl14_187
    | ~ spl14_189
    | spl14_208 ),
    inference(avatar_split_clause,[],[f1611,f1613,f1488,f1485,f1482])).

fof(f1482,plain,
    ( spl14_185
  <=> ~ v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_185])])).

fof(f1611,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X8,X9)
      | r2_hidden(X7,X9)
      | ~ v18_lattices(X9,sK0)
      | ~ v6_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ r1_lattices(sK0,X7,X8) ) ),
    inference(global_subsumption,[],[f99,f101,f1607])).

fof(f1607,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X8,X9)
      | r2_hidden(X7,X9)
      | ~ v18_lattices(X9,sK0)
      | ~ v6_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ r1_lattices(sK0,X7,X8)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1606])).

fof(f1606,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X8,X9)
      | r2_hidden(X7,X9)
      | ~ v18_lattices(X9,sK0)
      | ~ v6_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ r1_lattices(sK0,X7,X8)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f1537,f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',redefinition_r3_lattices)).

fof(f1537,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(sK0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X1,X0)
      | ~ v18_lattices(X0,sK0) ) ),
    inference(global_subsumption,[],[f99,f101,f1536])).

fof(f1536,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X1,X2)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X1,X0)
      | ~ v18_lattices(X0,sK0) ) ),
    inference(resolution,[],[f129,f100])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattices(X0,X2,X3)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X2,X1)
      | ~ v18_lattices(X1,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v18_lattices(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X2,X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r3_lattices(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v18_lattices(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X2,X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r3_lattices(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v18_lattices(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r3_lattices(X0,X2,X3) )
                     => r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',d22_lattices)).

fof(f1507,plain,
    ( spl14_38
    | ~ spl14_41
    | ~ spl14_187
    | ~ spl14_189
    | spl14_192
    | ~ spl14_190 ),
    inference(avatar_split_clause,[],[f1503,f1491,f1505,f1488,f1485,f456,f453])).

fof(f1491,plain,
    ( spl14_190
  <=> ! [X9,X7,X8] :
        ( ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X7,X8)
        | ~ v19_lattices(X9,sK0)
        | ~ r2_hidden(X7,X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r2_hidden(X8,X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_190])])).

fof(f1503,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
        | ~ v19_lattices(X2,sK0)
        | ~ r2_hidden(k4_lattices(sK0,X0,X1),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,X2)
        | ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl14_190 ),
    inference(duplicate_literal_removal,[],[f1500])).

fof(f1500,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
        | ~ v19_lattices(X2,sK0)
        | ~ r2_hidden(k4_lattices(sK0,X0,X1),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,X2)
        | ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl14_190 ),
    inference(resolution,[],[f1492,f135])).

fof(f1492,plain,
    ( ! [X8,X7,X9] :
        ( ~ r1_lattices(sK0,X7,X8)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ v19_lattices(X9,sK0)
        | ~ r2_hidden(X7,X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r2_hidden(X8,X9) )
    | ~ spl14_190 ),
    inference(avatar_component_clause,[],[f1491])).

fof(f1499,plain,
    ( ~ spl14_41
    | ~ spl14_43
    | spl14_38
    | spl14_189 ),
    inference(avatar_split_clause,[],[f1498,f1488,f453,f459,f456])).

fof(f459,plain,
    ( spl14_43
  <=> ~ v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_43])])).

fof(f1498,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl14_189 ),
    inference(resolution,[],[f1489,f113])).

fof(f1489,plain,
    ( ~ v6_lattices(sK0)
    | ~ spl14_189 ),
    inference(avatar_component_clause,[],[f1488])).

fof(f1497,plain,
    ( ~ spl14_41
    | ~ spl14_43
    | spl14_38
    | spl14_187 ),
    inference(avatar_split_clause,[],[f1496,f1485,f453,f459,f456])).

fof(f1496,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl14_187 ),
    inference(resolution,[],[f1486,f115])).

fof(f115,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1486,plain,
    ( ~ v8_lattices(sK0)
    | ~ spl14_187 ),
    inference(avatar_component_clause,[],[f1485])).

fof(f1495,plain,
    ( ~ spl14_41
    | ~ spl14_43
    | spl14_38
    | spl14_185 ),
    inference(avatar_split_clause,[],[f1494,f1482,f453,f459,f456])).

fof(f1494,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl14_185 ),
    inference(resolution,[],[f1483,f116])).

fof(f116,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1483,plain,
    ( ~ v9_lattices(sK0)
    | ~ spl14_185 ),
    inference(avatar_component_clause,[],[f1482])).

fof(f1493,plain,
    ( ~ spl14_185
    | ~ spl14_187
    | ~ spl14_189
    | spl14_190 ),
    inference(avatar_split_clause,[],[f1480,f1491,f1488,f1485,f1482])).

fof(f1480,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X7,X9)
      | r2_hidden(X8,X9)
      | ~ v19_lattices(X9,sK0)
      | ~ v6_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ r1_lattices(sK0,X7,X8) ) ),
    inference(global_subsumption,[],[f99,f101,f1476])).

fof(f1476,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X7,X9)
      | r2_hidden(X8,X9)
      | ~ v19_lattices(X9,sK0)
      | ~ v6_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ r1_lattices(sK0,X7,X8)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1475])).

fof(f1475,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X7,X9)
      | r2_hidden(X8,X9)
      | ~ v19_lattices(X9,sK0)
      | ~ v6_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ r1_lattices(sK0,X7,X8)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f1471,f150])).

fof(f1471,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(sK0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,X0)
      | r2_hidden(X2,X0)
      | ~ v19_lattices(X0,sK0) ) ),
    inference(global_subsumption,[],[f99,f101,f1470])).

fof(f1470,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X1,X2)
      | ~ r2_hidden(X1,X0)
      | r2_hidden(X2,X0)
      | ~ v19_lattices(X0,sK0) ) ),
    inference(resolution,[],[f123,f100])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattices(X0,X2,X3)
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X3,X1)
      | ~ v19_lattices(X1,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v19_lattices(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ r3_lattices(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v19_lattices(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ r3_lattices(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v19_lattices(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X2,X1)
                        & r3_lattices(X0,X2,X3) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',d23_lattices)).

fof(f1077,plain,(
    spl14_99 ),
    inference(avatar_contradiction_clause,[],[f1076])).

fof(f1076,plain,
    ( $false
    | ~ spl14_99 ),
    inference(resolution,[],[f1074,f101])).

fof(f1074,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl14_99 ),
    inference(resolution,[],[f1072,f109])).

fof(f1072,plain,
    ( ~ l1_lattices(sK0)
    | ~ spl14_99 ),
    inference(resolution,[],[f1070,f104])).

fof(f104,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_lattices(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_lattices(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',dt_l1_lattices)).

fof(f1070,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl14_99 ),
    inference(resolution,[],[f1064,f181])).

fof(f181,plain,(
    ! [X0] :
      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,(
    ! [X0] :
      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f118,f117])).

fof(f118,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',dt_k2_struct_0)).

fof(f1064,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl14_99 ),
    inference(avatar_component_clause,[],[f1063])).

fof(f1065,plain,
    ( spl14_96
    | ~ spl14_99 ),
    inference(avatar_split_clause,[],[f1058,f1063,f1060])).

fof(f1058,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK9(u1_struct_0(sK0),X0,u1_struct_0(sK0)),X0)
      | u1_struct_0(sK0) = X0 ) ),
    inference(duplicate_literal_removal,[],[f1048])).

fof(f1048,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK9(u1_struct_0(sK0),X0,u1_struct_0(sK0)),X0)
      | u1_struct_0(sK0) = X0
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = X0 ) ),
    inference(resolution,[],[f143,f548])).

fof(f548,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK9(u1_struct_0(sK0),X2,X3),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | X2 = X3 ) ),
    inference(resolution,[],[f193,f144])).

fof(f193,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f191,f139])).

fof(f191,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f190,f97])).

fof(f190,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f157,f185])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/lattices__t54_lattices.p',t5_subset)).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK9(X0,X1,X2),X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f72])).

fof(f729,plain,(
    ~ spl14_38 ),
    inference(avatar_contradiction_clause,[],[f728])).

fof(f728,plain,
    ( $false
    | ~ spl14_38 ),
    inference(resolution,[],[f454,f99])).

fof(f454,plain,
    ( v2_struct_0(sK0)
    | ~ spl14_38 ),
    inference(avatar_component_clause,[],[f453])).

fof(f481,plain,(
    spl14_43 ),
    inference(avatar_contradiction_clause,[],[f480])).

fof(f480,plain,
    ( $false
    | ~ spl14_43 ),
    inference(resolution,[],[f460,f100])).

fof(f460,plain,
    ( ~ v10_lattices(sK0)
    | ~ spl14_43 ),
    inference(avatar_component_clause,[],[f459])).

fof(f479,plain,(
    spl14_41 ),
    inference(avatar_contradiction_clause,[],[f478])).

fof(f478,plain,
    ( $false
    | ~ spl14_41 ),
    inference(resolution,[],[f457,f101])).

fof(f457,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl14_41 ),
    inference(avatar_component_clause,[],[f456])).

fof(f178,plain,(
    spl14_1 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl14_1 ),
    inference(resolution,[],[f175,f101])).

fof(f175,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl14_1 ),
    inference(resolution,[],[f173,f109])).

fof(f173,plain,
    ( ~ l1_lattices(sK0)
    | ~ spl14_1 ),
    inference(resolution,[],[f168,f104])).

fof(f168,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f167])).
%------------------------------------------------------------------------------
