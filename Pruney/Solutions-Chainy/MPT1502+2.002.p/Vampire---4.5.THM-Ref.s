%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:39 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 462 expanded)
%              Number of leaves         :   40 ( 187 expanded)
%              Depth                    :   17
%              Number of atoms          : 1308 (2822 expanded)
%              Number of equality atoms :   28 (  74 expanded)
%              Maximal formula depth    :   19 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f909,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f92,f96,f100,f104,f108,f118,f126,f138,f140,f142,f147,f149,f163,f175,f184,f190,f199,f253,f655,f782,f807,f881,f890,f908])).

fof(f908,plain,
    ( spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | ~ spl6_3
    | spl6_58 ),
    inference(avatar_split_clause,[],[f899,f888,f94,f98,f102,f106])).

fof(f106,plain,
    ( spl6_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f102,plain,
    ( spl6_5
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f98,plain,
    ( spl6_4
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f94,plain,
    ( spl6_3
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f888,plain,
    ( spl6_58
  <=> r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f899,plain,
    ( ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl6_58 ),
    inference(resolution,[],[f889,f109])).

fof(f109,plain,(
    ! [X2,X0] :
      ( r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f83,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f83,plain,(
    ! [X2,X0] :
      ( r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
                  & r3_lattice3(X0,sK3(X0,X1,X2),X2)
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
        & r3_lattice3(X0,sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

fof(f889,plain,
    ( ~ r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK2)
    | spl6_58 ),
    inference(avatar_component_clause,[],[f888])).

fof(f890,plain,
    ( ~ spl6_2
    | ~ spl6_58
    | ~ spl6_12
    | ~ spl6_8
    | ~ spl6_47
    | spl6_9
    | ~ spl6_57 ),
    inference(avatar_split_clause,[],[f882,f879,f124,f642,f121,f136,f888,f90])).

fof(f90,plain,
    ( spl6_2
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f136,plain,
    ( spl6_12
  <=> m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f121,plain,
    ( spl6_8
  <=> m1_subset_1(k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f642,plain,
    ( spl6_47
  <=> m1_subset_1(sK4(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),a_3_4_lattice3(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f124,plain,
    ( spl6_9
  <=> r3_lattice3(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f879,plain,
    ( spl6_57
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,k3_lattices(sK0,X1,X0),a_3_4_lattice3(sK0,X1,X2)),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_lattices(sK0,X1,X0),u1_struct_0(sK0))
        | r3_lattice3(sK0,k3_lattices(sK0,X1,X0),a_3_4_lattice3(sK0,X1,X2))
        | ~ r3_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f882,plain,
    ( ~ m1_subset_1(sK4(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),a_3_4_lattice3(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl6_9
    | ~ spl6_57 ),
    inference(resolution,[],[f880,f125])).

fof(f125,plain,
    ( ~ r3_lattice3(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f880,plain,
    ( ! [X2,X0,X1] :
        ( r3_lattice3(sK0,k3_lattices(sK0,X1,X0),a_3_4_lattice3(sK0,X1,X2))
        | ~ m1_subset_1(sK4(sK0,k3_lattices(sK0,X1,X0),a_3_4_lattice3(sK0,X1,X2)),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_lattices(sK0,X1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f879])).

fof(f881,plain,
    ( spl6_6
    | ~ spl6_3
    | spl6_57
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f877,f805,f188,f173,f879,f94,f106])).

fof(f173,plain,
    ( spl6_16
  <=> ! [X1,X3,X0,X2] :
        ( ~ r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2))
        | ~ r3_lattice3(sK0,X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_lattices(sK0,X3,sK5(X0,sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f188,plain,
    ( spl6_18
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_lattice3(sK0,X0,X1)
        | ~ r3_lattices(sK0,X0,sK4(sK0,X0,X1))
        | ~ m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f805,plain,
    ( spl6_52
  <=> ! [X5,X7,X8,X6] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X5,sK5(X7,sK0,X6,X8))
        | ~ r2_hidden(X7,a_3_4_lattice3(sK0,X6,X8))
        | r3_lattices(sK0,k3_lattices(sK0,X6,X5),X7)
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f877,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,X2)
        | r3_lattice3(sK0,k3_lattices(sK0,X1,X0),a_3_4_lattice3(sK0,X1,X2))
        | ~ m1_subset_1(k3_lattices(sK0,X1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,k3_lattices(sK0,X1,X0),a_3_4_lattice3(sK0,X1,X2)),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_52 ),
    inference(duplicate_literal_removal,[],[f874])).

fof(f874,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,X2)
        | r3_lattice3(sK0,k3_lattices(sK0,X1,X0),a_3_4_lattice3(sK0,X1,X2))
        | ~ m1_subset_1(k3_lattices(sK0,X1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,k3_lattices(sK0,X1,X0),a_3_4_lattice3(sK0,X1,X2)),u1_struct_0(sK0))
        | r3_lattice3(sK0,k3_lattices(sK0,X1,X0),a_3_4_lattice3(sK0,X1,X2))
        | ~ m1_subset_1(k3_lattices(sK0,X1,X0),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_52 ),
    inference(resolution,[],[f813,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK4(X0,X1,X2))
                  & r2_hidden(sK4(X0,X1,X2),X2)
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X2)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X1,X3)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

fof(f813,plain,
    ( ! [X4,X2,X3,X1] :
        ( ~ r2_hidden(sK4(sK0,k3_lattices(sK0,X1,X2),X3),a_3_4_lattice3(sK0,X1,X4))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X2,X4)
        | r3_lattice3(sK0,k3_lattices(sK0,X1,X2),X3)
        | ~ m1_subset_1(k3_lattices(sK0,X1,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,k3_lattices(sK0,X1,X2),X3),u1_struct_0(sK0)) )
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_52 ),
    inference(resolution,[],[f811,f189])).

fof(f189,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK0,X0,sK4(sK0,X0,X1))
        | r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0)) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f188])).

fof(f811,plain,
    ( ! [X2,X0,X3,X1] :
        ( r3_lattices(sK0,k3_lattices(sK0,X2,X0),X1)
        | ~ r2_hidden(X1,a_3_4_lattice3(sK0,X2,X3))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,X3) )
    | ~ spl6_16
    | ~ spl6_52 ),
    inference(duplicate_literal_removal,[],[f808])).

fof(f808,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_3_4_lattice3(sK0,X2,X3))
        | r3_lattices(sK0,k3_lattices(sK0,X2,X0),X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,X3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_3_4_lattice3(sK0,X2,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl6_16
    | ~ spl6_52 ),
    inference(resolution,[],[f806,f174])).

fof(f174,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_lattices(sK0,X3,sK5(X0,sK0,X1,X2))
        | ~ r3_lattice3(sK0,X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f173])).

fof(f806,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ r1_lattices(sK0,X5,sK5(X7,sK0,X6,X8))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X7,a_3_4_lattice3(sK0,X6,X8))
        | r3_lattices(sK0,k3_lattices(sK0,X6,X5),X7)
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f805])).

fof(f807,plain,
    ( spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | ~ spl6_3
    | spl6_52
    | ~ spl6_19
    | ~ spl6_28
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f802,f780,f251,f197,f805,f94,f98,f102,f106])).

fof(f197,plain,
    ( spl6_19
  <=> ! [X1,X0] :
        ( r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f251,plain,
    ( spl6_28
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2))
        | k3_lattices(sK0,X1,sK5(X0,sK0,X1,X2)) = X0
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f780,plain,
    ( spl6_50
  <=> ! [X1,X0,X2] :
        ( r3_lattices(sK0,k3_lattices(sK0,X0,X1),k3_lattices(sK0,X0,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f802,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r3_lattices(sK0,k3_lattices(sK0,X6,X5),X7)
        | ~ r2_hidden(X7,a_3_4_lattice3(sK0,X6,X8))
        | ~ r1_lattices(sK0,X5,sK5(X7,sK0,X6,X8))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_19
    | ~ spl6_28
    | ~ spl6_50 ),
    inference(duplicate_literal_removal,[],[f801])).

fof(f801,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r3_lattices(sK0,k3_lattices(sK0,X6,X5),X7)
        | ~ r2_hidden(X7,a_3_4_lattice3(sK0,X6,X8))
        | ~ r1_lattices(sK0,X5,sK5(X7,sK0,X6,X8))
        | ~ r2_hidden(X7,a_3_4_lattice3(sK0,X6,X8))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_19
    | ~ spl6_28
    | ~ spl6_50 ),
    inference(resolution,[],[f788,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
          | ! [X4] :
              ( ~ r2_hidden(X4,X3)
              | k3_lattices(X1,X2,X4) != X0
              | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK5(X0,X1,X2,X3),X3)
            & k3_lattices(X1,X2,sK5(X0,X1,X2,X3)) = X0
            & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f48,f49])).

fof(f49,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X3)
          & k3_lattices(X1,X2,X5) = X0
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( r2_hidden(sK5(X0,X1,X2,X3),X3)
        & k3_lattices(X1,X2,sK5(X0,X1,X2,X3)) = X0
        & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
          | ! [X4] :
              ( ~ r2_hidden(X4,X3)
              | k3_lattices(X1,X2,X4) != X0
              | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( r2_hidden(X5,X3)
              & k3_lattices(X1,X2,X5) = X0
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
          | ! [X4] :
              ( ~ r2_hidden(X4,X3)
              | k3_lattices(X1,X2,X4) != X0
              | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X3)
              & k3_lattices(X1,X2,X4) = X0
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      <=> ? [X4] :
            ( r2_hidden(X4,X3)
            & k3_lattices(X1,X2,X4) = X0
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      <=> ? [X4] :
            ( r2_hidden(X4,X3)
            & k3_lattices(X1,X2,X4) = X0
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      <=> ? [X4] :
            ( r2_hidden(X4,X3)
            & k3_lattices(X1,X2,X4) = X0
            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_3_4_lattice3)).

fof(f788,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK5(X1,sK0,X2,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r3_lattices(sK0,k3_lattices(sK0,X2,X0),X1)
        | ~ r2_hidden(X1,a_3_4_lattice3(sK0,X2,X3))
        | ~ r1_lattices(sK0,X0,sK5(X1,sK0,X2,X3)) )
    | ~ spl6_19
    | ~ spl6_28
    | ~ spl6_50 ),
    inference(duplicate_literal_removal,[],[f787])).

fof(f787,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(X1,sK0,X2,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r3_lattices(sK0,k3_lattices(sK0,X2,X0),X1)
        | ~ r2_hidden(X1,a_3_4_lattice3(sK0,X2,X3))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(X1,sK0,X2,X3),u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,sK5(X1,sK0,X2,X3)) )
    | ~ spl6_19
    | ~ spl6_28
    | ~ spl6_50 ),
    inference(resolution,[],[f785,f198])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,X1) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f197])).

fof(f785,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r3_lattices(sK0,X3,sK5(X1,sK0,X0,X2))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(X1,sK0,X0,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_lattices(sK0,k3_lattices(sK0,X0,X3),X1)
        | ~ r2_hidden(X1,a_3_4_lattice3(sK0,X0,X2)) )
    | ~ spl6_28
    | ~ spl6_50 ),
    inference(duplicate_literal_removal,[],[f784])).

fof(f784,plain,
    ( ! [X2,X0,X3,X1] :
        ( r3_lattices(sK0,k3_lattices(sK0,X0,X3),X1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(X1,sK0,X0,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X3,sK5(X1,sK0,X0,X2))
        | ~ r2_hidden(X1,a_3_4_lattice3(sK0,X0,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_28
    | ~ spl6_50 ),
    inference(superposition,[],[f781,f252])).

fof(f252,plain,
    ( ! [X2,X0,X1] :
        ( k3_lattices(sK0,X1,sK5(X0,sK0,X1,X2)) = X0
        | ~ r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f251])).

fof(f781,plain,
    ( ! [X2,X0,X1] :
        ( r3_lattices(sK0,k3_lattices(sK0,X0,X1),k3_lattices(sK0,X0,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X1,X2) )
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f780])).

fof(f782,plain,
    ( ~ spl6_3
    | spl6_6
    | spl6_50
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f778,f102,f780,f106,f94])).

fof(f778,plain,
    ( ! [X2,X0,X1] :
        ( r3_lattices(sK0,k3_lattices(sK0,X0,X1),k3_lattices(sK0,X0,X2))
        | ~ r3_lattices(sK0,X1,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f565,f103])).

fof(f103,plain,
    ( v10_lattices(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f565,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v10_lattices(X0)
      | r3_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
      | ~ r3_lattices(X0,X2,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f564])).

fof(f564,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l3_lattices(X0)
      | r3_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
      | ~ r3_lattices(X0,X2,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f507,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
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

fof(f507,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_lattices(X1)
      | ~ l3_lattices(X1)
      | r3_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3))
      | ~ r3_lattices(X1,X0,X3)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ v10_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f506])).

fof(f506,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r3_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3))
      | ~ r3_lattices(X1,X0,X3)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v4_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f453,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f453,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r3_lattices(X1,k3_lattices(X1,X3,X2),k3_lattices(X1,X3,X0))
      | ~ r3_lattices(X1,X2,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v4_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f452])).

fof(f452,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r3_lattices(X1,k3_lattices(X1,X3,X2),k3_lattices(X1,X3,X0))
      | ~ r3_lattices(X1,X2,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v5_lattices(X1)
      | ~ v4_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f407,f61])).

fof(f61,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f407,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v6_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r3_lattices(X1,k3_lattices(X1,X0,X3),k3_lattices(X1,X0,X2))
      | ~ r3_lattices(X1,X3,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_lattices(X1)
      | ~ v4_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f406])).

fof(f406,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r3_lattices(X1,k3_lattices(X1,X0,X3),k3_lattices(X1,X0,X2))
      | ~ r3_lattices(X1,X3,X2)
      | ~ v6_lattices(X1)
      | ~ v5_lattices(X1)
      | ~ v4_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f350,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f350,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2))
      | ~ r3_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f349])).

fof(f349,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2))
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f64,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v9_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2))
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2))
                  | ~ r3_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2))
                  | ~ r3_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_lattices(X0,X1,X2)
                   => r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_filter_0)).

fof(f655,plain,
    ( spl6_6
    | ~ spl6_3
    | ~ spl6_8
    | spl6_9
    | spl6_47 ),
    inference(avatar_split_clause,[],[f653,f642,f124,f121,f94,f106])).

fof(f653,plain,
    ( r3_lattice3(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl6_47 ),
    inference(resolution,[],[f643,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f643,plain,
    ( ~ m1_subset_1(sK4(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),a_3_4_lattice3(sK0,sK1,sK2)),u1_struct_0(sK0))
    | spl6_47 ),
    inference(avatar_component_clause,[],[f642])).

fof(f253,plain,
    ( spl6_6
    | ~ spl6_5
    | ~ spl6_3
    | spl6_28
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f249,f98,f251,f94,f102,f106])).

fof(f249,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | k3_lattices(sK0,X1,sK5(X0,sK0,X1,X2)) = X0
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f79,f99])).

fof(f99,plain,
    ( v4_lattice3(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_lattice3(X1)
      | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | k3_lattices(X1,X2,sK5(X0,X1,X2,X3)) = X0
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f199,plain,
    ( spl6_6
    | spl6_19
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f195,f102,f94,f197,f106])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ l3_lattices(sK0)
        | r3_lattices(sK0,X0,X1)
        | ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_5 ),
    inference(resolution,[],[f194,f103])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | r3_lattices(X1,X0,X2)
      | ~ r1_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r3_lattices(X1,X0,X2)
      | ~ r1_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f192,f61])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r3_lattices(X1,X2,X0)
      | ~ r1_lattices(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ v10_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r3_lattices(X1,X2,X0)
      | ~ r1_lattices(X1,X2,X0)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f168,f62])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f77,f63])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f190,plain,
    ( spl6_6
    | ~ spl6_3
    | spl6_18
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f186,f182,f188,f94,f106])).

fof(f182,plain,
    ( spl6_17
  <=> ! [X1,X0] :
        ( r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,sK4(sK0,X0,X1))
        | r3_lattice3(sK0,X0,X1)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_17 ),
    inference(duplicate_literal_removal,[],[f185])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,sK4(sK0,X0,X1))
        | r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_17 ),
    inference(resolution,[],[f183,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,sK4(X0,X1,X2))
      | r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X1) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f182])).

fof(f184,plain,
    ( spl6_6
    | spl6_17
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f180,f102,f94,f182,f106])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( ~ l3_lattices(sK0)
        | r1_lattices(sK0,X0,X1)
        | ~ r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_5 ),
    inference(resolution,[],[f179,f103])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X0,X2)
      | ~ r3_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X0,X2)
      | ~ r3_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f177,f61])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X2,X0)
      | ~ r3_lattices(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ v10_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X2,X0)
      | ~ r3_lattices(X1,X2,X0)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f166,f62])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f76,f63])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f175,plain,
    ( spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | ~ spl6_3
    | spl6_16
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f170,f161,f145,f173,f94,f98,f102,f106])).

fof(f145,plain,
    ( spl6_13
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | r1_lattices(sK0,X2,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f161,plain,
    ( spl6_15
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2))
        | r2_hidden(sK5(X0,sK0,X1,X2),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f170,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,X3,sK5(X0,sK0,X1,X2))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X3,X2) )
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattices(sK0,X3,sK5(X0,sK0,X1,X2))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X3,X2)
        | ~ r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2)) )
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(resolution,[],[f78,f164])).

fof(f164,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK5(X0,sK0,X1,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattices(sK0,X3,sK5(X0,sK0,X1,X2))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X3,X2)
        | ~ r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2)) )
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(resolution,[],[f162,f146])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | r1_lattices(sK0,X2,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f162,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK5(X0,sK0,X1,X2),X2)
        | ~ r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f161])).

fof(f163,plain,
    ( spl6_6
    | ~ spl6_5
    | ~ spl6_3
    | spl6_15
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f159,f98,f161,f94,f102,f106])).

fof(f159,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | r2_hidden(sK5(X0,sK0,X1,X2),X2)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f80,f99])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_lattice3(X1)
      | ~ r2_hidden(X0,a_3_4_lattice3(X1,X2,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r2_hidden(sK5(X0,X1,X2,X3),X3)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f149,plain,
    ( spl6_6
    | ~ spl6_3
    | spl6_12 ),
    inference(avatar_split_clause,[],[f148,f136,f94,f106])).

fof(f148,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl6_12 ),
    inference(resolution,[],[f137,f74])).

fof(f137,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f147,plain,
    ( ~ spl6_3
    | spl6_13
    | spl6_6 ),
    inference(avatar_split_clause,[],[f143,f106,f145,f94])).

fof(f143,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | r1_lattices(sK0,X2,X0) )
    | spl6_6 ),
    inference(resolution,[],[f70,f107])).

fof(f107,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f142,plain,
    ( ~ spl6_3
    | spl6_11 ),
    inference(avatar_split_clause,[],[f141,f132,f94])).

fof(f132,plain,
    ( spl6_11
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f141,plain,
    ( ~ l3_lattices(sK0)
    | spl6_11 ),
    inference(resolution,[],[f133,f57])).

fof(f57,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f133,plain,
    ( ~ l2_lattices(sK0)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f140,plain,
    ( ~ spl6_3
    | spl6_6
    | ~ spl6_5
    | spl6_10 ),
    inference(avatar_split_clause,[],[f139,f129,f102,f106,f94])).

fof(f129,plain,
    ( spl6_10
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f139,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl6_10 ),
    inference(resolution,[],[f130,f59])).

fof(f130,plain,
    ( ~ v4_lattices(sK0)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f138,plain,
    ( spl6_6
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_2
    | ~ spl6_12
    | spl6_8 ),
    inference(avatar_split_clause,[],[f127,f121,f136,f90,f132,f129,f106])).

fof(f127,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0)
    | spl6_8 ),
    inference(resolution,[],[f122,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_lattices)).

fof(f122,plain,
    ( ~ m1_subset_1(k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),u1_struct_0(sK0))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f126,plain,
    ( ~ spl6_8
    | ~ spl6_9
    | spl6_1
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f119,f116,f86,f124,f121])).

fof(f86,plain,
    ( spl6_1
  <=> r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f116,plain,
    ( spl6_7
  <=> ! [X1,X0] :
        ( ~ r3_lattice3(sK0,X0,X1)
        | r3_lattices(sK0,X0,k16_lattice3(sK0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f119,plain,
    ( ~ r3_lattice3(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),a_3_4_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_7 ),
    inference(resolution,[],[f117,f87])).

fof(f87,plain,
    ( ~ r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,X0,k16_lattice3(sK0,X1))
        | ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f118,plain,
    ( spl6_6
    | ~ spl6_5
    | ~ spl6_3
    | spl6_7
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f111,f98,f116,f94,f102,f106])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | r3_lattices(sK0,X0,k16_lattice3(sK0,X1))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f110,f99])).

fof(f110,plain,(
    ! [X4,X2,X0] :
      ( ~ v4_lattice3(X0)
      | ~ r3_lattice3(X0,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X4,k16_lattice3(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f82,f74])).

fof(f82,plain,(
    ! [X4,X2,X0] :
      ( r3_lattices(X0,X4,k16_lattice3(X0,X2))
      | ~ r3_lattice3(X0,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r3_lattices(X0,X4,X1)
      | ~ r3_lattice3(X0,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f108,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f51,f106])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] : ~ r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] : ~ r3_lattices(sK0,k3_lattices(sK0,X1,k16_lattice3(sK0,X2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,X1,X2)))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] : ~ r3_lattices(sK0,k3_lattices(sK0,X1,k16_lattice3(sK0,X2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,X1,X2)))
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] : ~ r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,X2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,X2)))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] : ~ r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,X2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,X2)))
   => ~ r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] : ~ r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] : ~ r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] : r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] : r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_lattice3)).

fof(f104,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f52,f102])).

fof(f52,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f100,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f53,f98])).

fof(f53,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f96,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f54,f94])).

fof(f54,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f55,f90])).

fof(f55,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f56,f86])).

fof(f56,plain,(
    ~ r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (20665)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (20667)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (20659)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (20673)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (20673)Refutation not found, incomplete strategy% (20673)------------------------------
% 0.20/0.48  % (20673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (20673)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (20673)Memory used [KB]: 10618
% 0.20/0.48  % (20673)Time elapsed: 0.065 s
% 0.20/0.48  % (20673)------------------------------
% 0.20/0.48  % (20673)------------------------------
% 0.20/0.48  % (20657)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (20658)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (20663)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (20654)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (20653)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (20655)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (20654)Refutation not found, incomplete strategy% (20654)------------------------------
% 0.20/0.50  % (20654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (20654)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (20654)Memory used [KB]: 10618
% 0.20/0.50  % (20654)Time elapsed: 0.091 s
% 0.20/0.50  % (20654)------------------------------
% 0.20/0.50  % (20654)------------------------------
% 0.20/0.50  % (20669)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (20671)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (20668)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (20670)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (20672)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (20662)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (20661)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.52  % (20666)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.52  % (20656)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (20664)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.52  % (20660)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.45/0.54  % (20659)Refutation found. Thanks to Tanya!
% 1.45/0.54  % SZS status Theorem for theBenchmark
% 1.45/0.54  % SZS output start Proof for theBenchmark
% 1.45/0.54  fof(f909,plain,(
% 1.45/0.54    $false),
% 1.45/0.54    inference(avatar_sat_refutation,[],[f88,f92,f96,f100,f104,f108,f118,f126,f138,f140,f142,f147,f149,f163,f175,f184,f190,f199,f253,f655,f782,f807,f881,f890,f908])).
% 1.45/0.54  fof(f908,plain,(
% 1.45/0.54    spl6_6 | ~spl6_5 | ~spl6_4 | ~spl6_3 | spl6_58),
% 1.45/0.54    inference(avatar_split_clause,[],[f899,f888,f94,f98,f102,f106])).
% 1.45/0.54  fof(f106,plain,(
% 1.45/0.54    spl6_6 <=> v2_struct_0(sK0)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.45/0.54  fof(f102,plain,(
% 1.45/0.54    spl6_5 <=> v10_lattices(sK0)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.45/0.54  fof(f98,plain,(
% 1.45/0.54    spl6_4 <=> v4_lattice3(sK0)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.45/0.54  fof(f94,plain,(
% 1.45/0.54    spl6_3 <=> l3_lattices(sK0)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.45/0.54  fof(f888,plain,(
% 1.45/0.54    spl6_58 <=> r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK2)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 1.45/0.54  fof(f899,plain,(
% 1.45/0.54    ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | spl6_58),
% 1.45/0.54    inference(resolution,[],[f889,f109])).
% 1.45/0.54  fof(f109,plain,(
% 1.45/0.54    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(subsumption_resolution,[],[f83,f74])).
% 1.45/0.54  fof(f74,plain,(
% 1.45/0.54    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f26])).
% 1.45/0.54  fof(f26,plain,(
% 1.45/0.54    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(flattening,[],[f25])).
% 1.45/0.54  fof(f25,plain,(
% 1.45/0.54    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f7])).
% 1.45/0.54  fof(f7,axiom,(
% 1.45/0.54    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 1.45/0.54  fof(f83,plain,(
% 1.45/0.54    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(equality_resolution,[],[f65])).
% 1.45/0.54  fof(f65,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f41])).
% 1.45/0.54  fof(f41,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 1.45/0.54  fof(f40,plain,(
% 1.45/0.54    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 1.45/0.54    introduced(choice_axiom,[])).
% 1.45/0.54  fof(f39,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(rectify,[],[f38])).
% 1.45/0.54  fof(f38,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(flattening,[],[f37])).
% 1.45/0.54  fof(f37,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(nnf_transformation,[],[f22])).
% 1.45/0.54  fof(f22,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(flattening,[],[f21])).
% 1.45/0.54  fof(f21,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f9])).
% 1.45/0.54  fof(f9,axiom,(
% 1.45/0.54    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).
% 1.45/0.54  fof(f889,plain,(
% 1.45/0.54    ~r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK2) | spl6_58),
% 1.45/0.54    inference(avatar_component_clause,[],[f888])).
% 1.45/0.54  fof(f890,plain,(
% 1.45/0.54    ~spl6_2 | ~spl6_58 | ~spl6_12 | ~spl6_8 | ~spl6_47 | spl6_9 | ~spl6_57),
% 1.45/0.54    inference(avatar_split_clause,[],[f882,f879,f124,f642,f121,f136,f888,f90])).
% 1.45/0.54  fof(f90,plain,(
% 1.45/0.54    spl6_2 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.45/0.54  fof(f136,plain,(
% 1.45/0.54    spl6_12 <=> m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.45/0.54  fof(f121,plain,(
% 1.45/0.54    spl6_8 <=> m1_subset_1(k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),u1_struct_0(sK0))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.45/0.54  fof(f642,plain,(
% 1.45/0.54    spl6_47 <=> m1_subset_1(sK4(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),a_3_4_lattice3(sK0,sK1,sK2)),u1_struct_0(sK0))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 1.45/0.54  fof(f124,plain,(
% 1.45/0.54    spl6_9 <=> r3_lattice3(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),a_3_4_lattice3(sK0,sK1,sK2))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.45/0.54  fof(f879,plain,(
% 1.45/0.54    spl6_57 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,k3_lattices(sK0,X1,X0),a_3_4_lattice3(sK0,X1,X2)),u1_struct_0(sK0)) | ~m1_subset_1(k3_lattices(sK0,X1,X0),u1_struct_0(sK0)) | r3_lattice3(sK0,k3_lattices(sK0,X1,X0),a_3_4_lattice3(sK0,X1,X2)) | ~r3_lattice3(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 1.45/0.54  fof(f882,plain,(
% 1.45/0.54    ~m1_subset_1(sK4(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),a_3_4_lattice3(sK0,sK1,sK2)),u1_struct_0(sK0)) | ~m1_subset_1(k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl6_9 | ~spl6_57)),
% 1.45/0.54    inference(resolution,[],[f880,f125])).
% 1.45/0.54  fof(f125,plain,(
% 1.45/0.54    ~r3_lattice3(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | spl6_9),
% 1.45/0.54    inference(avatar_component_clause,[],[f124])).
% 1.45/0.54  fof(f880,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (r3_lattice3(sK0,k3_lattices(sK0,X1,X0),a_3_4_lattice3(sK0,X1,X2)) | ~m1_subset_1(sK4(sK0,k3_lattices(sK0,X1,X0),a_3_4_lattice3(sK0,X1,X2)),u1_struct_0(sK0)) | ~m1_subset_1(k3_lattices(sK0,X1,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl6_57),
% 1.45/0.54    inference(avatar_component_clause,[],[f879])).
% 1.45/0.54  fof(f881,plain,(
% 1.45/0.54    spl6_6 | ~spl6_3 | spl6_57 | ~spl6_16 | ~spl6_18 | ~spl6_52),
% 1.45/0.54    inference(avatar_split_clause,[],[f877,f805,f188,f173,f879,f94,f106])).
% 1.45/0.54  fof(f173,plain,(
% 1.45/0.54    spl6_16 <=> ! [X1,X3,X0,X2] : (~r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2)) | ~r3_lattice3(sK0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,X3,sK5(X0,sK0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.45/0.54  fof(f188,plain,(
% 1.45/0.54    spl6_18 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattice3(sK0,X0,X1) | ~r3_lattices(sK0,X0,sK4(sK0,X0,X1)) | ~m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.45/0.54  fof(f805,plain,(
% 1.45/0.54    spl6_52 <=> ! [X5,X7,X8,X6] : (~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_lattices(sK0,X5,sK5(X7,sK0,X6,X8)) | ~r2_hidden(X7,a_3_4_lattice3(sK0,X6,X8)) | r3_lattices(sK0,k3_lattices(sK0,X6,X5),X7) | ~m1_subset_1(X6,u1_struct_0(sK0)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 1.45/0.54  fof(f877,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,X2) | r3_lattice3(sK0,k3_lattices(sK0,X1,X0),a_3_4_lattice3(sK0,X1,X2)) | ~m1_subset_1(k3_lattices(sK0,X1,X0),u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,k3_lattices(sK0,X1,X0),a_3_4_lattice3(sK0,X1,X2)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl6_16 | ~spl6_18 | ~spl6_52)),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f874])).
% 1.45/0.54  fof(f874,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,X2) | r3_lattice3(sK0,k3_lattices(sK0,X1,X0),a_3_4_lattice3(sK0,X1,X2)) | ~m1_subset_1(k3_lattices(sK0,X1,X0),u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,k3_lattices(sK0,X1,X0),a_3_4_lattice3(sK0,X1,X2)),u1_struct_0(sK0)) | r3_lattice3(sK0,k3_lattices(sK0,X1,X0),a_3_4_lattice3(sK0,X1,X2)) | ~m1_subset_1(k3_lattices(sK0,X1,X0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl6_16 | ~spl6_18 | ~spl6_52)),
% 1.45/0.54    inference(resolution,[],[f813,f72])).
% 1.45/0.54  fof(f72,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f45])).
% 1.45/0.54  fof(f45,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 1.45/0.54  fof(f44,plain,(
% 1.45/0.54    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 1.45/0.54    introduced(choice_axiom,[])).
% 1.45/0.54  fof(f43,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(rectify,[],[f42])).
% 1.45/0.54  fof(f42,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(nnf_transformation,[],[f24])).
% 1.45/0.54  fof(f24,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(flattening,[],[f23])).
% 1.45/0.54  fof(f23,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f6])).
% 1.45/0.54  fof(f6,axiom,(
% 1.45/0.54    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).
% 1.45/0.54  fof(f813,plain,(
% 1.45/0.54    ( ! [X4,X2,X3,X1] : (~r2_hidden(sK4(sK0,k3_lattices(sK0,X1,X2),X3),a_3_4_lattice3(sK0,X1,X4)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X2,X4) | r3_lattice3(sK0,k3_lattices(sK0,X1,X2),X3) | ~m1_subset_1(k3_lattices(sK0,X1,X2),u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,k3_lattices(sK0,X1,X2),X3),u1_struct_0(sK0))) ) | (~spl6_16 | ~spl6_18 | ~spl6_52)),
% 1.45/0.54    inference(resolution,[],[f811,f189])).
% 1.45/0.54  fof(f189,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~r3_lattices(sK0,X0,sK4(sK0,X0,X1)) | r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0))) ) | ~spl6_18),
% 1.45/0.54    inference(avatar_component_clause,[],[f188])).
% 1.45/0.54  fof(f811,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (r3_lattices(sK0,k3_lattices(sK0,X2,X0),X1) | ~r2_hidden(X1,a_3_4_lattice3(sK0,X2,X3)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,X3)) ) | (~spl6_16 | ~spl6_52)),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f808])).
% 1.45/0.54  fof(f808,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X1,a_3_4_lattice3(sK0,X2,X3)) | r3_lattices(sK0,k3_lattices(sK0,X2,X0),X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,X3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X1,a_3_4_lattice3(sK0,X2,X3)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (~spl6_16 | ~spl6_52)),
% 1.45/0.54    inference(resolution,[],[f806,f174])).
% 1.45/0.54  fof(f174,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (r1_lattices(sK0,X3,sK5(X0,sK0,X1,X2)) | ~r3_lattice3(sK0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl6_16),
% 1.45/0.54    inference(avatar_component_clause,[],[f173])).
% 1.45/0.54  fof(f806,plain,(
% 1.45/0.54    ( ! [X6,X8,X7,X5] : (~r1_lattices(sK0,X5,sK5(X7,sK0,X6,X8)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r2_hidden(X7,a_3_4_lattice3(sK0,X6,X8)) | r3_lattices(sK0,k3_lattices(sK0,X6,X5),X7) | ~m1_subset_1(X6,u1_struct_0(sK0))) ) | ~spl6_52),
% 1.45/0.54    inference(avatar_component_clause,[],[f805])).
% 1.45/0.54  fof(f807,plain,(
% 1.45/0.54    spl6_6 | ~spl6_5 | ~spl6_4 | ~spl6_3 | spl6_52 | ~spl6_19 | ~spl6_28 | ~spl6_50),
% 1.45/0.54    inference(avatar_split_clause,[],[f802,f780,f251,f197,f805,f94,f98,f102,f106])).
% 1.45/0.54  fof(f197,plain,(
% 1.45/0.54    spl6_19 <=> ! [X1,X0] : (r3_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattices(sK0,X0,X1))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.45/0.54  fof(f251,plain,(
% 1.45/0.54    spl6_28 <=> ! [X1,X0,X2] : (~r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2)) | k3_lattices(sK0,X1,sK5(X0,sK0,X1,X2)) = X0 | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 1.45/0.54  fof(f780,plain,(
% 1.45/0.54    spl6_50 <=> ! [X1,X0,X2] : (r3_lattices(sK0,k3_lattices(sK0,X0,X1),k3_lattices(sK0,X0,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,X1,X2))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 1.45/0.54  fof(f802,plain,(
% 1.45/0.54    ( ! [X6,X8,X7,X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r3_lattices(sK0,k3_lattices(sK0,X6,X5),X7) | ~r2_hidden(X7,a_3_4_lattice3(sK0,X6,X8)) | ~r1_lattices(sK0,X5,sK5(X7,sK0,X6,X8)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl6_19 | ~spl6_28 | ~spl6_50)),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f801])).
% 1.45/0.54  fof(f801,plain,(
% 1.45/0.54    ( ! [X6,X8,X7,X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r3_lattices(sK0,k3_lattices(sK0,X6,X5),X7) | ~r2_hidden(X7,a_3_4_lattice3(sK0,X6,X8)) | ~r1_lattices(sK0,X5,sK5(X7,sK0,X6,X8)) | ~r2_hidden(X7,a_3_4_lattice3(sK0,X6,X8)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl6_19 | ~spl6_28 | ~spl6_50)),
% 1.45/0.54    inference(resolution,[],[f788,f78])).
% 1.45/0.54  fof(f78,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1)) | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f50])).
% 1.45/0.54  fof(f50,plain,(
% 1.45/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) | ! [X4] : (~r2_hidden(X4,X3) | k3_lattices(X1,X2,X4) != X0 | ~m1_subset_1(X4,u1_struct_0(X1)))) & ((r2_hidden(sK5(X0,X1,X2,X3),X3) & k3_lattices(X1,X2,sK5(X0,X1,X2,X3)) = X0 & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1))) | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.45/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f48,f49])).
% 1.45/0.54  fof(f49,plain,(
% 1.45/0.54    ! [X3,X2,X1,X0] : (? [X5] : (r2_hidden(X5,X3) & k3_lattices(X1,X2,X5) = X0 & m1_subset_1(X5,u1_struct_0(X1))) => (r2_hidden(sK5(X0,X1,X2,X3),X3) & k3_lattices(X1,X2,sK5(X0,X1,X2,X3)) = X0 & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1))))),
% 1.45/0.54    introduced(choice_axiom,[])).
% 1.45/0.54  fof(f48,plain,(
% 1.45/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) | ! [X4] : (~r2_hidden(X4,X3) | k3_lattices(X1,X2,X4) != X0 | ~m1_subset_1(X4,u1_struct_0(X1)))) & (? [X5] : (r2_hidden(X5,X3) & k3_lattices(X1,X2,X5) = X0 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.45/0.54    inference(rectify,[],[f47])).
% 1.45/0.54  fof(f47,plain,(
% 1.45/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) | ! [X4] : (~r2_hidden(X4,X3) | k3_lattices(X1,X2,X4) != X0 | ~m1_subset_1(X4,u1_struct_0(X1)))) & (? [X4] : (r2_hidden(X4,X3) & k3_lattices(X1,X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.45/0.54    inference(nnf_transformation,[],[f32])).
% 1.45/0.54  fof(f32,plain,(
% 1.45/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) <=> ? [X4] : (r2_hidden(X4,X3) & k3_lattices(X1,X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X1)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.45/0.54    inference(flattening,[],[f31])).
% 1.45/0.54  fof(f31,plain,(
% 1.45/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) <=> ? [X4] : (r2_hidden(X4,X3) & k3_lattices(X1,X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X1)))) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 1.45/0.54    inference(ennf_transformation,[],[f8])).
% 1.45/0.54  fof(f8,axiom,(
% 1.45/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,u1_struct_0(X1)) & l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) <=> ? [X4] : (r2_hidden(X4,X3) & k3_lattices(X1,X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X1)))))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_3_4_lattice3)).
% 1.45/0.54  fof(f788,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK5(X1,sK0,X2,X3),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r3_lattices(sK0,k3_lattices(sK0,X2,X0),X1) | ~r2_hidden(X1,a_3_4_lattice3(sK0,X2,X3)) | ~r1_lattices(sK0,X0,sK5(X1,sK0,X2,X3))) ) | (~spl6_19 | ~spl6_28 | ~spl6_50)),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f787])).
% 1.45/0.54  fof(f787,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK5(X1,sK0,X2,X3),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r3_lattices(sK0,k3_lattices(sK0,X2,X0),X1) | ~r2_hidden(X1,a_3_4_lattice3(sK0,X2,X3)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK5(X1,sK0,X2,X3),u1_struct_0(sK0)) | ~r1_lattices(sK0,X0,sK5(X1,sK0,X2,X3))) ) | (~spl6_19 | ~spl6_28 | ~spl6_50)),
% 1.45/0.54    inference(resolution,[],[f785,f198])).
% 1.45/0.54  fof(f198,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r3_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattices(sK0,X0,X1)) ) | ~spl6_19),
% 1.45/0.54    inference(avatar_component_clause,[],[f197])).
% 1.45/0.54  fof(f785,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~r3_lattices(sK0,X3,sK5(X1,sK0,X0,X2)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(X1,sK0,X0,X2),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattices(sK0,k3_lattices(sK0,X0,X3),X1) | ~r2_hidden(X1,a_3_4_lattice3(sK0,X0,X2))) ) | (~spl6_28 | ~spl6_50)),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f784])).
% 1.45/0.54  fof(f784,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (r3_lattices(sK0,k3_lattices(sK0,X0,X3),X1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(X1,sK0,X0,X2),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,X3,sK5(X1,sK0,X0,X2)) | ~r2_hidden(X1,a_3_4_lattice3(sK0,X0,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl6_28 | ~spl6_50)),
% 1.45/0.54    inference(superposition,[],[f781,f252])).
% 1.45/0.54  fof(f252,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (k3_lattices(sK0,X1,sK5(X0,sK0,X1,X2)) = X0 | ~r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl6_28),
% 1.45/0.54    inference(avatar_component_clause,[],[f251])).
% 1.45/0.54  fof(f781,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (r3_lattices(sK0,k3_lattices(sK0,X0,X1),k3_lattices(sK0,X0,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,X1,X2)) ) | ~spl6_50),
% 1.45/0.54    inference(avatar_component_clause,[],[f780])).
% 1.45/0.54  fof(f782,plain,(
% 1.45/0.54    ~spl6_3 | spl6_6 | spl6_50 | ~spl6_5),
% 1.45/0.54    inference(avatar_split_clause,[],[f778,f102,f780,f106,f94])).
% 1.45/0.54  fof(f778,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (r3_lattices(sK0,k3_lattices(sK0,X0,X1),k3_lattices(sK0,X0,X2)) | ~r3_lattices(sK0,X1,X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~l3_lattices(sK0)) ) | ~spl6_5),
% 1.45/0.54    inference(resolution,[],[f565,f103])).
% 1.45/0.54  fof(f103,plain,(
% 1.45/0.54    v10_lattices(sK0) | ~spl6_5),
% 1.45/0.54    inference(avatar_component_clause,[],[f102])).
% 1.45/0.54  fof(f565,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~v10_lattices(X0) | r3_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~r3_lattices(X0,X2,X3) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f564])).
% 1.45/0.54  fof(f564,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~l3_lattices(X0) | r3_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~r3_lattices(X0,X2,X3) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~v10_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.45/0.54    inference(resolution,[],[f507,f59])).
% 1.45/0.54  fof(f59,plain,(
% 1.45/0.54    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f18])).
% 1.45/0.54  fof(f18,plain,(
% 1.45/0.54    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.45/0.54    inference(flattening,[],[f17])).
% 1.45/0.54  fof(f17,plain,(
% 1.45/0.54    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.45/0.54    inference(ennf_transformation,[],[f13])).
% 1.45/0.54  fof(f13,plain,(
% 1.45/0.54    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.45/0.54    inference(pure_predicate_removal,[],[f1])).
% 1.45/0.54  fof(f1,axiom,(
% 1.45/0.54    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 1.45/0.54  fof(f507,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~v4_lattices(X1) | ~l3_lattices(X1) | r3_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) | ~r3_lattices(X1,X0,X3) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~v10_lattices(X1)) )),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f506])).
% 1.45/0.54  fof(f506,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l3_lattices(X1) | r3_lattices(X1,k3_lattices(X1,X2,X0),k3_lattices(X1,X2,X3)) | ~r3_lattices(X1,X0,X3) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v4_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 1.45/0.54    inference(resolution,[],[f453,f60])).
% 1.45/0.54  fof(f60,plain,(
% 1.45/0.54    ( ! [X0] : (v5_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f18])).
% 1.45/0.54  fof(f453,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~v5_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r3_lattices(X1,k3_lattices(X1,X3,X2),k3_lattices(X1,X3,X0)) | ~r3_lattices(X1,X2,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v4_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1)) )),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f452])).
% 1.45/0.54  fof(f452,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r3_lattices(X1,k3_lattices(X1,X3,X2),k3_lattices(X1,X3,X0)) | ~r3_lattices(X1,X2,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v5_lattices(X1) | ~v4_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 1.45/0.54    inference(resolution,[],[f407,f61])).
% 1.45/0.54  fof(f61,plain,(
% 1.45/0.54    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f18])).
% 1.45/0.54  fof(f407,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~v6_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | r3_lattices(X1,k3_lattices(X1,X0,X3),k3_lattices(X1,X0,X2)) | ~r3_lattices(X1,X3,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v5_lattices(X1) | ~v4_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1)) )),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f406])).
% 1.45/0.54  fof(f406,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | r3_lattices(X1,k3_lattices(X1,X0,X3),k3_lattices(X1,X0,X2)) | ~r3_lattices(X1,X3,X2) | ~v6_lattices(X1) | ~v5_lattices(X1) | ~v4_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 1.45/0.54    inference(resolution,[],[f350,f62])).
% 1.45/0.54  fof(f62,plain,(
% 1.45/0.54    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f18])).
% 1.45/0.54  fof(f350,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~v8_lattices(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2)) | ~r3_lattices(X0,X1,X2) | ~v6_lattices(X0) | ~v5_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f349])).
% 1.45/0.54  fof(f349,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2)) | ~v8_lattices(X0) | ~v6_lattices(X0) | ~v5_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.45/0.54    inference(resolution,[],[f64,f63])).
% 1.45/0.54  fof(f63,plain,(
% 1.45/0.54    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f18])).
% 1.45/0.54  fof(f64,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~v9_lattices(X0) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2)) | ~v8_lattices(X0) | ~v6_lattices(X0) | ~v5_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f20])).
% 1.45/0.54  fof(f20,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2)) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | ~v5_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(flattening,[],[f19])).
% 1.45/0.54  fof(f19,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2)) | ~r3_lattices(X0,X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | ~v5_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f5])).
% 1.45/0.54  fof(f5,axiom,(
% 1.45/0.54    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k3_lattices(X0,X3,X1),k3_lattices(X0,X3,X2)))))))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_filter_0)).
% 1.45/0.54  fof(f655,plain,(
% 1.45/0.54    spl6_6 | ~spl6_3 | ~spl6_8 | spl6_9 | spl6_47),
% 1.45/0.54    inference(avatar_split_clause,[],[f653,f642,f124,f121,f94,f106])).
% 1.45/0.54  fof(f653,plain,(
% 1.45/0.54    r3_lattice3(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | spl6_47),
% 1.45/0.54    inference(resolution,[],[f643,f71])).
% 1.45/0.54  fof(f71,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f45])).
% 1.45/0.54  fof(f643,plain,(
% 1.45/0.54    ~m1_subset_1(sK4(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),a_3_4_lattice3(sK0,sK1,sK2)),u1_struct_0(sK0)) | spl6_47),
% 1.45/0.54    inference(avatar_component_clause,[],[f642])).
% 1.45/0.54  fof(f253,plain,(
% 1.45/0.54    spl6_6 | ~spl6_5 | ~spl6_3 | spl6_28 | ~spl6_4),
% 1.45/0.54    inference(avatar_split_clause,[],[f249,f98,f251,f94,f102,f106])).
% 1.45/0.54  fof(f249,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k3_lattices(sK0,X1,sK5(X0,sK0,X1,X2)) = X0 | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl6_4),
% 1.45/0.54    inference(resolution,[],[f79,f99])).
% 1.45/0.54  fof(f99,plain,(
% 1.45/0.54    v4_lattice3(sK0) | ~spl6_4),
% 1.45/0.54    inference(avatar_component_clause,[],[f98])).
% 1.45/0.54  fof(f79,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~v4_lattice3(X1) | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | k3_lattices(X1,X2,sK5(X0,X1,X2,X3)) = X0 | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f50])).
% 1.45/0.54  fof(f199,plain,(
% 1.45/0.54    spl6_6 | spl6_19 | ~spl6_3 | ~spl6_5),
% 1.45/0.54    inference(avatar_split_clause,[],[f195,f102,f94,f197,f106])).
% 1.45/0.54  fof(f195,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~l3_lattices(sK0) | r3_lattices(sK0,X0,X1) | ~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl6_5),
% 1.45/0.54    inference(resolution,[],[f194,f103])).
% 1.45/0.54  fof(f194,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~l3_lattices(X1) | r3_lattices(X1,X0,X2) | ~r1_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f193])).
% 1.45/0.54  fof(f193,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l3_lattices(X1) | r3_lattices(X1,X0,X2) | ~r1_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 1.45/0.54    inference(resolution,[],[f192,f61])).
% 1.45/0.54  fof(f192,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~v6_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r3_lattices(X1,X2,X0) | ~r1_lattices(X1,X2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~v10_lattices(X1)) )),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f191])).
% 1.45/0.54  fof(f191,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r3_lattices(X1,X2,X0) | ~r1_lattices(X1,X2,X0) | ~v6_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 1.45/0.54    inference(resolution,[],[f168,f62])).
% 1.45/0.54  fof(f168,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~v8_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f167])).
% 1.45/0.54  fof(f167,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.45/0.54    inference(resolution,[],[f77,f63])).
% 1.45/0.54  fof(f77,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f46])).
% 1.45/0.54  fof(f46,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(nnf_transformation,[],[f30])).
% 1.45/0.54  fof(f30,plain,(
% 1.45/0.54    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(flattening,[],[f29])).
% 1.45/0.54  fof(f29,plain,(
% 1.45/0.54    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f4])).
% 1.45/0.54  fof(f4,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 1.45/0.54  fof(f190,plain,(
% 1.45/0.54    spl6_6 | ~spl6_3 | spl6_18 | ~spl6_17),
% 1.45/0.54    inference(avatar_split_clause,[],[f186,f182,f188,f94,f106])).
% 1.45/0.54  fof(f182,plain,(
% 1.45/0.54    spl6_17 <=> ! [X1,X0] : (r1_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X1))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.45/0.54  fof(f186,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,sK4(sK0,X0,X1)) | r3_lattice3(sK0,X0,X1) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl6_17),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f185])).
% 1.45/0.54  fof(f185,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,sK4(sK0,X0,X1)) | r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl6_17),
% 1.45/0.54    inference(resolution,[],[f183,f73])).
% 1.45/0.54  fof(f73,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,sK4(X0,X1,X2)) | r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f45])).
% 1.45/0.54  fof(f183,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r1_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X1)) ) | ~spl6_17),
% 1.45/0.54    inference(avatar_component_clause,[],[f182])).
% 1.45/0.54  fof(f184,plain,(
% 1.45/0.54    spl6_6 | spl6_17 | ~spl6_3 | ~spl6_5),
% 1.45/0.54    inference(avatar_split_clause,[],[f180,f102,f94,f182,f106])).
% 1.45/0.54  fof(f180,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~l3_lattices(sK0) | r1_lattices(sK0,X0,X1) | ~r3_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl6_5),
% 1.45/0.54    inference(resolution,[],[f179,f103])).
% 1.45/0.54  fof(f179,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~l3_lattices(X1) | r1_lattices(X1,X0,X2) | ~r3_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f178])).
% 1.45/0.54  fof(f178,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l3_lattices(X1) | r1_lattices(X1,X0,X2) | ~r3_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 1.45/0.54    inference(resolution,[],[f177,f61])).
% 1.45/0.54  fof(f177,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~v6_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r1_lattices(X1,X2,X0) | ~r3_lattices(X1,X2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~v10_lattices(X1)) )),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f176])).
% 1.45/0.54  fof(f176,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r1_lattices(X1,X2,X0) | ~r3_lattices(X1,X2,X0) | ~v6_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 1.45/0.54    inference(resolution,[],[f166,f62])).
% 1.45/0.54  fof(f166,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~v8_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f165])).
% 1.45/0.54  fof(f165,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.45/0.54    inference(resolution,[],[f76,f63])).
% 1.45/0.54  fof(f76,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f46])).
% 1.45/0.54  fof(f175,plain,(
% 1.45/0.54    spl6_6 | ~spl6_5 | ~spl6_4 | ~spl6_3 | spl6_16 | ~spl6_13 | ~spl6_15),
% 1.45/0.54    inference(avatar_split_clause,[],[f170,f161,f145,f173,f94,f98,f102,f106])).
% 1.45/0.54  fof(f145,plain,(
% 1.45/0.54    spl6_13 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | r1_lattices(sK0,X2,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.45/0.54  fof(f161,plain,(
% 1.45/0.54    spl6_15 <=> ! [X1,X0,X2] : (~r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2)) | r2_hidden(sK5(X0,sK0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.45/0.54  fof(f170,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | r1_lattices(sK0,X3,sK5(X0,sK0,X1,X2)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X3,X2)) ) | (~spl6_13 | ~spl6_15)),
% 1.45/0.54    inference(duplicate_literal_removal,[],[f169])).
% 1.45/0.54  fof(f169,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X3,sK5(X0,sK0,X1,X2)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X3,X2) | ~r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2))) ) | (~spl6_13 | ~spl6_15)),
% 1.45/0.54    inference(resolution,[],[f78,f164])).
% 1.45/0.54  fof(f164,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK5(X0,sK0,X1,X2),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X3,sK5(X0,sK0,X1,X2)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X3,X2) | ~r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2))) ) | (~spl6_13 | ~spl6_15)),
% 1.45/0.54    inference(resolution,[],[f162,f146])).
% 1.45/0.54  fof(f146,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r1_lattices(sK0,X2,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl6_13),
% 1.45/0.54    inference(avatar_component_clause,[],[f145])).
% 1.45/0.54  fof(f162,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,sK0,X1,X2),X2) | ~r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl6_15),
% 1.45/0.54    inference(avatar_component_clause,[],[f161])).
% 1.45/0.54  fof(f163,plain,(
% 1.45/0.54    spl6_6 | ~spl6_5 | ~spl6_3 | spl6_15 | ~spl6_4),
% 1.45/0.54    inference(avatar_split_clause,[],[f159,f98,f161,f94,f102,f106])).
% 1.45/0.54  fof(f159,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_3_4_lattice3(sK0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r2_hidden(sK5(X0,sK0,X1,X2),X2) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl6_4),
% 1.45/0.54    inference(resolution,[],[f80,f99])).
% 1.45/0.54  fof(f80,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~v4_lattice3(X1) | ~r2_hidden(X0,a_3_4_lattice3(X1,X2,X3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r2_hidden(sK5(X0,X1,X2,X3),X3) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f50])).
% 1.45/0.54  fof(f149,plain,(
% 1.45/0.54    spl6_6 | ~spl6_3 | spl6_12),
% 1.45/0.54    inference(avatar_split_clause,[],[f148,f136,f94,f106])).
% 1.45/0.54  fof(f148,plain,(
% 1.45/0.54    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl6_12),
% 1.45/0.54    inference(resolution,[],[f137,f74])).
% 1.45/0.54  fof(f137,plain,(
% 1.45/0.54    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | spl6_12),
% 1.45/0.54    inference(avatar_component_clause,[],[f136])).
% 1.45/0.54  fof(f147,plain,(
% 1.45/0.54    ~spl6_3 | spl6_13 | spl6_6),
% 1.45/0.54    inference(avatar_split_clause,[],[f143,f106,f145,f94])).
% 1.45/0.54  fof(f143,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r1_lattices(sK0,X2,X0)) ) | spl6_6),
% 1.45/0.54    inference(resolution,[],[f70,f107])).
% 1.45/0.54  fof(f107,plain,(
% 1.45/0.54    ~v2_struct_0(sK0) | spl6_6),
% 1.45/0.54    inference(avatar_component_clause,[],[f106])).
% 1.45/0.54  fof(f70,plain,(
% 1.45/0.54    ( ! [X4,X2,X0,X1] : (v2_struct_0(X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X4)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f45])).
% 1.45/0.54  fof(f142,plain,(
% 1.45/0.54    ~spl6_3 | spl6_11),
% 1.45/0.54    inference(avatar_split_clause,[],[f141,f132,f94])).
% 1.45/0.54  fof(f132,plain,(
% 1.45/0.54    spl6_11 <=> l2_lattices(sK0)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.45/0.54  fof(f141,plain,(
% 1.45/0.54    ~l3_lattices(sK0) | spl6_11),
% 1.45/0.54    inference(resolution,[],[f133,f57])).
% 1.45/0.54  fof(f57,plain,(
% 1.45/0.54    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f16])).
% 1.45/0.54  fof(f16,plain,(
% 1.45/0.54    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 1.45/0.54    inference(ennf_transformation,[],[f12])).
% 1.45/0.54  fof(f12,plain,(
% 1.45/0.54    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 1.45/0.54    inference(pure_predicate_removal,[],[f3])).
% 1.45/0.54  fof(f3,axiom,(
% 1.45/0.54    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 1.45/0.54  fof(f133,plain,(
% 1.45/0.54    ~l2_lattices(sK0) | spl6_11),
% 1.45/0.54    inference(avatar_component_clause,[],[f132])).
% 1.45/0.54  fof(f140,plain,(
% 1.45/0.54    ~spl6_3 | spl6_6 | ~spl6_5 | spl6_10),
% 1.45/0.54    inference(avatar_split_clause,[],[f139,f129,f102,f106,f94])).
% 1.45/0.54  fof(f129,plain,(
% 1.45/0.54    spl6_10 <=> v4_lattices(sK0)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.45/0.54  fof(f139,plain,(
% 1.45/0.54    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl6_10),
% 1.45/0.54    inference(resolution,[],[f130,f59])).
% 1.45/0.54  fof(f130,plain,(
% 1.45/0.54    ~v4_lattices(sK0) | spl6_10),
% 1.45/0.54    inference(avatar_component_clause,[],[f129])).
% 1.45/0.54  fof(f138,plain,(
% 1.45/0.54    spl6_6 | ~spl6_10 | ~spl6_11 | ~spl6_2 | ~spl6_12 | spl6_8),
% 1.45/0.54    inference(avatar_split_clause,[],[f127,f121,f136,f90,f132,f129,f106])).
% 1.45/0.54  fof(f127,plain,(
% 1.45/0.54    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0) | spl6_8),
% 1.45/0.54    inference(resolution,[],[f122,f75])).
% 1.45/0.54  fof(f75,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f28])).
% 1.45/0.54  fof(f28,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(flattening,[],[f27])).
% 1.45/0.54  fof(f27,plain,(
% 1.45/0.54    ! [X0,X1,X2] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f2])).
% 1.45/0.54  fof(f2,axiom,(
% 1.45/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_lattices)).
% 1.45/0.54  fof(f122,plain,(
% 1.45/0.54    ~m1_subset_1(k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),u1_struct_0(sK0)) | spl6_8),
% 1.45/0.54    inference(avatar_component_clause,[],[f121])).
% 1.45/0.54  fof(f126,plain,(
% 1.45/0.54    ~spl6_8 | ~spl6_9 | spl6_1 | ~spl6_7),
% 1.45/0.54    inference(avatar_split_clause,[],[f119,f116,f86,f124,f121])).
% 1.45/0.54  fof(f86,plain,(
% 1.45/0.54    spl6_1 <=> r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.45/0.54  fof(f116,plain,(
% 1.45/0.54    spl6_7 <=> ! [X1,X0] : (~r3_lattice3(sK0,X0,X1) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.45/0.54  fof(f119,plain,(
% 1.45/0.54    ~r3_lattice3(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),a_3_4_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),u1_struct_0(sK0)) | (spl6_1 | ~spl6_7)),
% 1.45/0.54    inference(resolution,[],[f117,f87])).
% 1.45/0.54  fof(f87,plain,(
% 1.45/0.54    ~r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) | spl6_1),
% 1.45/0.54    inference(avatar_component_clause,[],[f86])).
% 1.45/0.54  fof(f117,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) | ~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl6_7),
% 1.45/0.54    inference(avatar_component_clause,[],[f116])).
% 1.45/0.54  fof(f118,plain,(
% 1.45/0.54    spl6_6 | ~spl6_5 | ~spl6_3 | spl6_7 | ~spl6_4),
% 1.45/0.54    inference(avatar_split_clause,[],[f111,f98,f116,f94,f102,f106])).
% 1.45/0.54  fof(f111,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl6_4),
% 1.45/0.54    inference(resolution,[],[f110,f99])).
% 1.45/0.54  fof(f110,plain,(
% 1.45/0.54    ( ! [X4,X2,X0] : (~v4_lattice3(X0) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X4,k16_lattice3(X0,X2)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(subsumption_resolution,[],[f82,f74])).
% 1.45/0.54  fof(f82,plain,(
% 1.45/0.54    ( ! [X4,X2,X0] : (r3_lattices(X0,X4,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(equality_resolution,[],[f66])).
% 1.45/0.54  fof(f66,plain,(
% 1.45/0.54    ( ! [X4,X2,X0,X1] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f41])).
% 1.45/0.54  fof(f108,plain,(
% 1.45/0.54    ~spl6_6),
% 1.45/0.54    inference(avatar_split_clause,[],[f51,f106])).
% 1.45/0.54  fof(f51,plain,(
% 1.45/0.54    ~v2_struct_0(sK0)),
% 1.45/0.54    inference(cnf_transformation,[],[f36])).
% 1.45/0.54  fof(f36,plain,(
% 1.45/0.54    (~r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 1.45/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f35,f34,f33])).
% 1.45/0.54  fof(f33,plain,(
% 1.45/0.54    ? [X0] : (? [X1] : (? [X2] : ~r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ~r3_lattices(sK0,k3_lattices(sK0,X1,k16_lattice3(sK0,X2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,X1,X2))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 1.45/0.54    introduced(choice_axiom,[])).
% 1.45/0.54  fof(f34,plain,(
% 1.45/0.54    ? [X1] : (? [X2] : ~r3_lattices(sK0,k3_lattices(sK0,X1,k16_lattice3(sK0,X2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,X1,X2))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ~r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,X2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,X2))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.45/0.54    introduced(choice_axiom,[])).
% 1.45/0.54  fof(f35,plain,(
% 1.45/0.54    ? [X2] : ~r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,X2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,X2))) => ~r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))),
% 1.45/0.54    introduced(choice_axiom,[])).
% 1.45/0.54  fof(f15,plain,(
% 1.45/0.54    ? [X0] : (? [X1] : (? [X2] : ~r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.45/0.54    inference(flattening,[],[f14])).
% 1.45/0.54  fof(f14,plain,(
% 1.45/0.54    ? [X0] : (? [X1] : (? [X2] : ~r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f11])).
% 1.45/0.54  fof(f11,negated_conjecture,(
% 1.45/0.54    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))))),
% 1.45/0.54    inference(negated_conjecture,[],[f10])).
% 1.45/0.54  fof(f10,conjecture,(
% 1.45/0.54    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : r3_lattices(X0,k3_lattices(X0,X1,k16_lattice3(X0,X2)),k16_lattice3(X0,a_3_4_lattice3(X0,X1,X2)))))),
% 1.45/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_lattice3)).
% 1.45/0.54  fof(f104,plain,(
% 1.45/0.54    spl6_5),
% 1.45/0.54    inference(avatar_split_clause,[],[f52,f102])).
% 1.45/0.54  fof(f52,plain,(
% 1.45/0.54    v10_lattices(sK0)),
% 1.45/0.54    inference(cnf_transformation,[],[f36])).
% 1.45/0.54  fof(f100,plain,(
% 1.45/0.54    spl6_4),
% 1.45/0.54    inference(avatar_split_clause,[],[f53,f98])).
% 1.45/0.54  fof(f53,plain,(
% 1.45/0.54    v4_lattice3(sK0)),
% 1.45/0.54    inference(cnf_transformation,[],[f36])).
% 1.45/0.54  fof(f96,plain,(
% 1.45/0.54    spl6_3),
% 1.45/0.54    inference(avatar_split_clause,[],[f54,f94])).
% 1.45/0.54  fof(f54,plain,(
% 1.45/0.54    l3_lattices(sK0)),
% 1.45/0.54    inference(cnf_transformation,[],[f36])).
% 1.45/0.54  fof(f92,plain,(
% 1.45/0.54    spl6_2),
% 1.45/0.54    inference(avatar_split_clause,[],[f55,f90])).
% 1.45/0.54  fof(f55,plain,(
% 1.45/0.54    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.45/0.54    inference(cnf_transformation,[],[f36])).
% 1.45/0.54  fof(f88,plain,(
% 1.45/0.54    ~spl6_1),
% 1.45/0.54    inference(avatar_split_clause,[],[f56,f86])).
% 1.45/0.54  fof(f56,plain,(
% 1.45/0.54    ~r3_lattices(sK0,k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)),k16_lattice3(sK0,a_3_4_lattice3(sK0,sK1,sK2)))),
% 1.45/0.54    inference(cnf_transformation,[],[f36])).
% 1.45/0.54  % SZS output end Proof for theBenchmark
% 1.45/0.54  % (20659)------------------------------
% 1.45/0.54  % (20659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.54  % (20659)Termination reason: Refutation
% 1.45/0.54  
% 1.45/0.54  % (20659)Memory used [KB]: 11513
% 1.45/0.54  % (20659)Time elapsed: 0.086 s
% 1.45/0.54  % (20659)------------------------------
% 1.45/0.54  % (20659)------------------------------
% 1.45/0.55  % (20652)Success in time 0.189 s
%------------------------------------------------------------------------------
