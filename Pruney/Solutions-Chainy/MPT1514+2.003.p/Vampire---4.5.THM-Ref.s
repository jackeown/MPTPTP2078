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
% DateTime   : Thu Dec  3 13:15:46 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 850 expanded)
%              Number of leaves         :   22 ( 308 expanded)
%              Depth                    :   37
%              Number of atoms          : 1009 (7259 expanded)
%              Number of equality atoms :   43 (  79 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1168,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f267,f280,f369,f383,f503,f1164])).

fof(f1164,plain,
    ( ~ spl8_5
    | spl8_6
    | ~ spl8_19 ),
    inference(avatar_contradiction_clause,[],[f1163])).

fof(f1163,plain,
    ( $false
    | ~ spl8_5
    | spl8_6
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f1162,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
    & ! [X3] :
        ( ( r2_hidden(sK3(X3),sK2)
          & r3_lattices(sK0,X3,sK3(X3))
          & m1_subset_1(sK3(X3),u1_struct_0(sK0)) )
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
            & ! [X3] :
                ( ? [X4] :
                    ( r2_hidden(X4,X2)
                    & r3_lattices(X0,X3,X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( ~ r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(sK0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(sK0)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2,X1] :
        ( ~ r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X2))
        & ! [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(sK0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(sK0)) )
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) )
   => ( ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
      & ! [X3] :
          ( ? [X4] :
              ( r2_hidden(X4,sK2)
              & r3_lattices(sK0,X3,X4)
              & m1_subset_1(X4,u1_struct_0(sK0)) )
          | ~ r2_hidden(X3,sK1)
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X3] :
      ( ? [X4] :
          ( r2_hidden(X4,sK2)
          & r3_lattices(sK0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(sK0)) )
     => ( r2_hidden(sK3(X3),sK2)
        & r3_lattices(sK0,X3,sK3(X3))
        & m1_subset_1(sK3(X3),u1_struct_0(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
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
       => ! [X1,X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ~ ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( r2_hidden(X4,X2)
                            & r3_lattices(X0,X3,X4) ) )
                    & r2_hidden(X3,X1) ) )
           => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ~ ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ~ ( r2_hidden(X4,X2)
                          & r3_lattices(X0,X3,X4) ) )
                  & r2_hidden(X3,X1) ) )
         => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).

fof(f1162,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_5
    | spl8_6
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f1161,f54])).

fof(f54,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f1161,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5
    | spl8_6
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f1160,f55])).

fof(f55,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f1160,plain,
    ( ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5
    | spl8_6
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f1159,f56])).

fof(f56,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f1159,plain,
    ( ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5
    | spl8_6
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f1158,f261])).

fof(f261,plain,
    ( m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl8_5
  <=> m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f1158,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5
    | spl8_6
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f1156,f266])).

fof(f266,plain,
    ( ~ r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl8_6
  <=> r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f1156,plain,
    ( r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5
    | ~ spl8_19 ),
    inference(resolution,[],[f1143,f87])).

fof(f87,plain,(
    ! [X2,X3,X1] :
      ( ~ r4_lattice3(X1,X3,X2)
      | r2_hidden(X3,a_2_2_lattice3(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r4_lattice3(X1,sK5(X0,X1,X2),X2)
            & sK5(X0,X1,X2) = X0
            & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK5(X0,X1,X2),X2)
        & sK5(X0,X1,X2) = X0
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r4_lattice3(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r4_lattice3(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

fof(f1143,plain,
    ( r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1)
    | ~ spl8_5
    | ~ spl8_19 ),
    inference(resolution,[],[f609,f489])).

fof(f489,plain,
    ( r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),a_2_5_lattice3(sK0,sK2))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f488])).

fof(f488,plain,
    ( spl8_19
  <=> r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),a_2_5_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f609,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2))
        | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f608,f290])).

fof(f290,plain,
    ( ! [X0] :
        ( r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0)
        | m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0)) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f289,f53])).

fof(f289,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0))
        | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0)
        | v2_struct_0(sK0) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f287,f56])).

fof(f287,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0))
        | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f261,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r4_lattice3(X0,X1,X2)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK4(X0,X1,X2),X1)
                  & r2_hidden(sK4(X0,X1,X2),X2)
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK4(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X2)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X3,X1)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
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
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

fof(f608,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2))
        | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f607,f53])).

fof(f607,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2))
        | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0)
        | v2_struct_0(sK0) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f606,f56])).

fof(f606,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2))
        | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f603,f261])).

fof(f603,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2))
        | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0)
        | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f591,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,sK4(X0,X1,X2),X1)
      | r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f591,plain,
    ( ! [X1] :
        ( r1_lattices(sK0,X1,k15_lattice3(sK0,sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_5_lattice3(sK0,sK2)) )
    | ~ spl8_5 ),
    inference(resolution,[],[f236,f261])).

fof(f236,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(k15_lattice3(sK0,X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r1_lattices(sK0,X3,k15_lattice3(sK0,X4))
      | ~ r2_hidden(X3,a_2_5_lattice3(sK0,X4)) ) ),
    inference(subsumption_resolution,[],[f235,f53])).

fof(f235,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,a_2_5_lattice3(sK0,X4))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r1_lattices(sK0,X3,k15_lattice3(sK0,X4))
      | ~ m1_subset_1(k15_lattice3(sK0,X4),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f234,f93])).

fof(f93,plain,(
    v6_lattices(sK0) ),
    inference(global_subsumption,[],[f56,f92])).

fof(f92,plain,
    ( v6_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f89,f53])).

fof(f89,plain,
    ( v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f54,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
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
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
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

fof(f234,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,a_2_5_lattice3(sK0,X4))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r1_lattices(sK0,X3,k15_lattice3(sK0,X4))
      | ~ m1_subset_1(k15_lattice3(sK0,X4),u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f233,f95])).

fof(f95,plain,(
    v8_lattices(sK0) ),
    inference(global_subsumption,[],[f56,f94])).

fof(f94,plain,
    ( v8_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f90,f53])).

fof(f90,plain,
    ( v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f54,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f233,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,a_2_5_lattice3(sK0,X4))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r1_lattices(sK0,X3,k15_lattice3(sK0,X4))
      | ~ m1_subset_1(k15_lattice3(sK0,X4),u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f232,f97])).

fof(f97,plain,(
    v9_lattices(sK0) ),
    inference(global_subsumption,[],[f56,f96])).

fof(f96,plain,
    ( v9_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f91,f53])).

fof(f91,plain,
    ( v9_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f54,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f232,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,a_2_5_lattice3(sK0,X4))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r1_lattices(sK0,X3,k15_lattice3(sK0,X4))
      | ~ m1_subset_1(k15_lattice3(sK0,X4),u1_struct_0(sK0))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f225,f56])).

fof(f225,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,a_2_5_lattice3(sK0,X4))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r1_lattices(sK0,X3,k15_lattice3(sK0,X4))
      | ~ m1_subset_1(k15_lattice3(sK0,X4),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,a_2_5_lattice3(sK0,X4))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r1_lattices(sK0,X3,k15_lattice3(sK0,X4))
      | ~ m1_subset_1(k15_lattice3(sK0,X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f156,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f156,plain,(
    ! [X2,X1] :
      ( r3_lattices(sK0,X2,k15_lattice3(sK0,X1))
      | ~ r2_hidden(X2,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f155,f53])).

fof(f155,plain,(
    ! [X2,X1] :
      ( r3_lattices(sK0,X2,k15_lattice3(sK0,X1))
      | ~ r2_hidden(X2,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f154,f54])).

fof(f154,plain,(
    ! [X2,X1] :
      ( r3_lattices(sK0,X2,k15_lattice3(sK0,X1))
      | ~ r2_hidden(X2,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f153,f55])).

fof(f153,plain,(
    ! [X2,X1] :
      ( r3_lattices(sK0,X2,k15_lattice3(sK0,X1))
      | ~ r2_hidden(X2,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f152,f56])).

fof(f152,plain,(
    ! [X2,X1] :
      ( r3_lattices(sK0,X2,k15_lattice3(sK0,X1))
      | ~ r2_hidden(X2,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f68,f103])).

fof(f103,plain,(
    ! [X0] : k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0)) ),
    inference(global_subsumption,[],[f56,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f101,f53])).

fof(f101,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f98,f54])).

fof(f98,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f55,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
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
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

fof(f503,plain,
    ( ~ spl8_5
    | spl8_6
    | ~ spl8_8
    | ~ spl8_9
    | spl8_19 ),
    inference(avatar_contradiction_clause,[],[f502])).

fof(f502,plain,
    ( $false
    | ~ spl8_5
    | spl8_6
    | ~ spl8_8
    | ~ spl8_9
    | spl8_19 ),
    inference(subsumption_resolution,[],[f501,f362])).

fof(f362,plain,
    ( r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl8_8
  <=> r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f501,plain,
    ( ~ r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | spl8_19 ),
    inference(subsumption_resolution,[],[f500,f368])).

fof(f368,plain,
    ( r2_hidden(sK3(sK4(sK0,k15_lattice3(sK0,sK2),sK1)),sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl8_9
  <=> r2_hidden(sK3(sK4(sK0,k15_lattice3(sK0,sK2),sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f500,plain,
    ( ~ r2_hidden(sK3(sK4(sK0,k15_lattice3(sK0,sK2),sK1)),sK2)
    | ~ r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ spl8_5
    | spl8_6
    | spl8_19 ),
    inference(subsumption_resolution,[],[f499,f341])).

fof(f341,plain,
    ( m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ spl8_5
    | spl8_6 ),
    inference(resolution,[],[f318,f266])).

fof(f318,plain,
    ( ! [X0] :
        ( r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0))
        | m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0)) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f317,f53])).

fof(f317,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0))
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f316,f54])).

fof(f316,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0))
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f315,f55])).

fof(f315,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0))
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0))
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f314,f56])).

fof(f314,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0))
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f312,f261])).

fof(f312,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0))
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0))
        | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f290,f87])).

fof(f499,plain,
    ( ~ m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK3(sK4(sK0,k15_lattice3(sK0,sK2),sK1)),sK2)
    | ~ r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | spl8_19 ),
    inference(resolution,[],[f490,f175])).

fof(f175,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK3(X0),X1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f174,f57])).

fof(f57,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,sK1)
      | m1_subset_1(sK3(X3),u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f174,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK3(X0),X1)
      | r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f173,f53])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK3(X0),X1)
      | r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f172,f54])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK3(X0),X1)
      | r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f171,f55])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK3(X0),X1)
      | r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f170,f56])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK3(X0),X1)
      | r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK3(X0),X1)
      | r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f58,f88])).

fof(f88,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r3_lattices(X1,X3,X4)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X3,a_2_5_lattice3(X1,X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r3_lattices(X1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X2)
            & r3_lattices(X1,sK6(X0,X1,X2),sK7(X0,X1,X2))
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
            & sK6(X0,X1,X2) = X0
            & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f49,f51,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X2)
              & r3_lattices(X1,X5,X6)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,X2)
            & r3_lattices(X1,sK6(X0,X1,X2),X6)
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK6(X0,X1,X2) = X0
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r3_lattices(X1,sK6(X0,X1,X2),X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK7(X0,X1,X2),X2)
        & r3_lattices(X1,sK6(X0,X1,X2),sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,X2)
                  & r3_lattices(X1,X5,X6)
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).

fof(f58,plain,(
    ! [X3] :
      ( r3_lattices(sK0,X3,sK3(X3))
      | ~ r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f490,plain,
    ( ~ r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),a_2_5_lattice3(sK0,sK2))
    | spl8_19 ),
    inference(avatar_component_clause,[],[f488])).

fof(f383,plain,
    ( ~ spl8_5
    | spl8_6
    | spl8_8 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | ~ spl8_5
    | spl8_6
    | spl8_8 ),
    inference(subsumption_resolution,[],[f381,f266])).

fof(f381,plain,
    ( r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1))
    | ~ spl8_5
    | spl8_8 ),
    inference(resolution,[],[f363,f299])).

fof(f299,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),X0)
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0)) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f298,f53])).

fof(f298,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),X0)
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f297,f54])).

fof(f297,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),X0)
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f296,f55])).

fof(f296,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),X0)
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0))
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f295,f56])).

fof(f295,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),X0)
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f293,f261])).

fof(f293,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),X0)
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0))
        | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f292,f87])).

fof(f292,plain,
    ( ! [X1] :
        ( r4_lattice3(sK0,k15_lattice3(sK0,sK2),X1)
        | r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X1),X1) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f291,f53])).

fof(f291,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X1),X1)
        | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X1)
        | v2_struct_0(sK0) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f288,f56])).

fof(f288,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X1),X1)
        | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X1)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f261,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(sK4(X0,X1,X2),X2)
      | r4_lattice3(X0,X1,X2)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f363,plain,
    ( ~ r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f361])).

fof(f369,plain,
    ( spl8_9
    | ~ spl8_8
    | ~ spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f353,f264,f260,f361,f366])).

fof(f353,plain,
    ( ~ r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | r2_hidden(sK3(sK4(sK0,k15_lattice3(sK0,sK2),sK1)),sK2)
    | ~ spl8_5
    | spl8_6 ),
    inference(resolution,[],[f341,f59])).

fof(f59,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(sK3(X3),sK2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f280,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | spl8_5 ),
    inference(subsumption_resolution,[],[f278,f53])).

fof(f278,plain,
    ( v2_struct_0(sK0)
    | spl8_5 ),
    inference(subsumption_resolution,[],[f277,f56])).

fof(f277,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_5 ),
    inference(resolution,[],[f262,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f262,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | spl8_5 ),
    inference(avatar_component_clause,[],[f260])).

fof(f267,plain,
    ( ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f253,f264,f260])).

fof(f253,plain,
    ( ~ r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f166,f60])).

fof(f60,plain,(
    ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f166,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ r2_hidden(X1,a_2_2_lattice3(sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f165,f53])).

fof(f165,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ r2_hidden(X1,a_2_2_lattice3(sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f164,f54])).

fof(f164,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ r2_hidden(X1,a_2_2_lattice3(sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f163,f55])).

fof(f163,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ r2_hidden(X1,a_2_2_lattice3(sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f162,f56])).

fof(f162,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ r2_hidden(X1,a_2_2_lattice3(sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f69,f109])).

fof(f109,plain,(
    ! [X2] : k15_lattice3(sK0,X2) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X2)) ),
    inference(global_subsumption,[],[f56,f108])).

fof(f108,plain,(
    ! [X2] :
      ( ~ l3_lattices(sK0)
      | k15_lattice3(sK0,X2) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X2)) ) ),
    inference(subsumption_resolution,[],[f107,f53])).

fof(f107,plain,(
    ! [X2] :
      ( ~ l3_lattices(sK0)
      | k15_lattice3(sK0,X2) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X2))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f100,f54])).

fof(f100,plain,(
    ! [X2] :
      ( ~ l3_lattices(sK0)
      | k15_lattice3(sK0,X2) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X2))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f55,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:12:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (10325)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (10332)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (10315)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (10335)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (10321)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (10326)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (10326)Refutation not found, incomplete strategy% (10326)------------------------------
% 0.20/0.51  % (10326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (10326)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (10326)Memory used [KB]: 6140
% 0.20/0.51  % (10326)Time elapsed: 0.059 s
% 0.20/0.51  % (10326)------------------------------
% 0.20/0.51  % (10326)------------------------------
% 0.20/0.52  % (10318)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (10320)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (10320)Refutation not found, incomplete strategy% (10320)------------------------------
% 0.20/0.52  % (10320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10320)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10320)Memory used [KB]: 1663
% 0.20/0.52  % (10320)Time elapsed: 0.111 s
% 0.20/0.52  % (10320)------------------------------
% 0.20/0.52  % (10320)------------------------------
% 0.20/0.52  % (10319)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.53  % (10333)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.53  % (10328)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.53  % (10314)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (10322)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.53  % (10317)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.53  % (10316)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.54  % (10338)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.54  % (10330)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.54  % (10331)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.54  % (10329)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.46/0.55  % (10323)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.46/0.55  % (10324)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.46/0.55  % (10324)Refutation not found, incomplete strategy% (10324)------------------------------
% 1.46/0.55  % (10324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (10324)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (10324)Memory used [KB]: 10618
% 1.46/0.55  % (10324)Time elapsed: 0.137 s
% 1.46/0.55  % (10324)------------------------------
% 1.46/0.55  % (10324)------------------------------
% 1.46/0.55  % (10319)Refutation not found, incomplete strategy% (10319)------------------------------
% 1.46/0.55  % (10319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (10319)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (10319)Memory used [KB]: 10618
% 1.46/0.55  % (10319)Time elapsed: 0.134 s
% 1.46/0.55  % (10319)------------------------------
% 1.46/0.55  % (10319)------------------------------
% 1.46/0.55  % (10336)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.46/0.55  % (10334)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.46/0.55  % (10327)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.46/0.56  % (10313)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.46/0.56  % (10313)Refutation not found, incomplete strategy% (10313)------------------------------
% 1.46/0.56  % (10313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (10313)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (10313)Memory used [KB]: 10618
% 1.46/0.56  % (10313)Time elapsed: 0.152 s
% 1.46/0.56  % (10313)------------------------------
% 1.46/0.56  % (10313)------------------------------
% 1.46/0.56  % (10314)Refutation found. Thanks to Tanya!
% 1.46/0.56  % SZS status Theorem for theBenchmark
% 1.46/0.56  % SZS output start Proof for theBenchmark
% 1.46/0.56  fof(f1168,plain,(
% 1.46/0.56    $false),
% 1.46/0.56    inference(avatar_sat_refutation,[],[f267,f280,f369,f383,f503,f1164])).
% 1.46/0.56  fof(f1164,plain,(
% 1.46/0.56    ~spl8_5 | spl8_6 | ~spl8_19),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f1163])).
% 1.46/0.56  fof(f1163,plain,(
% 1.46/0.56    $false | (~spl8_5 | spl8_6 | ~spl8_19)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1162,f53])).
% 1.46/0.56  fof(f53,plain,(
% 1.46/0.56    ~v2_struct_0(sK0)),
% 1.46/0.56    inference(cnf_transformation,[],[f38])).
% 1.46/0.56  fof(f38,plain,(
% 1.46/0.56    (~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) & ! [X3] : ((r2_hidden(sK3(X3),sK2) & r3_lattices(sK0,X3,sK3(X3)) & m1_subset_1(sK3(X3),u1_struct_0(sK0))) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)))) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f37,f36,f35])).
% 1.46/0.56  fof(f35,plain,(
% 1.46/0.56    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X2,X1] : (~r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(sK0,X3,X4) & m1_subset_1(X4,u1_struct_0(sK0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(sK0)))) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f36,plain,(
% 1.46/0.56    ? [X2,X1] : (~r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(sK0,X3,X4) & m1_subset_1(X4,u1_struct_0(sK0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(sK0)))) => (~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) & ! [X3] : (? [X4] : (r2_hidden(X4,sK2) & r3_lattices(sK0,X3,X4) & m1_subset_1(X4,u1_struct_0(sK0))) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0))))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f37,plain,(
% 1.46/0.56    ! [X3] : (? [X4] : (r2_hidden(X4,sK2) & r3_lattices(sK0,X3,X4) & m1_subset_1(X4,u1_struct_0(sK0))) => (r2_hidden(sK3(X3),sK2) & r3_lattices(sK0,X3,sK3(X3)) & m1_subset_1(sK3(X3),u1_struct_0(sK0))))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f16,plain,(
% 1.46/0.56    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f15])).
% 1.46/0.56  fof(f15,plain,(
% 1.46/0.56    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : ((? [X4] : ((r2_hidden(X4,X2) & r3_lattices(X0,X3,X4)) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f11])).
% 1.46/0.56  fof(f11,negated_conjecture,(
% 1.46/0.56    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 1.46/0.56    inference(negated_conjecture,[],[f10])).
% 1.46/0.56  fof(f10,conjecture,(
% 1.46/0.56    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).
% 1.46/0.56  fof(f1162,plain,(
% 1.46/0.56    v2_struct_0(sK0) | (~spl8_5 | spl8_6 | ~spl8_19)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1161,f54])).
% 1.46/0.56  fof(f54,plain,(
% 1.46/0.56    v10_lattices(sK0)),
% 1.46/0.56    inference(cnf_transformation,[],[f38])).
% 1.46/0.56  fof(f1161,plain,(
% 1.46/0.56    ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_5 | spl8_6 | ~spl8_19)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1160,f55])).
% 1.46/0.56  fof(f55,plain,(
% 1.46/0.56    v4_lattice3(sK0)),
% 1.46/0.56    inference(cnf_transformation,[],[f38])).
% 1.46/0.56  fof(f1160,plain,(
% 1.46/0.56    ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_5 | spl8_6 | ~spl8_19)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1159,f56])).
% 1.46/0.56  fof(f56,plain,(
% 1.46/0.56    l3_lattices(sK0)),
% 1.46/0.56    inference(cnf_transformation,[],[f38])).
% 1.46/0.56  fof(f1159,plain,(
% 1.46/0.56    ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_5 | spl8_6 | ~spl8_19)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1158,f261])).
% 1.46/0.56  fof(f261,plain,(
% 1.46/0.56    m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~spl8_5),
% 1.46/0.56    inference(avatar_component_clause,[],[f260])).
% 1.46/0.56  fof(f260,plain,(
% 1.46/0.56    spl8_5 <=> m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.46/0.56  fof(f1158,plain,(
% 1.46/0.56    ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_5 | spl8_6 | ~spl8_19)),
% 1.46/0.56    inference(subsumption_resolution,[],[f1156,f266])).
% 1.46/0.56  fof(f266,plain,(
% 1.46/0.56    ~r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1)) | spl8_6),
% 1.46/0.56    inference(avatar_component_clause,[],[f264])).
% 1.46/0.56  fof(f264,plain,(
% 1.46/0.56    spl8_6 <=> r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.46/0.56  fof(f1156,plain,(
% 1.46/0.56    r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1)) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_5 | ~spl8_19)),
% 1.46/0.56    inference(resolution,[],[f1143,f87])).
% 1.46/0.56  fof(f87,plain,(
% 1.46/0.56    ( ! [X2,X3,X1] : (~r4_lattice3(X1,X3,X2) | r2_hidden(X3,a_2_2_lattice3(X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.46/0.56    inference(equality_resolution,[],[f80])).
% 1.46/0.56  fof(f80,plain,(
% 1.46/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f47])).
% 1.46/0.56  fof(f47,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK5(X0,X1,X2),X2) & sK5(X0,X1,X2) = X0 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).
% 1.46/0.56  fof(f46,plain,(
% 1.46/0.56    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK5(X0,X1,X2),X2) & sK5(X0,X1,X2) = X0 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f45,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.46/0.56    inference(rectify,[],[f44])).
% 1.46/0.56  fof(f44,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.46/0.56    inference(nnf_transformation,[],[f32])).
% 1.46/0.56  fof(f32,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.46/0.56    inference(flattening,[],[f31])).
% 1.46/0.56  fof(f31,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 1.46/0.56    inference(ennf_transformation,[],[f5])).
% 1.46/0.56  fof(f5,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).
% 1.46/0.56  fof(f1143,plain,(
% 1.46/0.56    r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1) | (~spl8_5 | ~spl8_19)),
% 1.46/0.56    inference(resolution,[],[f609,f489])).
% 1.46/0.56  fof(f489,plain,(
% 1.46/0.56    r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),a_2_5_lattice3(sK0,sK2)) | ~spl8_19),
% 1.46/0.56    inference(avatar_component_clause,[],[f488])).
% 1.46/0.56  fof(f488,plain,(
% 1.46/0.56    spl8_19 <=> r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),a_2_5_lattice3(sK0,sK2))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.46/0.56  fof(f609,plain,(
% 1.46/0.56    ( ! [X0] : (~r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2)) | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0)) ) | ~spl8_5),
% 1.46/0.56    inference(subsumption_resolution,[],[f608,f290])).
% 1.46/0.56  fof(f290,plain,(
% 1.46/0.56    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0) | m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0))) ) | ~spl8_5),
% 1.46/0.56    inference(subsumption_resolution,[],[f289,f53])).
% 1.46/0.56  fof(f289,plain,(
% 1.46/0.56    ( ! [X0] : (m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0)) | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0) | v2_struct_0(sK0)) ) | ~spl8_5),
% 1.46/0.56    inference(subsumption_resolution,[],[f287,f56])).
% 1.46/0.56  fof(f287,plain,(
% 1.46/0.56    ( ! [X0] : (m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0)) | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl8_5),
% 1.46/0.56    inference(resolution,[],[f261,f71])).
% 1.46/0.56  fof(f71,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | r4_lattice3(X0,X1,X2) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f42])).
% 1.46/0.56  fof(f42,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 1.46/0.56  fof(f41,plain,(
% 1.46/0.56    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f40,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(rectify,[],[f39])).
% 1.46/0.56  fof(f39,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(nnf_transformation,[],[f26])).
% 1.46/0.56  fof(f26,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f25])).
% 1.46/0.56  fof(f25,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f3])).
% 1.46/0.56  fof(f3,axiom,(
% 1.46/0.56    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 1.46/0.56  fof(f608,plain,(
% 1.46/0.56    ( ! [X0] : (~m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0)) | ~r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2)) | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0)) ) | ~spl8_5),
% 1.46/0.56    inference(subsumption_resolution,[],[f607,f53])).
% 1.46/0.56  fof(f607,plain,(
% 1.46/0.56    ( ! [X0] : (~m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0)) | ~r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2)) | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0) | v2_struct_0(sK0)) ) | ~spl8_5),
% 1.46/0.56    inference(subsumption_resolution,[],[f606,f56])).
% 1.46/0.56  fof(f606,plain,(
% 1.46/0.56    ( ! [X0] : (~m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0)) | ~r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2)) | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl8_5),
% 1.46/0.56    inference(subsumption_resolution,[],[f603,f261])).
% 1.46/0.56  fof(f603,plain,(
% 1.46/0.56    ( ! [X0] : (~m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0)) | ~r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2)) | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl8_5),
% 1.46/0.56    inference(resolution,[],[f591,f73])).
% 1.46/0.56  fof(f73,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~r1_lattices(X0,sK4(X0,X1,X2),X1) | r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f42])).
% 1.46/0.56  fof(f591,plain,(
% 1.46/0.56    ( ! [X1] : (r1_lattices(sK0,X1,k15_lattice3(sK0,sK2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,a_2_5_lattice3(sK0,sK2))) ) | ~spl8_5),
% 1.46/0.56    inference(resolution,[],[f236,f261])).
% 1.46/0.56  fof(f236,plain,(
% 1.46/0.56    ( ! [X4,X3] : (~m1_subset_1(k15_lattice3(sK0,X4),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,X3,k15_lattice3(sK0,X4)) | ~r2_hidden(X3,a_2_5_lattice3(sK0,X4))) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f235,f53])).
% 1.46/0.56  fof(f235,plain,(
% 1.46/0.56    ( ! [X4,X3] : (~r2_hidden(X3,a_2_5_lattice3(sK0,X4)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,X3,k15_lattice3(sK0,X4)) | ~m1_subset_1(k15_lattice3(sK0,X4),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f234,f93])).
% 1.46/0.56  fof(f93,plain,(
% 1.46/0.56    v6_lattices(sK0)),
% 1.46/0.56    inference(global_subsumption,[],[f56,f92])).
% 1.46/0.56  fof(f92,plain,(
% 1.46/0.56    v6_lattices(sK0) | ~l3_lattices(sK0)),
% 1.46/0.56    inference(subsumption_resolution,[],[f89,f53])).
% 1.46/0.56  fof(f89,plain,(
% 1.46/0.56    v6_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.46/0.56    inference(resolution,[],[f54,f62])).
% 1.46/0.56  fof(f62,plain,(
% 1.46/0.56    ( ! [X0] : (~v10_lattices(X0) | v6_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f18])).
% 1.46/0.56  fof(f18,plain,(
% 1.46/0.56    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.46/0.56    inference(flattening,[],[f17])).
% 1.46/0.56  fof(f17,plain,(
% 1.46/0.56    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f14])).
% 1.46/0.56  fof(f14,plain,(
% 1.46/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 1.46/0.56    inference(pure_predicate_removal,[],[f13])).
% 1.46/0.56  fof(f13,plain,(
% 1.46/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.46/0.56    inference(pure_predicate_removal,[],[f12])).
% 1.46/0.56  fof(f12,plain,(
% 1.46/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.46/0.56    inference(pure_predicate_removal,[],[f1])).
% 1.46/0.56  fof(f1,axiom,(
% 1.46/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 1.46/0.56  fof(f234,plain,(
% 1.46/0.56    ( ! [X4,X3] : (~r2_hidden(X3,a_2_5_lattice3(sK0,X4)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,X3,k15_lattice3(sK0,X4)) | ~m1_subset_1(k15_lattice3(sK0,X4),u1_struct_0(sK0)) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f233,f95])).
% 1.46/0.56  fof(f95,plain,(
% 1.46/0.56    v8_lattices(sK0)),
% 1.46/0.56    inference(global_subsumption,[],[f56,f94])).
% 1.46/0.56  fof(f94,plain,(
% 1.46/0.56    v8_lattices(sK0) | ~l3_lattices(sK0)),
% 1.46/0.56    inference(subsumption_resolution,[],[f90,f53])).
% 1.46/0.56  fof(f90,plain,(
% 1.46/0.56    v8_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.46/0.56    inference(resolution,[],[f54,f63])).
% 1.46/0.56  fof(f63,plain,(
% 1.46/0.56    ( ! [X0] : (~v10_lattices(X0) | v8_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f18])).
% 1.46/0.56  fof(f233,plain,(
% 1.46/0.56    ( ! [X4,X3] : (~r2_hidden(X3,a_2_5_lattice3(sK0,X4)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,X3,k15_lattice3(sK0,X4)) | ~m1_subset_1(k15_lattice3(sK0,X4),u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f232,f97])).
% 1.46/0.56  fof(f97,plain,(
% 1.46/0.56    v9_lattices(sK0)),
% 1.46/0.56    inference(global_subsumption,[],[f56,f96])).
% 1.46/0.56  fof(f96,plain,(
% 1.46/0.56    v9_lattices(sK0) | ~l3_lattices(sK0)),
% 1.46/0.56    inference(subsumption_resolution,[],[f91,f53])).
% 1.46/0.56  fof(f91,plain,(
% 1.46/0.56    v9_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.46/0.56    inference(resolution,[],[f54,f64])).
% 1.46/0.56  fof(f64,plain,(
% 1.46/0.56    ( ! [X0] : (~v10_lattices(X0) | v9_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f18])).
% 1.46/0.56  fof(f232,plain,(
% 1.46/0.56    ( ! [X4,X3] : (~r2_hidden(X3,a_2_5_lattice3(sK0,X4)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,X3,k15_lattice3(sK0,X4)) | ~m1_subset_1(k15_lattice3(sK0,X4),u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f225,f56])).
% 1.46/0.56  fof(f225,plain,(
% 1.46/0.56    ( ! [X4,X3] : (~r2_hidden(X3,a_2_5_lattice3(sK0,X4)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,X3,k15_lattice3(sK0,X4)) | ~m1_subset_1(k15_lattice3(sK0,X4),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(duplicate_literal_removal,[],[f223])).
% 1.46/0.56  fof(f223,plain,(
% 1.46/0.56    ( ! [X4,X3] : (~r2_hidden(X3,a_2_5_lattice3(sK0,X4)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,X3,k15_lattice3(sK0,X4)) | ~m1_subset_1(k15_lattice3(sK0,X4),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(resolution,[],[f156,f75])).
% 1.46/0.56  fof(f75,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f43])).
% 1.46/0.56  fof(f43,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(nnf_transformation,[],[f30])).
% 1.46/0.56  fof(f30,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f29])).
% 1.46/0.56  fof(f29,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f2])).
% 1.46/0.56  fof(f2,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 1.46/0.56  fof(f156,plain,(
% 1.46/0.56    ( ! [X2,X1] : (r3_lattices(sK0,X2,k15_lattice3(sK0,X1)) | ~r2_hidden(X2,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f155,f53])).
% 1.46/0.56  fof(f155,plain,(
% 1.46/0.56    ( ! [X2,X1] : (r3_lattices(sK0,X2,k15_lattice3(sK0,X1)) | ~r2_hidden(X2,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f154,f54])).
% 1.46/0.56  fof(f154,plain,(
% 1.46/0.56    ( ! [X2,X1] : (r3_lattices(sK0,X2,k15_lattice3(sK0,X1)) | ~r2_hidden(X2,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f153,f55])).
% 1.46/0.56  fof(f153,plain,(
% 1.46/0.56    ( ! [X2,X1] : (r3_lattices(sK0,X2,k15_lattice3(sK0,X1)) | ~r2_hidden(X2,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f152,f56])).
% 1.46/0.56  fof(f152,plain,(
% 1.46/0.56    ( ! [X2,X1] : (r3_lattices(sK0,X2,k15_lattice3(sK0,X1)) | ~r2_hidden(X2,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(superposition,[],[f68,f103])).
% 1.46/0.56  fof(f103,plain,(
% 1.46/0.56    ( ! [X0] : (k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))) )),
% 1.46/0.56    inference(global_subsumption,[],[f56,f102])).
% 1.46/0.56  fof(f102,plain,(
% 1.46/0.56    ( ! [X0] : (~l3_lattices(sK0) | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f101,f53])).
% 1.46/0.56  fof(f101,plain,(
% 1.46/0.56    ( ! [X0] : (~l3_lattices(sK0) | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0)) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f98,f54])).
% 1.46/0.56  fof(f98,plain,(
% 1.46/0.56    ( ! [X0] : (~l3_lattices(sK0) | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(resolution,[],[f55,f66])).
% 1.46/0.56  fof(f66,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~v4_lattice3(X0) | ~l3_lattices(X0) | k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f22])).
% 1.46/0.56  fof(f22,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f21])).
% 1.46/0.56  fof(f21,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f9])).
% 1.46/0.56  fof(f9,axiom,(
% 1.46/0.56    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).
% 1.46/0.56  fof(f68,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k15_lattice3(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f24])).
% 1.46/0.56  fof(f24,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f23])).
% 1.46/0.56  fof(f23,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f8])).
% 1.46/0.56  fof(f8,axiom,(
% 1.46/0.56    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).
% 1.46/0.56  fof(f503,plain,(
% 1.46/0.56    ~spl8_5 | spl8_6 | ~spl8_8 | ~spl8_9 | spl8_19),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f502])).
% 1.46/0.56  fof(f502,plain,(
% 1.46/0.56    $false | (~spl8_5 | spl8_6 | ~spl8_8 | ~spl8_9 | spl8_19)),
% 1.46/0.56    inference(subsumption_resolution,[],[f501,f362])).
% 1.46/0.56  fof(f362,plain,(
% 1.46/0.56    r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | ~spl8_8),
% 1.46/0.56    inference(avatar_component_clause,[],[f361])).
% 1.46/0.56  fof(f361,plain,(
% 1.46/0.56    spl8_8 <=> r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),sK1)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.46/0.56  fof(f501,plain,(
% 1.46/0.56    ~r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | (~spl8_5 | spl8_6 | ~spl8_9 | spl8_19)),
% 1.46/0.56    inference(subsumption_resolution,[],[f500,f368])).
% 1.46/0.56  fof(f368,plain,(
% 1.46/0.56    r2_hidden(sK3(sK4(sK0,k15_lattice3(sK0,sK2),sK1)),sK2) | ~spl8_9),
% 1.46/0.56    inference(avatar_component_clause,[],[f366])).
% 1.46/0.56  fof(f366,plain,(
% 1.46/0.56    spl8_9 <=> r2_hidden(sK3(sK4(sK0,k15_lattice3(sK0,sK2),sK1)),sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.46/0.56  fof(f500,plain,(
% 1.46/0.56    ~r2_hidden(sK3(sK4(sK0,k15_lattice3(sK0,sK2),sK1)),sK2) | ~r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | (~spl8_5 | spl8_6 | spl8_19)),
% 1.46/0.56    inference(subsumption_resolution,[],[f499,f341])).
% 1.46/0.56  fof(f341,plain,(
% 1.46/0.56    m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) | (~spl8_5 | spl8_6)),
% 1.46/0.56    inference(resolution,[],[f318,f266])).
% 1.46/0.56  fof(f318,plain,(
% 1.46/0.56    ( ! [X0] : (r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0)) | m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0))) ) | ~spl8_5),
% 1.46/0.56    inference(subsumption_resolution,[],[f317,f53])).
% 1.46/0.56  fof(f317,plain,(
% 1.46/0.56    ( ! [X0] : (m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0)) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0)) | v2_struct_0(sK0)) ) | ~spl8_5),
% 1.46/0.56    inference(subsumption_resolution,[],[f316,f54])).
% 1.46/0.56  fof(f316,plain,(
% 1.46/0.56    ( ! [X0] : (m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0)) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl8_5),
% 1.46/0.56    inference(subsumption_resolution,[],[f315,f55])).
% 1.46/0.56  fof(f315,plain,(
% 1.46/0.56    ( ! [X0] : (m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0)) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl8_5),
% 1.46/0.56    inference(subsumption_resolution,[],[f314,f56])).
% 1.46/0.56  fof(f314,plain,(
% 1.46/0.56    ( ! [X0] : (m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0)) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl8_5),
% 1.46/0.56    inference(subsumption_resolution,[],[f312,f261])).
% 1.46/0.56  fof(f312,plain,(
% 1.46/0.56    ( ! [X0] : (m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0)) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0)) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl8_5),
% 1.46/0.56    inference(resolution,[],[f290,f87])).
% 1.46/0.56  fof(f499,plain,(
% 1.46/0.56    ~m1_subset_1(sK4(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) | ~r2_hidden(sK3(sK4(sK0,k15_lattice3(sK0,sK2),sK1)),sK2) | ~r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | spl8_19),
% 1.46/0.56    inference(resolution,[],[f490,f175])).
% 1.46/0.56  fof(f175,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK3(X0),X1) | ~r2_hidden(X0,sK1)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f174,f57])).
% 1.46/0.56  fof(f57,plain,(
% 1.46/0.56    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1) | m1_subset_1(sK3(X3),u1_struct_0(sK0))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f38])).
% 1.46/0.56  fof(f174,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK3(X0),X1) | r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(sK3(X0),u1_struct_0(sK0))) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f173,f53])).
% 1.46/0.56  fof(f173,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK3(X0),X1) | r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(sK3(X0),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f172,f54])).
% 1.46/0.56  fof(f172,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK3(X0),X1) | r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(sK3(X0),u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f171,f55])).
% 1.46/0.56  fof(f171,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK3(X0),X1) | r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(sK3(X0),u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f170,f56])).
% 1.46/0.56  fof(f170,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK3(X0),X1) | r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(sK3(X0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(duplicate_literal_removal,[],[f167])).
% 1.46/0.56  fof(f167,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK3(X0),X1) | r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(sK3(X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(resolution,[],[f58,f88])).
% 1.46/0.56  fof(f88,plain,(
% 1.46/0.56    ( ! [X4,X2,X3,X1] : (~r3_lattices(X1,X3,X4) | ~r2_hidden(X4,X2) | r2_hidden(X3,a_2_5_lattice3(X1,X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.46/0.56    inference(equality_resolution,[],[f86])).
% 1.46/0.56  fof(f86,plain,(
% 1.46/0.56    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f52])).
% 1.46/0.56  fof(f52,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (((r2_hidden(sK7(X0,X1,X2),X2) & r3_lattices(X1,sK6(X0,X1,X2),sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))) & sK6(X0,X1,X2) = X0 & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f49,f51,f50])).
% 1.46/0.56  fof(f50,plain,(
% 1.46/0.56    ! [X2,X1,X0] : (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,sK6(X0,X1,X2),X6) & m1_subset_1(X6,u1_struct_0(X1))) & sK6(X0,X1,X2) = X0 & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f51,plain,(
% 1.46/0.56    ! [X2,X1,X0] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,sK6(X0,X1,X2),X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(sK7(X0,X1,X2),X2) & r3_lattices(X1,sK6(X0,X1,X2),sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f49,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.46/0.56    inference(rectify,[],[f48])).
% 1.46/0.56  fof(f48,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.46/0.56    inference(nnf_transformation,[],[f34])).
% 1.46/0.56  fof(f34,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.46/0.56    inference(flattening,[],[f33])).
% 1.46/0.56  fof(f33,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 1.46/0.56    inference(ennf_transformation,[],[f6])).
% 1.46/0.56  fof(f6,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).
% 1.46/0.56  fof(f58,plain,(
% 1.46/0.56    ( ! [X3] : (r3_lattices(sK0,X3,sK3(X3)) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f38])).
% 1.46/0.56  fof(f490,plain,(
% 1.46/0.56    ~r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),a_2_5_lattice3(sK0,sK2)) | spl8_19),
% 1.46/0.56    inference(avatar_component_clause,[],[f488])).
% 1.46/0.56  fof(f383,plain,(
% 1.46/0.56    ~spl8_5 | spl8_6 | spl8_8),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f382])).
% 1.46/0.56  fof(f382,plain,(
% 1.46/0.56    $false | (~spl8_5 | spl8_6 | spl8_8)),
% 1.46/0.56    inference(subsumption_resolution,[],[f381,f266])).
% 1.46/0.56  fof(f381,plain,(
% 1.46/0.56    r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1)) | (~spl8_5 | spl8_8)),
% 1.46/0.56    inference(resolution,[],[f363,f299])).
% 1.46/0.56  fof(f299,plain,(
% 1.46/0.56    ( ! [X0] : (r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),X0) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0))) ) | ~spl8_5),
% 1.46/0.56    inference(subsumption_resolution,[],[f298,f53])).
% 1.46/0.56  fof(f298,plain,(
% 1.46/0.56    ( ! [X0] : (r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),X0) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0)) | v2_struct_0(sK0)) ) | ~spl8_5),
% 1.46/0.56    inference(subsumption_resolution,[],[f297,f54])).
% 1.46/0.57  fof(f297,plain,(
% 1.46/0.57    ( ! [X0] : (r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),X0) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl8_5),
% 1.46/0.57    inference(subsumption_resolution,[],[f296,f55])).
% 1.46/0.57  fof(f296,plain,(
% 1.46/0.57    ( ! [X0] : (r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),X0) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl8_5),
% 1.46/0.57    inference(subsumption_resolution,[],[f295,f56])).
% 1.46/0.57  fof(f295,plain,(
% 1.46/0.57    ( ! [X0] : (r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),X0) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl8_5),
% 1.46/0.57    inference(subsumption_resolution,[],[f293,f261])).
% 1.46/0.57  fof(f293,plain,(
% 1.46/0.57    ( ! [X0] : (r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X0),X0) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X0)) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl8_5),
% 1.46/0.57    inference(resolution,[],[f292,f87])).
% 1.46/0.57  fof(f292,plain,(
% 1.46/0.57    ( ! [X1] : (r4_lattice3(sK0,k15_lattice3(sK0,sK2),X1) | r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X1),X1)) ) | ~spl8_5),
% 1.46/0.57    inference(subsumption_resolution,[],[f291,f53])).
% 1.46/0.57  fof(f291,plain,(
% 1.46/0.57    ( ! [X1] : (r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X1),X1) | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X1) | v2_struct_0(sK0)) ) | ~spl8_5),
% 1.46/0.57    inference(subsumption_resolution,[],[f288,f56])).
% 1.46/0.57  fof(f288,plain,(
% 1.46/0.57    ( ! [X1] : (r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),X1),X1) | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X1) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl8_5),
% 1.46/0.57    inference(resolution,[],[f261,f72])).
% 1.46/0.57  fof(f72,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(sK4(X0,X1,X2),X2) | r4_lattice3(X0,X1,X2) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f42])).
% 1.46/0.57  fof(f363,plain,(
% 1.46/0.57    ~r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | spl8_8),
% 1.46/0.57    inference(avatar_component_clause,[],[f361])).
% 1.46/0.57  fof(f369,plain,(
% 1.46/0.57    spl8_9 | ~spl8_8 | ~spl8_5 | spl8_6),
% 1.46/0.57    inference(avatar_split_clause,[],[f353,f264,f260,f361,f366])).
% 1.46/0.57  fof(f353,plain,(
% 1.46/0.57    ~r2_hidden(sK4(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | r2_hidden(sK3(sK4(sK0,k15_lattice3(sK0,sK2),sK1)),sK2) | (~spl8_5 | spl8_6)),
% 1.46/0.57    inference(resolution,[],[f341,f59])).
% 1.46/0.57  fof(f59,plain,(
% 1.46/0.57    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1) | r2_hidden(sK3(X3),sK2)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f38])).
% 1.46/0.57  fof(f280,plain,(
% 1.46/0.57    spl8_5),
% 1.46/0.57    inference(avatar_contradiction_clause,[],[f279])).
% 1.46/0.57  fof(f279,plain,(
% 1.46/0.57    $false | spl8_5),
% 1.46/0.57    inference(subsumption_resolution,[],[f278,f53])).
% 1.46/0.57  fof(f278,plain,(
% 1.46/0.57    v2_struct_0(sK0) | spl8_5),
% 1.46/0.57    inference(subsumption_resolution,[],[f277,f56])).
% 1.46/0.57  fof(f277,plain,(
% 1.46/0.57    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl8_5),
% 1.46/0.57    inference(resolution,[],[f262,f74])).
% 1.46/0.57  fof(f74,plain,(
% 1.46/0.57    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f28])).
% 1.46/0.57  fof(f28,plain,(
% 1.46/0.57    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.57    inference(flattening,[],[f27])).
% 1.46/0.57  fof(f27,plain,(
% 1.46/0.57    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.46/0.57    inference(ennf_transformation,[],[f4])).
% 1.46/0.57  fof(f4,axiom,(
% 1.46/0.57    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 1.46/0.57  fof(f262,plain,(
% 1.46/0.57    ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | spl8_5),
% 1.46/0.57    inference(avatar_component_clause,[],[f260])).
% 1.46/0.57  fof(f267,plain,(
% 1.46/0.57    ~spl8_5 | ~spl8_6),
% 1.46/0.57    inference(avatar_split_clause,[],[f253,f264,f260])).
% 1.46/0.57  fof(f253,plain,(
% 1.46/0.57    ~r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1)) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))),
% 1.46/0.57    inference(resolution,[],[f166,f60])).
% 1.46/0.57  fof(f60,plain,(
% 1.46/0.57    ~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))),
% 1.46/0.57    inference(cnf_transformation,[],[f38])).
% 1.46/0.57  fof(f166,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r3_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~r2_hidden(X1,a_2_2_lattice3(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f165,f53])).
% 1.46/0.57  fof(f165,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r3_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~r2_hidden(X1,a_2_2_lattice3(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f164,f54])).
% 1.46/0.57  fof(f164,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r3_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~r2_hidden(X1,a_2_2_lattice3(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f163,f55])).
% 1.46/0.57  fof(f163,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r3_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~r2_hidden(X1,a_2_2_lattice3(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f162,f56])).
% 1.46/0.57  fof(f162,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r3_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~r2_hidden(X1,a_2_2_lattice3(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.57    inference(superposition,[],[f69,f109])).
% 1.46/0.57  fof(f109,plain,(
% 1.46/0.57    ( ! [X2] : (k15_lattice3(sK0,X2) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X2))) )),
% 1.46/0.57    inference(global_subsumption,[],[f56,f108])).
% 1.46/0.57  fof(f108,plain,(
% 1.46/0.57    ( ! [X2] : (~l3_lattices(sK0) | k15_lattice3(sK0,X2) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X2))) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f107,f53])).
% 1.46/0.57  fof(f107,plain,(
% 1.46/0.57    ( ! [X2] : (~l3_lattices(sK0) | k15_lattice3(sK0,X2) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X2)) | v2_struct_0(sK0)) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f100,f54])).
% 1.46/0.57  fof(f100,plain,(
% 1.46/0.57    ( ! [X2] : (~l3_lattices(sK0) | k15_lattice3(sK0,X2) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X2)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.57    inference(resolution,[],[f55,f65])).
% 1.46/0.57  fof(f65,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~v4_lattice3(X0) | ~l3_lattices(X0) | k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f20])).
% 1.46/0.57  fof(f20,plain,(
% 1.46/0.57    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.57    inference(flattening,[],[f19])).
% 1.46/0.57  fof(f19,plain,(
% 1.46/0.57    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.46/0.57    inference(ennf_transformation,[],[f7])).
% 1.46/0.57  fof(f7,axiom,(
% 1.46/0.57    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).
% 1.46/0.57  fof(f69,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f24])).
% 1.46/0.57  % SZS output end Proof for theBenchmark
% 1.46/0.57  % (10314)------------------------------
% 1.46/0.57  % (10314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (10314)Termination reason: Refutation
% 1.46/0.57  
% 1.46/0.57  % (10314)Memory used [KB]: 11129
% 1.46/0.57  % (10314)Time elapsed: 0.146 s
% 1.46/0.57  % (10314)------------------------------
% 1.46/0.57  % (10314)------------------------------
% 1.46/0.57  % (10312)Success in time 0.206 s
%------------------------------------------------------------------------------
