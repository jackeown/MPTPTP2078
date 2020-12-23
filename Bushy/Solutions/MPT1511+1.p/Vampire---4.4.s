%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattice3__t45_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:55 EDT 2019

% Result     : Theorem 3.64s
% Output     : Refutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  261 (1096 expanded)
%              Number of leaves         :   33 ( 336 expanded)
%              Depth                    :   27
%              Number of atoms          : 1477 (7470 expanded)
%              Number of equality atoms :  100 (1785 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128706,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f183,f2436,f2442,f2447,f2452,f13015,f77856,f77886,f128703,f128705])).

fof(f128705,plain,
    ( spl13_3
    | ~ spl13_872
    | ~ spl13_918 ),
    inference(avatar_contradiction_clause,[],[f128704])).

fof(f128704,plain,
    ( $false
    | ~ spl13_3
    | ~ spl13_872
    | ~ spl13_918 ),
    inference(subsumption_resolution,[],[f182,f77890])).

fof(f77890,plain,
    ( k16_lattice3(sK0,a_2_4_lattice3(sK0,sK1)) = sK1
    | ~ spl13_872
    | ~ spl13_918 ),
    inference(subsumption_resolution,[],[f77889,f113])).

fof(f113,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,
    ( ( k16_lattice3(sK0,a_2_4_lattice3(sK0,sK1)) != sK1
      | k15_lattice3(sK0,a_2_3_lattice3(sK0,sK1)) != sK1 )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f73,f72])).

fof(f72,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) != X1
              | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) != X1 )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k16_lattice3(sK0,a_2_4_lattice3(sK0,X1)) != X1
            | k15_lattice3(sK0,a_2_3_lattice3(sK0,X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) != X1
            | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( k16_lattice3(X0,a_2_4_lattice3(X0,sK1)) != sK1
          | k15_lattice3(X0,a_2_3_lattice3(X0,sK1)) != sK1 )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) != X1
            | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) != X1
            | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
              & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t45_lattice3.p',t45_lattice3)).

fof(f77889,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k16_lattice3(sK0,a_2_4_lattice3(sK0,sK1)) = sK1
    | ~ spl13_872
    | ~ spl13_918 ),
    inference(subsumption_resolution,[],[f77887,f12928])).

fof(f12928,plain,
    ( r2_hidden(sK1,a_2_4_lattice3(sK0,sK1))
    | ~ spl13_872 ),
    inference(avatar_component_clause,[],[f12927])).

fof(f12927,plain,
    ( spl13_872
  <=> r2_hidden(sK1,a_2_4_lattice3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_872])])).

fof(f77887,plain,
    ( ~ r2_hidden(sK1,a_2_4_lattice3(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k16_lattice3(sK0,a_2_4_lattice3(sK0,sK1)) = sK1
    | ~ spl13_918 ),
    inference(resolution,[],[f14110,f1272])).

fof(f1272,plain,(
    ! [X0,X1] :
      ( ~ r3_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k16_lattice3(sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f1271,f109])).

fof(f109,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f74])).

fof(f1271,plain,(
    ! [X0,X1] :
      ( ~ r3_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k16_lattice3(sK0,X1) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1270,f110])).

fof(f110,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f74])).

fof(f1270,plain,(
    ! [X0,X1] :
      ( ~ r3_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k16_lattice3(sK0,X1) = X0
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1269,f112])).

fof(f112,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f74])).

fof(f1269,plain,(
    ! [X0,X1] :
      ( ~ r3_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | k16_lattice3(sK0,X1) = X0
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f129,f111])).

fof(f111,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f74])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k16_lattice3(X0,X2) = X1
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
              | ~ r3_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
              | ~ r3_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k16_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t45_lattice3.p',t42_lattice3)).

fof(f14110,plain,
    ( r3_lattice3(sK0,sK1,a_2_4_lattice3(sK0,sK1))
    | ~ spl13_918 ),
    inference(avatar_component_clause,[],[f14109])).

fof(f14109,plain,
    ( spl13_918
  <=> r3_lattice3(sK0,sK1,a_2_4_lattice3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_918])])).

fof(f182,plain,
    ( k16_lattice3(sK0,a_2_4_lattice3(sK0,sK1)) != sK1
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl13_3
  <=> k16_lattice3(sK0,a_2_4_lattice3(sK0,sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f128703,plain,
    ( spl13_1
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112
    | ~ spl13_114 ),
    inference(avatar_contradiction_clause,[],[f128702])).

fof(f128702,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112
    | ~ spl13_114 ),
    inference(subsumption_resolution,[],[f128701,f113])).

fof(f128701,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112
    | ~ spl13_114 ),
    inference(trivial_inequality_removal,[],[f128679])).

fof(f128679,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112
    | ~ spl13_114 ),
    inference(superposition,[],[f176,f124349])).

fof(f124349,plain,
    ( ! [X4] :
        ( k15_lattice3(sK0,a_2_3_lattice3(sK0,X4)) = X4
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112
    | ~ spl13_114 ),
    inference(subsumption_resolution,[],[f124346,f2435])).

fof(f2435,plain,
    ( ! [X6] :
        ( r2_hidden(X6,a_2_3_lattice3(sK0,X6))
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | ~ spl13_114 ),
    inference(avatar_component_clause,[],[f2434])).

fof(f2434,plain,
    ( spl13_114
  <=> ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r2_hidden(X6,a_2_3_lattice3(sK0,X6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_114])])).

fof(f124346,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,a_2_3_lattice3(sK0,X4))
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X4)) = X4
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(duplicate_literal_removal,[],[f124343])).

fof(f124343,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,a_2_3_lattice3(sK0,X4))
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X4)) = X4
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X4)) = X4
        | ~ r2_hidden(X4,a_2_3_lattice3(sK0,X4)) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(resolution,[],[f6382,f1158])).

fof(f1158,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK2(sK0,X2,X3),X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k15_lattice3(sK0,X3) = X2
      | ~ r2_hidden(X2,X3) ) ),
    inference(subsumption_resolution,[],[f1157,f109])).

fof(f1157,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k15_lattice3(sK0,X3) = X2
      | r2_hidden(sK2(sK0,X2,X3),X3)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1153,f112])).

fof(f1153,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k15_lattice3(sK0,X3) = X2
      | r2_hidden(sK2(sK0,X2,X3),X3)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1152])).

fof(f1152,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k15_lattice3(sK0,X3) = X2
      | r2_hidden(sK2(sK0,X2,X3),X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f1150,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK2(X0,X1,X2),X1)
                  & r2_hidden(sK2(X0,X1,X2),X2)
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f76,f77])).

fof(f77,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X2)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
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
    inference(rectify,[],[f75])).

fof(f75,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/lattice3__t45_lattice3.p',d17_lattice3)).

fof(f1150,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k15_lattice3(sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f1149,f109])).

fof(f1149,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k15_lattice3(sK0,X1) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1148,f110])).

fof(f1148,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k15_lattice3(sK0,X1) = X0
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1147,f112])).

fof(f1147,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | k15_lattice3(sK0,X1) = X0
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f128,f111])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ r4_lattice3(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,X2) = X1
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k15_lattice3(X0,X2) = X1
              | ~ r4_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k15_lattice3(X0,X2) = X1
              | ~ r4_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k15_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t45_lattice3.p',t41_lattice3)).

fof(f6382,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(sK2(sK0,X4,X5),a_2_3_lattice3(sK0,X4))
        | ~ r2_hidden(X4,X5)
        | k15_lattice3(sK0,X5) = X4
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(duplicate_literal_removal,[],[f6381])).

fof(f6381,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,X5)
        | k15_lattice3(sK0,X5) = X4
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(sK2(sK0,X4,X5),a_2_3_lattice3(sK0,X4)) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(resolution,[],[f4247,f1741])).

fof(f1741,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_3_lattice3(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f1740,f109])).

fof(f1740,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_3_lattice3(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1739,f110])).

fof(f1739,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_3_lattice3(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1738,f111])).

fof(f1738,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_3_lattice3(sK0,X1))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1737,f112])).

fof(f1737,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_3_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1736])).

fof(f1736,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_3_lattice3(sK0,X1))
      | ~ r2_hidden(X0,a_2_3_lattice3(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f1735,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( sK6(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_3_lattice3(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r3_lattices(X1,sK6(X0,X1,X2),X2)
            & sK6(X0,X1,X2) = X0
            & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_3_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f90,f91])).

fof(f91,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattices(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattices(X1,sK6(X0,X1,X2),X2)
        & sK6(X0,X1,X2) = X0
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r3_lattices(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_3_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f89])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r3_lattices(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_3_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t45_lattice3.p',fraenkel_a_2_3_lattice3)).

fof(f1735,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,sK6(X0,sK0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_3_lattice3(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f1734,f109])).

fof(f1734,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_3_lattice3(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_lattices(sK0,sK6(X0,sK0,X1),X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1733,f110])).

fof(f1733,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_3_lattice3(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_lattices(sK0,sK6(X0,sK0,X1),X1)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1732,f112])).

fof(f1732,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_3_lattice3(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r3_lattices(sK0,sK6(X0,sK0,X1),X1)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f153,f111])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X1)
      | ~ r2_hidden(X0,a_2_3_lattice3(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r3_lattices(X1,sK6(X0,X1,X2),X2)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f4247,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK0,sK2(sK0,X0,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | k15_lattice3(sK0,X1) = X0 )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(subsumption_resolution,[],[f4246,f1156])).

fof(f1156,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k15_lattice3(sK0,X1) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f1155,f109])).

fof(f1155,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k15_lattice3(sK0,X1) = X0
      | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1154,f112])).

fof(f1154,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k15_lattice3(sK0,X1) = X0
      | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1151])).

fof(f1151,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k15_lattice3(sK0,X1) = X0
      | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f1150,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f4246,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,sK2(sK0,X0,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | k15_lattice3(sK0,X1) = X0 )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(duplicate_literal_removal,[],[f4243])).

fof(f4243,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,sK2(sK0,X0,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = X0 )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(resolution,[],[f3373,f1150])).

fof(f3373,plain,
    ( ! [X0,X1] :
        ( r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,sK2(sK0,X0,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(subsumption_resolution,[],[f3372,f109])).

fof(f3372,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,sK2(sK0,X0,X1),X0)
        | r4_lattice3(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(subsumption_resolution,[],[f3371,f112])).

fof(f3371,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,sK2(sK0,X0,X1),X0)
        | r4_lattice3(sK0,X0,X1)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(duplicate_literal_removal,[],[f3368])).

fof(f3368,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,sK2(sK0,X0,X1),X0)
        | r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(resolution,[],[f2953,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,sK2(X0,X1,X2),X1)
      | r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f2953,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X1) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(subsumption_resolution,[],[f2952,f2417])).

fof(f2417,plain,
    ( v6_lattices(sK0)
    | ~ spl13_108 ),
    inference(avatar_component_clause,[],[f2416])).

fof(f2416,plain,
    ( spl13_108
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_108])])).

fof(f2952,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v6_lattices(sK0)
        | r1_lattices(sK0,X0,X1) )
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(subsumption_resolution,[],[f2951,f2423])).

fof(f2423,plain,
    ( v8_lattices(sK0)
    | ~ spl13_110 ),
    inference(avatar_component_clause,[],[f2422])).

fof(f2422,plain,
    ( spl13_110
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_110])])).

fof(f2951,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v8_lattices(sK0)
        | ~ v6_lattices(sK0)
        | r1_lattices(sK0,X0,X1) )
    | ~ spl13_112 ),
    inference(subsumption_resolution,[],[f2950,f2429])).

fof(f2429,plain,
    ( v9_lattices(sK0)
    | ~ spl13_112 ),
    inference(avatar_component_clause,[],[f2428])).

fof(f2428,plain,
    ( spl13_112
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_112])])).

fof(f2950,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | r1_lattices(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f2949,f112])).

fof(f2949,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | r1_lattices(sK0,X0,X1) ) ),
    inference(resolution,[],[f149,f109])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
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
    inference(nnf_transformation,[],[f65])).

fof(f65,plain,(
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
    inference(flattening,[],[f64])).

fof(f64,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/lattice3__t45_lattice3.p',redefinition_r3_lattices)).

fof(f176,plain,
    ( k15_lattice3(sK0,a_2_3_lattice3(sK0,sK1)) != sK1
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl13_1
  <=> k15_lattice3(sK0,a_2_3_lattice3(sK0,sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f77886,plain,
    ( spl13_919
    | ~ spl13_1140 ),
    inference(avatar_contradiction_clause,[],[f77885])).

fof(f77885,plain,
    ( $false
    | ~ spl13_919
    | ~ spl13_1140 ),
    inference(subsumption_resolution,[],[f72236,f17537])).

fof(f17537,plain,
    ( r2_hidden(sK1,a_2_1_lattice3(sK0,a_2_4_lattice3(sK0,sK1)))
    | ~ spl13_1140 ),
    inference(avatar_component_clause,[],[f17536])).

fof(f17536,plain,
    ( spl13_1140
  <=> r2_hidden(sK1,a_2_1_lattice3(sK0,a_2_4_lattice3(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1140])])).

fof(f72236,plain,
    ( ~ r2_hidden(sK1,a_2_1_lattice3(sK0,a_2_4_lattice3(sK0,sK1)))
    | ~ spl13_919 ),
    inference(resolution,[],[f270,f14107])).

fof(f14107,plain,
    ( ~ r3_lattice3(sK0,sK1,a_2_4_lattice3(sK0,sK1))
    | ~ spl13_919 ),
    inference(avatar_component_clause,[],[f14106])).

fof(f14106,plain,
    ( spl13_919
  <=> ~ r3_lattice3(sK0,sK1,a_2_4_lattice3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_919])])).

fof(f270,plain,(
    ! [X0,X1] :
      ( r3_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,a_2_1_lattice3(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f269,f109])).

fof(f269,plain,(
    ! [X0,X1] :
      ( r3_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,a_2_1_lattice3(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f268,f112])).

fof(f268,plain,(
    ! [X0,X1] :
      ( r3_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,a_2_1_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f267])).

fof(f267,plain,(
    ! [X0,X1] :
      ( r3_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,a_2_1_lattice3(sK0,X1))
      | ~ r2_hidden(X0,a_2_1_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f266,f160])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( sK8(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r3_lattice3(X1,sK8(X0,X1,X2),X2)
            & sK8(X0,X1,X2) = X0
            & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f98,f99])).

fof(f99,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK8(X0,X1,X2),X2)
        & sK8(X0,X1,X2) = X0
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f98,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r3_lattice3(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f97])).

fof(f97,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r3_lattice3(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t45_lattice3.p',fraenkel_a_2_1_lattice3)).

fof(f266,plain,(
    ! [X0,X1] :
      ( r3_lattice3(sK0,sK8(X0,sK0,X1),X1)
      | ~ r2_hidden(X0,a_2_1_lattice3(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f265,f112])).

fof(f265,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | r3_lattice3(sK0,sK8(X0,sK0,X1),X1) ) ),
    inference(resolution,[],[f161,f109])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | r3_lattice3(X1,sK8(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f77856,plain,
    ( ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112
    | spl13_1141 ),
    inference(avatar_contradiction_clause,[],[f77855])).

fof(f77855,plain,
    ( $false
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112
    | ~ spl13_1141 ),
    inference(subsumption_resolution,[],[f77842,f113])).

fof(f77842,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112
    | ~ spl13_1141 ),
    inference(resolution,[],[f5248,f17534])).

fof(f17534,plain,
    ( ~ r2_hidden(sK1,a_2_1_lattice3(sK0,a_2_4_lattice3(sK0,sK1)))
    | ~ spl13_1141 ),
    inference(avatar_component_clause,[],[f17533])).

fof(f17533,plain,
    ( spl13_1141
  <=> ~ r2_hidden(sK1,a_2_1_lattice3(sK0,a_2_4_lattice3(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1141])])).

fof(f5248,plain,
    ( ! [X3] :
        ( r2_hidden(X3,a_2_1_lattice3(sK0,a_2_4_lattice3(sK0,X3)))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(duplicate_literal_removal,[],[f5243])).

fof(f5243,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X3,a_2_1_lattice3(sK0,a_2_4_lattice3(sK0,X3)))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X3,a_2_1_lattice3(sK0,a_2_4_lattice3(sK0,X3))) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(resolution,[],[f4719,f645])).

fof(f645,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK0,X0,X1),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_1_lattice3(sK0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f644])).

fof(f644,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(sK3(sK0,X0,X1),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_1_lattice3(sK0,X1)) ) ),
    inference(resolution,[],[f289,f272])).

fof(f272,plain,(
    ! [X0,X1] :
      ( ~ r3_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_1_lattice3(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f271,f112])).

fof(f271,plain,(
    ! [X0,X1] :
      ( ~ r3_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r2_hidden(X0,a_2_1_lattice3(sK0,X1)) ) ),
    inference(resolution,[],[f169,f109])).

fof(f169,plain,(
    ! [X2,X3,X1] :
      ( v2_struct_0(X1)
      | ~ r3_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r2_hidden(X3,a_2_1_lattice3(X1,X2)) ) ),
    inference(equality_resolution,[],[f162])).

fof(f162,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ r3_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f289,plain,(
    ! [X0,X1] :
      ( r3_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(sK3(sK0,X0,X1),X1) ) ),
    inference(subsumption_resolution,[],[f288,f112])).

fof(f288,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK0,X0,X1),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r3_lattice3(sK0,X0,X1) ) ),
    inference(resolution,[],[f136,f109])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK3(X0,X1,X2))
                  & r2_hidden(sK3(X0,X1,X2),X2)
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f80,f81])).

fof(f81,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK3(X0,X1,X2))
        & r2_hidden(sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
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
    inference(rectify,[],[f79])).

fof(f79,plain,(
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
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/lattice3__t45_lattice3.p',d16_lattice3)).

fof(f4719,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(sK3(sK0,X5,X6),a_2_4_lattice3(sK0,X5))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | r2_hidden(X5,a_2_1_lattice3(sK0,X6)) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(duplicate_literal_removal,[],[f4718])).

fof(f4718,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(sK3(sK0,X5,X6),a_2_4_lattice3(sK0,X5))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | r2_hidden(X5,a_2_1_lattice3(sK0,X6)) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(resolution,[],[f4542,f272])).

fof(f4542,plain,
    ( ! [X2,X3] :
        ( r3_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(sK3(sK0,X2,X3),a_2_4_lattice3(sK0,X2)) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(subsumption_resolution,[],[f4540,f2006])).

fof(f2006,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f2005,f109])).

fof(f2005,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2004,f110])).

fof(f2004,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2003,f111])).

fof(f2003,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1983,f112])).

fof(f1983,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1982])).

fof(f1982,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1))
      | ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f1940,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( sK7(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r3_lattices(X1,X2,sK7(X0,X1,X2))
            & sK7(X0,X1,X2) = X0
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f94,f95])).

fof(f95,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattices(X1,X2,X4)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattices(X1,X2,sK7(X0,X1,X2))
        & sK7(X0,X1,X2) = X0
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f94,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r3_lattices(X1,X2,X4)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r3_lattices(X1,X2,X3)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t45_lattice3.p',fraenkel_a_2_4_lattice3)).

fof(f1940,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,sK0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f1939,f109])).

fof(f1939,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(sK7(X0,sK0,X1),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1938,f110])).

fof(f1938,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | m1_subset_1(sK7(X0,sK0,X1),u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1937,f112])).

fof(f1937,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | m1_subset_1(sK7(X0,sK0,X1),u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f155,f111])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X1)
      | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f4540,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,X2,X3),u1_struct_0(sK0))
        | r3_lattice3(sK0,X2,X3)
        | ~ r2_hidden(sK3(sK0,X2,X3),a_2_4_lattice3(sK0,X2)) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(duplicate_literal_removal,[],[f4537])).

fof(f4537,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,X2,X3),u1_struct_0(sK0))
        | r3_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(sK3(sK0,X2,X3),a_2_4_lattice3(sK0,X2)) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(resolution,[],[f3375,f2127])).

fof(f2127,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f2126,f109])).

fof(f2126,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2125,f110])).

fof(f2125,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2124,f111])).

fof(f2124,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2123,f112])).

fof(f2123,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f2122])).

fof(f2122,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1))
      | ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f2121,f156])).

fof(f2121,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X1,sK7(X0,sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f2120,f109])).

fof(f2120,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_lattices(sK0,X1,sK7(X0,sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2119,f110])).

fof(f2119,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_lattices(sK0,X1,sK7(X0,sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2118,f112])).

fof(f2118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_4_lattice3(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r3_lattices(sK0,X1,sK7(X0,sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f157,f111])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X1)
      | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r3_lattices(X1,X2,sK7(X0,X1,X2))
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f3375,plain,
    ( ! [X2,X3] :
        ( ~ r3_lattices(sK0,X2,sK3(sK0,X2,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,X2,X3),u1_struct_0(sK0))
        | r3_lattice3(sK0,X2,X3) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(subsumption_resolution,[],[f3374,f109])).

fof(f3374,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK3(sK0,X2,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X2,sK3(sK0,X2,X3))
        | r3_lattice3(sK0,X2,X3)
        | v2_struct_0(sK0) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(subsumption_resolution,[],[f3370,f112])).

fof(f3370,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK3(sK0,X2,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X2,sK3(sK0,X2,X3))
        | r3_lattice3(sK0,X2,X3)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(duplicate_literal_removal,[],[f3369])).

fof(f3369,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK3(sK0,X2,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X2,sK3(sK0,X2,X3))
        | r3_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(resolution,[],[f2953,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,sK3(X0,X1,X2))
      | r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f13015,plain,
    ( ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112
    | spl13_873 ),
    inference(avatar_contradiction_clause,[],[f13014])).

fof(f13014,plain,
    ( $false
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112
    | ~ spl13_873 ),
    inference(subsumption_resolution,[],[f13011,f113])).

fof(f13011,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112
    | ~ spl13_873 ),
    inference(resolution,[],[f12931,f2627])).

fof(f2627,plain,
    ( ! [X6] :
        ( r2_hidden(X6,a_2_4_lattice3(sK0,X6))
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(subsumption_resolution,[],[f2626,f109])).

fof(f2626,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r2_hidden(X6,a_2_4_lattice3(sK0,X6))
        | v2_struct_0(sK0) )
    | ~ spl13_108
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(subsumption_resolution,[],[f2625,f2417])).

fof(f2625,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r2_hidden(X6,a_2_4_lattice3(sK0,X6))
        | ~ v6_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_110
    | ~ spl13_112 ),
    inference(subsumption_resolution,[],[f2624,f2423])).

fof(f2624,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r2_hidden(X6,a_2_4_lattice3(sK0,X6))
        | ~ v8_lattices(sK0)
        | ~ v6_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_112 ),
    inference(subsumption_resolution,[],[f2623,f2429])).

fof(f2623,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r2_hidden(X6,a_2_4_lattice3(sK0,X6))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2617,f112])).

fof(f2617,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r2_hidden(X6,a_2_4_lattice3(sK0,X6))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f2614])).

fof(f2614,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r2_hidden(X6,a_2_4_lattice3(sK0,X6))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2610,f170])).

fof(f170,plain,(
    ! [X0,X1] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(condensation,[],[f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r3_lattices(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t45_lattice3.p',reflexivity_r3_lattices)).

fof(f2610,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X1,a_2_4_lattice3(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f2609,f109])).

fof(f2609,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X1,a_2_4_lattice3(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2608,f110])).

fof(f2608,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X1,a_2_4_lattice3(sK0,X0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2607,f112])).

fof(f2607,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r2_hidden(X1,a_2_4_lattice3(sK0,X0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f168,f111])).

fof(f168,plain,(
    ! [X2,X3,X1] :
      ( ~ v4_lattice3(X1)
      | ~ r3_lattices(X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r2_hidden(X3,a_2_4_lattice3(X1,X2))
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f158])).

fof(f158,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      | ~ r3_lattices(X1,X2,X3)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f12931,plain,
    ( ~ r2_hidden(sK1,a_2_4_lattice3(sK0,sK1))
    | ~ spl13_873 ),
    inference(avatar_component_clause,[],[f12930])).

fof(f12930,plain,
    ( spl13_873
  <=> ~ r2_hidden(sK1,a_2_4_lattice3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_873])])).

fof(f2452,plain,(
    spl13_113 ),
    inference(avatar_contradiction_clause,[],[f2451])).

fof(f2451,plain,
    ( $false
    | ~ spl13_113 ),
    inference(subsumption_resolution,[],[f2450,f112])).

fof(f2450,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl13_113 ),
    inference(subsumption_resolution,[],[f2449,f109])).

fof(f2449,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl13_113 ),
    inference(subsumption_resolution,[],[f2448,f110])).

fof(f2448,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl13_113 ),
    inference(resolution,[],[f2432,f127])).

fof(f127,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/lattice3__t45_lattice3.p',cc1_lattices)).

fof(f2432,plain,
    ( ~ v9_lattices(sK0)
    | ~ spl13_113 ),
    inference(avatar_component_clause,[],[f2431])).

fof(f2431,plain,
    ( spl13_113
  <=> ~ v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_113])])).

fof(f2447,plain,(
    spl13_111 ),
    inference(avatar_contradiction_clause,[],[f2446])).

fof(f2446,plain,
    ( $false
    | ~ spl13_111 ),
    inference(subsumption_resolution,[],[f2445,f112])).

fof(f2445,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl13_111 ),
    inference(subsumption_resolution,[],[f2444,f109])).

fof(f2444,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl13_111 ),
    inference(subsumption_resolution,[],[f2443,f110])).

fof(f2443,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl13_111 ),
    inference(resolution,[],[f2426,f126])).

fof(f126,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2426,plain,
    ( ~ v8_lattices(sK0)
    | ~ spl13_111 ),
    inference(avatar_component_clause,[],[f2425])).

fof(f2425,plain,
    ( spl13_111
  <=> ~ v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_111])])).

fof(f2442,plain,(
    spl13_109 ),
    inference(avatar_contradiction_clause,[],[f2441])).

fof(f2441,plain,
    ( $false
    | ~ spl13_109 ),
    inference(subsumption_resolution,[],[f2440,f112])).

fof(f2440,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl13_109 ),
    inference(subsumption_resolution,[],[f2439,f109])).

fof(f2439,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl13_109 ),
    inference(subsumption_resolution,[],[f2438,f110])).

fof(f2438,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl13_109 ),
    inference(resolution,[],[f2420,f124])).

fof(f124,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2420,plain,
    ( ~ v6_lattices(sK0)
    | ~ spl13_109 ),
    inference(avatar_component_clause,[],[f2419])).

fof(f2419,plain,
    ( spl13_109
  <=> ~ v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_109])])).

fof(f2436,plain,
    ( ~ spl13_109
    | ~ spl13_111
    | ~ spl13_113
    | spl13_114 ),
    inference(avatar_split_clause,[],[f2414,f2434,f2431,f2425,f2419])).

fof(f2414,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r2_hidden(X6,a_2_3_lattice3(sK0,X6))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f2413,f109])).

fof(f2413,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r2_hidden(X6,a_2_3_lattice3(sK0,X6))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2407,f112])).

fof(f2407,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r2_hidden(X6,a_2_3_lattice3(sK0,X6))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f2404])).

fof(f2404,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r2_hidden(X6,a_2_3_lattice3(sK0,X6))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2400,f170])).

fof(f2400,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_3_lattice3(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f2399,f109])).

fof(f2399,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_3_lattice3(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2398,f110])).

fof(f2398,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_3_lattice3(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2397,f112])).

fof(f2397,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r2_hidden(X0,a_2_3_lattice3(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f167,f111])).

fof(f167,plain,(
    ! [X2,X3,X1] :
      ( ~ v4_lattice3(X1)
      | ~ r3_lattices(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r2_hidden(X3,a_2_3_lattice3(X1,X2))
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f154])).

fof(f154,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
      | ~ r3_lattices(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f183,plain,
    ( ~ spl13_1
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f114,f181,f175])).

fof(f114,plain,
    ( k16_lattice3(sK0,a_2_4_lattice3(sK0,sK1)) != sK1
    | k15_lattice3(sK0,a_2_3_lattice3(sK0,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f74])).
%------------------------------------------------------------------------------
