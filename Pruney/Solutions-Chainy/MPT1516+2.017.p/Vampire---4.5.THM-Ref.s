%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:51 EST 2020

% Result     : Theorem 4.52s
% Output     : Refutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :  266 (1047 expanded)
%              Number of leaves         :   38 ( 272 expanded)
%              Depth                    :   24
%              Number of atoms          : 1418 (7756 expanded)
%              Number of equality atoms :  176 ( 890 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11748,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f158,f178,f365,f740,f2500,f2540,f2567,f2583,f2585,f4913,f5128,f9994,f10703,f11718])).

fof(f11718,plain,
    ( ~ spl9_6
    | ~ spl9_7
    | ~ spl9_337
    | spl9_377 ),
    inference(avatar_contradiction_clause,[],[f11717])).

fof(f11717,plain,
    ( $false
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_337
    | spl9_377 ),
    inference(subsumption_resolution,[],[f11716,f10664])).

fof(f10664,plain,
    ( ~ r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | spl9_377 ),
    inference(avatar_component_clause,[],[f10663])).

fof(f10663,plain,
    ( spl9_377
  <=> r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_377])])).

fof(f11716,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_337 ),
    inference(subsumption_resolution,[],[f11712,f356])).

fof(f356,plain,
    ( m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl9_6
  <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f11712,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ spl9_7
    | ~ spl9_337 ),
    inference(resolution,[],[f10403,f10167])).

fof(f10167,plain,
    ( r2_hidden(k15_lattice3(sK0,k1_xboole_0),a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))))
    | ~ spl9_7
    | ~ spl9_337 ),
    inference(subsumption_resolution,[],[f10072,f9978])).

fof(f9978,plain,
    ( m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl9_337 ),
    inference(avatar_component_clause,[],[f9977])).

fof(f9977,plain,
    ( spl9_337
  <=> m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_337])])).

fof(f10072,plain,
    ( r2_hidden(k15_lattice3(sK0,k1_xboole_0),a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))))
    | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl9_7
    | ~ spl9_337 ),
    inference(superposition,[],[f360,f10030])).

fof(f10030,plain,
    ( sK2(sK0,k15_lattice3(sK0,k1_xboole_0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))))
    | ~ spl9_337 ),
    inference(subsumption_resolution,[],[f10029,f81])).

fof(f81,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
          | ~ l3_lattices(X0)
          | ~ v13_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
        | ~ l3_lattices(sK0)
        | ~ v13_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
          & l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).

fof(f10029,plain,
    ( sK2(sK0,k15_lattice3(sK0,k1_xboole_0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))))
    | v2_struct_0(sK0)
    | ~ spl9_337 ),
    inference(subsumption_resolution,[],[f10028,f82])).

fof(f82,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f10028,plain,
    ( sK2(sK0,k15_lattice3(sK0,k1_xboole_0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_337 ),
    inference(subsumption_resolution,[],[f10027,f83])).

fof(f83,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f10027,plain,
    ( sK2(sK0,k15_lattice3(sK0,k1_xboole_0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_337 ),
    inference(subsumption_resolution,[],[f10005,f84])).

fof(f84,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f10005,plain,
    ( sK2(sK0,k15_lattice3(sK0,k1_xboole_0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_337 ),
    inference(resolution,[],[f9978,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).

fof(f360,plain,
    ( ! [X0] :
        ( r2_hidden(k15_lattice3(sK0,k1_xboole_0),a_2_3_lattice3(sK0,k15_lattice3(sK0,X0)))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl9_7
  <=> ! [X0] :
        ( r2_hidden(k15_lattice3(sK0,k1_xboole_0),a_2_3_lattice3(sK0,k15_lattice3(sK0,X0)))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f10403,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) )
    | ~ spl9_337 ),
    inference(subsumption_resolution,[],[f10402,f81])).

fof(f10402,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
        | v2_struct_0(sK0) )
    | ~ spl9_337 ),
    inference(subsumption_resolution,[],[f10401,f84])).

fof(f10401,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_337 ),
    inference(subsumption_resolution,[],[f10399,f9978])).

fof(f10399,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
        | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_337 ),
    inference(resolution,[],[f10309,f119])).

fof(f119,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r4_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_lattices(X0,X4,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK7(X0,X1,X2),X1)
                  & r2_hidden(sK7(X0,X1,X2),X2)
                  & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f74,f75])).

fof(f75,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK7(X0,X1,X2),X1)
        & r2_hidden(sK7(X0,X1,X2),X2)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
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
    inference(rectify,[],[f73])).

fof(f73,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

fof(f10309,plain,
    ( r4_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))))
    | ~ spl9_337 ),
    inference(subsumption_resolution,[],[f10308,f81])).

fof(f10308,plain,
    ( r4_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))))
    | v2_struct_0(sK0)
    | ~ spl9_337 ),
    inference(subsumption_resolution,[],[f10307,f82])).

fof(f10307,plain,
    ( r4_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_337 ),
    inference(subsumption_resolution,[],[f10306,f83])).

fof(f10306,plain,
    ( r4_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_337 ),
    inference(subsumption_resolution,[],[f10305,f84])).

fof(f10305,plain,
    ( r4_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_337 ),
    inference(subsumption_resolution,[],[f10143,f9978])).

fof(f10143,plain,
    ( ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | r4_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_337 ),
    inference(superposition,[],[f137,f10030])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X2,X1)
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK6(X0,X1,X2))
                & r4_lattice3(X0,sK6(X0,X1,X2),X1)
                & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f70,f71])).

fof(f71,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK6(X0,X1,X2))
        & r4_lattice3(X0,sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( k15_lattice3(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r4_lattice3(X0,X3,X1)
                     => r1_lattices(X0,X2,X3) ) )
                & r4_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

fof(f10703,plain,
    ( spl9_3
    | ~ spl9_6
    | ~ spl9_66
    | ~ spl9_337
    | ~ spl9_377 ),
    inference(avatar_contradiction_clause,[],[f10702])).

fof(f10702,plain,
    ( $false
    | spl9_3
    | ~ spl9_6
    | ~ spl9_66
    | ~ spl9_337
    | ~ spl9_377 ),
    inference(subsumption_resolution,[],[f10701,f81])).

fof(f10701,plain,
    ( v2_struct_0(sK0)
    | spl9_3
    | ~ spl9_6
    | ~ spl9_66
    | ~ spl9_337
    | ~ spl9_377 ),
    inference(subsumption_resolution,[],[f10700,f165])).

fof(f165,plain,(
    v8_lattices(sK0) ),
    inference(global_subsumption,[],[f84,f164])).

fof(f164,plain,
    ( v8_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f160,f81])).

fof(f160,plain,
    ( v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f82,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,plain,(
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
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f10700,plain,
    ( ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_3
    | ~ spl9_6
    | ~ spl9_66
    | ~ spl9_337
    | ~ spl9_377 ),
    inference(subsumption_resolution,[],[f10699,f167])).

fof(f167,plain,(
    v9_lattices(sK0) ),
    inference(global_subsumption,[],[f84,f166])).

fof(f166,plain,
    ( v9_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f161,f81])).

fof(f161,plain,
    ( v9_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f82,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10699,plain,
    ( ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_3
    | ~ spl9_6
    | ~ spl9_66
    | ~ spl9_337
    | ~ spl9_377 ),
    inference(subsumption_resolution,[],[f10698,f84])).

fof(f10698,plain,
    ( ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_3
    | ~ spl9_6
    | ~ spl9_66
    | ~ spl9_337
    | ~ spl9_377 ),
    inference(subsumption_resolution,[],[f10697,f356])).

fof(f10697,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_3
    | ~ spl9_6
    | ~ spl9_66
    | ~ spl9_337
    | ~ spl9_377 ),
    inference(subsumption_resolution,[],[f10696,f9978])).

fof(f10696,plain,
    ( ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_3
    | ~ spl9_6
    | ~ spl9_66
    | ~ spl9_377 ),
    inference(subsumption_resolution,[],[f10695,f9970])).

fof(f9970,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | spl9_3
    | ~ spl9_6
    | ~ spl9_66 ),
    inference(subsumption_resolution,[],[f9969,f81])).

fof(f9969,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | v2_struct_0(sK0)
    | spl9_3
    | ~ spl9_6
    | ~ spl9_66 ),
    inference(subsumption_resolution,[],[f9968,f176])).

fof(f176,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f84,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f9968,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_3
    | ~ spl9_6
    | ~ spl9_66 ),
    inference(subsumption_resolution,[],[f9967,f356])).

fof(f9967,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_3
    | ~ spl9_6
    | ~ spl9_66 ),
    inference(subsumption_resolution,[],[f9966,f149])).

fof(f149,plain,
    ( ~ v13_lattices(sK0)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl9_3
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f9966,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | v13_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_6
    | ~ spl9_66 ),
    inference(duplicate_literal_removal,[],[f9964])).

fof(f9964,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | v13_lattices(sK0)
    | k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_6
    | ~ spl9_66 ),
    inference(superposition,[],[f103,f9720])).

fof(f9720,plain,
    ( k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),k15_lattice3(sK0,k1_xboole_0)) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ spl9_6
    | ~ spl9_66 ),
    inference(resolution,[],[f2566,f356])).

fof(f2566,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_lattices(sK0,sK2(sK0,X2),k15_lattice3(sK0,k1_xboole_0)) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2)) )
    | ~ spl9_66 ),
    inference(avatar_component_clause,[],[f2565])).

fof(f2565,plain,
    ( spl9_66
  <=> ! [X2] :
        ( k2_lattices(sK0,sK2(sK0,X2),k15_lattice3(sK0,k1_xboole_0)) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k2_lattices(X0,sK2(X0,X1),X1) != X1
      | v13_lattices(X0)
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( ! [X4] :
                ( ( sK3(X0) = k2_lattices(X0,X4,sK3(X0))
                  & sK3(X0) = k2_lattices(X0,sK3(X0),X4) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f59,f61,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( k2_lattices(X0,X4,X3) = X3
                & k2_lattices(X0,X3,X4) = X3 )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ( sK3(X0) = k2_lattices(X0,X4,sK3(X0))
              & sK3(X0) = k2_lattices(X0,sK3(X0),X4) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( ( k2_lattices(X0,X4,X3) = X3
                    & k2_lattices(X0,X3,X4) = X3 )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).

fof(f10695,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_377 ),
    inference(resolution,[],[f10665,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) = X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k2_lattices(X0,X1,X2) != X1 )
                & ( k2_lattices(X0,X1,X2) = X1
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

fof(f10665,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ spl9_377 ),
    inference(avatar_component_clause,[],[f10663])).

fof(f9994,plain,
    ( spl9_3
    | ~ spl9_6
    | spl9_337 ),
    inference(avatar_contradiction_clause,[],[f9993])).

fof(f9993,plain,
    ( $false
    | spl9_3
    | ~ spl9_6
    | spl9_337 ),
    inference(subsumption_resolution,[],[f9992,f81])).

fof(f9992,plain,
    ( v2_struct_0(sK0)
    | spl9_3
    | ~ spl9_6
    | spl9_337 ),
    inference(subsumption_resolution,[],[f9991,f176])).

fof(f9991,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_3
    | ~ spl9_6
    | spl9_337 ),
    inference(subsumption_resolution,[],[f9990,f356])).

fof(f9990,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_3
    | spl9_337 ),
    inference(subsumption_resolution,[],[f9989,f149])).

fof(f9989,plain,
    ( v13_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_337 ),
    inference(resolution,[],[f9979,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f9979,plain,
    ( ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl9_337 ),
    inference(avatar_component_clause,[],[f9977])).

fof(f5128,plain,
    ( spl9_5
    | ~ spl9_6
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_59 ),
    inference(avatar_contradiction_clause,[],[f5127])).

fof(f5127,plain,
    ( $false
    | spl9_5
    | ~ spl9_6
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_59 ),
    inference(subsumption_resolution,[],[f5123,f157])).

fof(f157,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl9_5
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f5123,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | ~ spl9_6
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_59 ),
    inference(backward_demodulation,[],[f4417,f4840])).

fof(f4840,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl9_6
    | ~ spl9_59 ),
    inference(resolution,[],[f2499,f356])).

fof(f2499,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0)) )
    | ~ spl9_59 ),
    inference(avatar_component_clause,[],[f2498])).

fof(f2498,plain,
    ( spl9_59
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f4417,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl9_6
    | ~ spl9_12
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f4416,f81])).

fof(f4416,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_6
    | ~ spl9_12
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f4415,f165])).

fof(f4415,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_6
    | ~ spl9_12
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f4414,f167])).

fof(f4414,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_6
    | ~ spl9_12
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f4413,f84])).

fof(f4413,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_6
    | ~ spl9_12
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f4412,f356])).

fof(f4412,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_12
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f4411,f726])).

fof(f726,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f725])).

fof(f725,plain,
    ( spl9_12
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f4411,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_13 ),
    inference(resolution,[],[f731,f92])).

fof(f731,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f729])).

fof(f729,plain,
    ( spl9_13
  <=> r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f4913,plain,(
    ~ spl9_1 ),
    inference(avatar_contradiction_clause,[],[f4912])).

fof(f4912,plain,
    ( $false
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f141,f81])).

fof(f141,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl9_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f2585,plain,
    ( spl9_13
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f1351,f725,f359,f355,f729])).

fof(f1351,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl9_7
    | ~ spl9_12 ),
    inference(resolution,[],[f885,f827])).

fof(f827,plain,
    ( r2_hidden(k15_lattice3(sK0,k1_xboole_0),a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ spl9_7
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f810,f726])).

fof(f810,plain,
    ( r2_hidden(k15_lattice3(sK0,k1_xboole_0),a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl9_7
    | ~ spl9_12 ),
    inference(superposition,[],[f360,f780])).

fof(f780,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f779,f81])).

fof(f779,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f778,f82])).

fof(f778,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f777,f83])).

fof(f777,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f770,f84])).

fof(f770,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_12 ),
    inference(resolution,[],[f726,f110])).

fof(f885,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X0,k5_lattices(sK0)) )
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f884,f81])).

fof(f884,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X0,k5_lattices(sK0))
        | v2_struct_0(sK0) )
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f883,f84])).

fof(f883,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X0,k5_lattices(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f881,f726])).

fof(f881,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X0,k5_lattices(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_12 ),
    inference(resolution,[],[f841,f119])).

fof(f841,plain,
    ( r4_lattice3(sK0,k5_lattices(sK0),a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f840,f81])).

fof(f840,plain,
    ( r4_lattice3(sK0,k5_lattices(sK0),a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f839,f82])).

fof(f839,plain,
    ( r4_lattice3(sK0,k5_lattices(sK0),a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f838,f83])).

fof(f838,plain,
    ( r4_lattice3(sK0,k5_lattices(sK0),a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f837,f84])).

fof(f837,plain,
    ( r4_lattice3(sK0,k5_lattices(sK0),a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f814,f726])).

fof(f814,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | r4_lattice3(sK0,k5_lattices(sK0),a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_12 ),
    inference(superposition,[],[f137,f780])).

fof(f2583,plain,
    ( ~ spl9_6
    | spl9_7 ),
    inference(avatar_split_clause,[],[f1910,f359,f355])).

fof(f1910,plain,(
    ! [X0] :
      ( r2_hidden(k15_lattice3(sK0,k1_xboole_0),a_2_3_lattice3(sK0,k15_lattice3(sK0,X0)))
      | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f968,f86])).

fof(f86,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f968,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,a_2_5_lattice3(sK0,a_2_5_lattice3(sK0,a_2_5_lattice3(sK0,X0))))
      | r2_hidden(k15_lattice3(sK0,X1),a_2_3_lattice3(sK0,k15_lattice3(sK0,X0)))
      | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f273,f172])).

fof(f172,plain,(
    ! [X0] : k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0)) ),
    inference(global_subsumption,[],[f84,f171])).

fof(f171,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f170,f81])).

fof(f170,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f168,f82])).

fof(f168,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f83,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattice3)).

fof(f273,plain,(
    ! [X0,X1] :
      ( r2_hidden(k15_lattice3(sK0,X0),a_2_3_lattice3(sK0,k15_lattice3(sK0,X1)))
      | ~ r1_tarski(X0,a_2_5_lattice3(sK0,a_2_5_lattice3(sK0,X1)))
      | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f272,f81])).

fof(f272,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,a_2_5_lattice3(sK0,a_2_5_lattice3(sK0,X1)))
      | r2_hidden(k15_lattice3(sK0,X0),a_2_3_lattice3(sK0,k15_lattice3(sK0,X1)))
      | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f271,f82])).

fof(f271,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,a_2_5_lattice3(sK0,a_2_5_lattice3(sK0,X1)))
      | r2_hidden(k15_lattice3(sK0,X0),a_2_3_lattice3(sK0,k15_lattice3(sK0,X1)))
      | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f270,f83])).

fof(f270,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,a_2_5_lattice3(sK0,a_2_5_lattice3(sK0,X1)))
      | r2_hidden(k15_lattice3(sK0,X0),a_2_3_lattice3(sK0,k15_lattice3(sK0,X1)))
      | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f267,f84])).

fof(f267,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,a_2_5_lattice3(sK0,a_2_5_lattice3(sK0,X1)))
      | r2_hidden(k15_lattice3(sK0,X0),a_2_3_lattice3(sK0,k15_lattice3(sK0,X1)))
      | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f212,f132])).

fof(f132,plain,(
    ! [X2,X3,X1] :
      ( ~ r3_lattices(X1,X3,X2)
      | r2_hidden(X3,a_2_3_lattice3(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
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
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattices(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r3_lattices(X1,sK8(X0,X1,X2),X2)
            & sK8(X0,X1,X2) = X0
            & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_3_lattice3(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f78,f79])).

fof(f79,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattices(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattices(X1,sK8(X0,X1,X2),X2)
        & sK8(X0,X1,X2) = X0
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
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
    inference(rectify,[],[f77])).

fof(f77,plain,(
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
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_3_lattice3)).

fof(f212,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X0))
      | ~ r1_tarski(X1,a_2_5_lattice3(sK0,a_2_5_lattice3(sK0,X0))) ) ),
    inference(superposition,[],[f195,f172])).

fof(f195,plain,(
    ! [X4,X5] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X5),k15_lattice3(sK0,X4))
      | ~ r1_tarski(X5,a_2_5_lattice3(sK0,X4)) ) ),
    inference(subsumption_resolution,[],[f194,f81])).

fof(f194,plain,(
    ! [X4,X5] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X5),k15_lattice3(sK0,X4))
      | ~ r1_tarski(X5,a_2_5_lattice3(sK0,X4))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f193,f82])).

fof(f193,plain,(
    ! [X4,X5] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X5),k15_lattice3(sK0,X4))
      | ~ r1_tarski(X5,a_2_5_lattice3(sK0,X4))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f192,f83])).

fof(f192,plain,(
    ! [X4,X5] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X5),k15_lattice3(sK0,X4))
      | ~ r1_tarski(X5,a_2_5_lattice3(sK0,X4))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f182,f84])).

fof(f182,plain,(
    ! [X4,X5] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X5),k15_lattice3(sK0,X4))
      | ~ r1_tarski(X5,a_2_5_lattice3(sK0,X4))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f112,f172])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_lattice3)).

fof(f2567,plain,
    ( spl9_3
    | spl9_66
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f2512,f355,f2565,f147])).

fof(f2512,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,sK2(sK0,X2),k15_lattice3(sK0,k1_xboole_0)) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2))
        | v13_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f2511,f81])).

fof(f2511,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,sK2(sK0,X2),k15_lattice3(sK0,k1_xboole_0)) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2))
        | v13_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f696,f176])).

fof(f696,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,sK2(sK0,X2),k15_lattice3(sK0,k1_xboole_0)) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2))
        | v13_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_6 ),
    inference(resolution,[],[f400,f102])).

fof(f400,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X2) = k2_lattices(sK0,X2,k15_lattice3(sK0,k1_xboole_0)) )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f399,f81])).

fof(f399,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X2) = k2_lattices(sK0,X2,k15_lattice3(sK0,k1_xboole_0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f398,f176])).

fof(f398,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X2) = k2_lattices(sK0,X2,k15_lattice3(sK0,k1_xboole_0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f385,f163])).

fof(f163,plain,(
    v6_lattices(sK0) ),
    inference(global_subsumption,[],[f84,f162])).

fof(f162,plain,
    ( v6_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f159,f81])).

fof(f159,plain,
    ( v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f82,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f385,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X2) = k2_lattices(sK0,X2,k15_lattice3(sK0,k1_xboole_0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v6_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_6 ),
    inference(resolution,[],[f356,f104])).

fof(f104,plain,(
    ! [X4,X0,X3] :
      ( ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f64,f66,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

% (30155)Time limit reached!
% (30155)------------------------------
% (30155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f66,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).

fof(f2540,plain,(
    spl9_4 ),
    inference(avatar_contradiction_clause,[],[f2539])).

fof(f2539,plain,
    ( $false
    | spl9_4 ),
    inference(subsumption_resolution,[],[f153,f84])).

fof(f153,plain,
    ( ~ l3_lattices(sK0)
    | spl9_4 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl9_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f2500,plain,
    ( ~ spl9_3
    | spl9_59
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f2496,f725,f2498,f147])).

fof(f2496,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0))
        | ~ v13_lattices(sK0) )
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f2495,f81])).

fof(f2495,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0))
        | ~ v13_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f764,f176])).

fof(f764,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0))
        | ~ v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_12 ),
    inference(resolution,[],[f726,f128])).

fof(f128,plain,(
    ! [X0,X3] :
      ( ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

fof(f740,plain,(
    spl9_12 ),
    inference(avatar_contradiction_clause,[],[f739])).

fof(f739,plain,
    ( $false
    | spl9_12 ),
    inference(subsumption_resolution,[],[f738,f81])).

fof(f738,plain,
    ( v2_struct_0(sK0)
    | spl9_12 ),
    inference(subsumption_resolution,[],[f737,f176])).

fof(f737,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_12 ),
    inference(resolution,[],[f727,f94])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f727,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl9_12 ),
    inference(avatar_component_clause,[],[f725])).

fof(f365,plain,(
    spl9_6 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | spl9_6 ),
    inference(subsumption_resolution,[],[f363,f81])).

fof(f363,plain,
    ( v2_struct_0(sK0)
    | spl9_6 ),
    inference(subsumption_resolution,[],[f362,f84])).

fof(f362,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_6 ),
    inference(resolution,[],[f357,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f357,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl9_6 ),
    inference(avatar_component_clause,[],[f355])).

fof(f178,plain,(
    spl9_2 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl9_2 ),
    inference(subsumption_resolution,[],[f145,f82])).

fof(f145,plain,
    ( ~ v10_lattices(sK0)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl9_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f158,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f85,f155,f151,f147,f143,f139])).

fof(f85,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:43:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.48  % (30143)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (30155)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (30146)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  % (30147)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.49  % (30144)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (30147)Refutation not found, incomplete strategy% (30147)------------------------------
% 0.20/0.49  % (30147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (30142)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (30147)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (30147)Memory used [KB]: 10490
% 0.20/0.49  % (30147)Time elapsed: 0.005 s
% 0.20/0.49  % (30147)------------------------------
% 0.20/0.49  % (30147)------------------------------
% 0.20/0.50  % (30166)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.50  % (30160)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (30161)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.50  % (30149)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (30145)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (30152)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (30165)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.51  % (30158)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.23/0.51  % (30164)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.23/0.51  % (30150)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.23/0.52  % (30162)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.23/0.52  % (30153)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.23/0.52  % (30163)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.23/0.52  % (30156)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.23/0.52  % (30159)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.23/0.53  % (30148)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.23/0.53  % (30157)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.23/0.53  % (30141)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.23/0.53  % (30151)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.42/0.54  % (30154)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.42/0.55  % (30141)Refutation not found, incomplete strategy% (30141)------------------------------
% 1.42/0.55  % (30141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (30141)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (30141)Memory used [KB]: 10746
% 1.42/0.55  % (30141)Time elapsed: 0.126 s
% 1.42/0.55  % (30141)------------------------------
% 1.42/0.55  % (30141)------------------------------
% 1.42/0.62  % (30150)Refutation not found, incomplete strategy% (30150)------------------------------
% 1.42/0.62  % (30150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.63  % (30150)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.63  
% 1.42/0.63  % (30150)Memory used [KB]: 6140
% 1.42/0.63  % (30150)Time elapsed: 0.222 s
% 1.42/0.63  % (30150)------------------------------
% 1.42/0.63  % (30150)------------------------------
% 3.80/0.90  % (30154)Time limit reached!
% 3.80/0.90  % (30154)------------------------------
% 3.80/0.90  % (30154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.80/0.90  % (30154)Termination reason: Time limit
% 3.80/0.90  % (30154)Termination phase: Saturation
% 3.80/0.90  
% 3.80/0.90  % (30154)Memory used [KB]: 7419
% 3.80/0.90  % (30154)Time elapsed: 0.500 s
% 3.80/0.90  % (30154)------------------------------
% 3.80/0.90  % (30154)------------------------------
% 4.52/0.95  % (30142)Refutation found. Thanks to Tanya!
% 4.52/0.95  % SZS status Theorem for theBenchmark
% 4.52/0.95  % SZS output start Proof for theBenchmark
% 4.52/0.95  fof(f11748,plain,(
% 4.52/0.95    $false),
% 4.52/0.95    inference(avatar_sat_refutation,[],[f158,f178,f365,f740,f2500,f2540,f2567,f2583,f2585,f4913,f5128,f9994,f10703,f11718])).
% 4.52/0.95  fof(f11718,plain,(
% 4.52/0.95    ~spl9_6 | ~spl9_7 | ~spl9_337 | spl9_377),
% 4.52/0.95    inference(avatar_contradiction_clause,[],[f11717])).
% 4.52/0.95  fof(f11717,plain,(
% 4.52/0.95    $false | (~spl9_6 | ~spl9_7 | ~spl9_337 | spl9_377)),
% 4.52/0.95    inference(subsumption_resolution,[],[f11716,f10664])).
% 4.52/0.95  fof(f10664,plain,(
% 4.52/0.95    ~r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | spl9_377),
% 4.52/0.95    inference(avatar_component_clause,[],[f10663])).
% 4.52/0.95  fof(f10663,plain,(
% 4.52/0.95    spl9_377 <=> r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))),
% 4.52/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_377])])).
% 4.52/0.95  fof(f11716,plain,(
% 4.52/0.95    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | (~spl9_6 | ~spl9_7 | ~spl9_337)),
% 4.52/0.95    inference(subsumption_resolution,[],[f11712,f356])).
% 4.52/0.95  fof(f356,plain,(
% 4.52/0.95    m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~spl9_6),
% 4.52/0.95    inference(avatar_component_clause,[],[f355])).
% 4.52/0.95  fof(f355,plain,(
% 4.52/0.95    spl9_6 <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))),
% 4.52/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 4.52/0.95  fof(f11712,plain,(
% 4.52/0.95    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | (~spl9_7 | ~spl9_337)),
% 4.52/0.95    inference(resolution,[],[f10403,f10167])).
% 4.52/0.95  fof(f10167,plain,(
% 4.52/0.95    r2_hidden(k15_lattice3(sK0,k1_xboole_0),a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))) | (~spl9_7 | ~spl9_337)),
% 4.52/0.95    inference(subsumption_resolution,[],[f10072,f9978])).
% 4.52/0.95  fof(f9978,plain,(
% 4.52/0.95    m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | ~spl9_337),
% 4.52/0.95    inference(avatar_component_clause,[],[f9977])).
% 4.52/0.95  fof(f9977,plain,(
% 4.52/0.95    spl9_337 <=> m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))),
% 4.52/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_337])])).
% 4.52/0.95  fof(f10072,plain,(
% 4.52/0.95    r2_hidden(k15_lattice3(sK0,k1_xboole_0),a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))) | ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (~spl9_7 | ~spl9_337)),
% 4.52/0.95    inference(superposition,[],[f360,f10030])).
% 4.52/0.95  fof(f10030,plain,(
% 4.52/0.95    sK2(sK0,k15_lattice3(sK0,k1_xboole_0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))) | ~spl9_337),
% 4.52/0.95    inference(subsumption_resolution,[],[f10029,f81])).
% 4.52/0.95  fof(f81,plain,(
% 4.52/0.95    ~v2_struct_0(sK0)),
% 4.52/0.95    inference(cnf_transformation,[],[f52])).
% 4.52/0.95  fof(f52,plain,(
% 4.52/0.95    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 4.52/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f51])).
% 4.52/0.95  fof(f51,plain,(
% 4.52/0.95    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 4.52/0.95    introduced(choice_axiom,[])).
% 4.52/0.95  fof(f23,plain,(
% 4.52/0.95    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 4.52/0.95    inference(flattening,[],[f22])).
% 4.52/0.95  fof(f22,plain,(
% 4.52/0.95    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 4.52/0.95    inference(ennf_transformation,[],[f17])).
% 4.52/0.95  fof(f17,negated_conjecture,(
% 4.52/0.95    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 4.52/0.95    inference(negated_conjecture,[],[f16])).
% 4.52/0.95  fof(f16,conjecture,(
% 4.52/0.95    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 4.52/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).
% 4.52/0.95  fof(f10029,plain,(
% 4.52/0.95    sK2(sK0,k15_lattice3(sK0,k1_xboole_0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))) | v2_struct_0(sK0) | ~spl9_337),
% 4.52/0.95    inference(subsumption_resolution,[],[f10028,f82])).
% 4.52/0.95  fof(f82,plain,(
% 4.52/0.95    v10_lattices(sK0)),
% 4.52/0.95    inference(cnf_transformation,[],[f52])).
% 4.52/0.95  fof(f10028,plain,(
% 4.52/0.95    sK2(sK0,k15_lattice3(sK0,k1_xboole_0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl9_337),
% 4.52/0.95    inference(subsumption_resolution,[],[f10027,f83])).
% 4.52/0.95  fof(f83,plain,(
% 4.52/0.95    v4_lattice3(sK0)),
% 4.52/0.95    inference(cnf_transformation,[],[f52])).
% 4.52/0.95  fof(f10027,plain,(
% 4.52/0.95    sK2(sK0,k15_lattice3(sK0,k1_xboole_0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl9_337),
% 4.52/0.95    inference(subsumption_resolution,[],[f10005,f84])).
% 4.52/0.95  fof(f84,plain,(
% 4.52/0.95    l3_lattices(sK0)),
% 4.52/0.95    inference(cnf_transformation,[],[f52])).
% 4.52/0.95  fof(f10005,plain,(
% 4.52/0.95    sK2(sK0,k15_lattice3(sK0,k1_xboole_0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl9_337),
% 4.52/0.95    inference(resolution,[],[f9978,f110])).
% 4.52/0.95  fof(f110,plain,(
% 4.52/0.95    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 4.52/0.95    inference(cnf_transformation,[],[f40])).
% 4.52/0.95  fof(f40,plain,(
% 4.52/0.95    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(flattening,[],[f39])).
% 4.52/0.95  fof(f39,plain,(
% 4.52/0.95    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 4.52/0.95    inference(ennf_transformation,[],[f13])).
% 4.52/0.95  fof(f13,axiom,(
% 4.52/0.95    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1)))),
% 4.52/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).
% 4.52/0.95  fof(f360,plain,(
% 4.52/0.95    ( ! [X0] : (r2_hidden(k15_lattice3(sK0,k1_xboole_0),a_2_3_lattice3(sK0,k15_lattice3(sK0,X0))) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) ) | ~spl9_7),
% 4.52/0.95    inference(avatar_component_clause,[],[f359])).
% 4.52/0.95  fof(f359,plain,(
% 4.52/0.95    spl9_7 <=> ! [X0] : (r2_hidden(k15_lattice3(sK0,k1_xboole_0),a_2_3_lattice3(sK0,k15_lattice3(sK0,X0))) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)))),
% 4.52/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 4.52/0.95  fof(f10403,plain,(
% 4.52/0.95    ( ! [X0] : (~r2_hidden(X0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))) ) | ~spl9_337),
% 4.52/0.95    inference(subsumption_resolution,[],[f10402,f81])).
% 4.52/0.95  fof(f10402,plain,(
% 4.52/0.95    ( ! [X0] : (~r2_hidden(X0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | v2_struct_0(sK0)) ) | ~spl9_337),
% 4.52/0.95    inference(subsumption_resolution,[],[f10401,f84])).
% 4.52/0.95  fof(f10401,plain,(
% 4.52/0.95    ( ! [X0] : (~r2_hidden(X0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_337),
% 4.52/0.95    inference(subsumption_resolution,[],[f10399,f9978])).
% 4.52/0.95  fof(f10399,plain,(
% 4.52/0.95    ( ! [X0] : (~r2_hidden(X0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_337),
% 4.52/0.95    inference(resolution,[],[f10309,f119])).
% 4.52/0.95  fof(f119,plain,(
% 4.52/0.95    ( ! [X4,X2,X0,X1] : (~r4_lattice3(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_lattices(X0,X4,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.52/0.95    inference(cnf_transformation,[],[f76])).
% 4.52/0.95  fof(f76,plain,(
% 4.52/0.95    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X2) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f74,f75])).
% 4.52/0.95  fof(f75,plain,(
% 4.52/0.95    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X2) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 4.52/0.95    introduced(choice_axiom,[])).
% 4.52/0.95  fof(f74,plain,(
% 4.52/0.95    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(rectify,[],[f73])).
% 4.52/0.95  fof(f73,plain,(
% 4.52/0.95    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(nnf_transformation,[],[f46])).
% 4.52/0.95  fof(f46,plain,(
% 4.52/0.95    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(flattening,[],[f45])).
% 4.52/0.95  fof(f45,plain,(
% 4.52/0.95    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 4.52/0.95    inference(ennf_transformation,[],[f8])).
% 4.52/0.95  fof(f8,axiom,(
% 4.52/0.95    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 4.52/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 4.52/0.95  fof(f10309,plain,(
% 4.52/0.95    r4_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))) | ~spl9_337),
% 4.52/0.95    inference(subsumption_resolution,[],[f10308,f81])).
% 4.52/0.95  fof(f10308,plain,(
% 4.52/0.95    r4_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))) | v2_struct_0(sK0) | ~spl9_337),
% 4.52/0.95    inference(subsumption_resolution,[],[f10307,f82])).
% 4.52/0.95  fof(f10307,plain,(
% 4.52/0.95    r4_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl9_337),
% 4.52/0.95    inference(subsumption_resolution,[],[f10306,f83])).
% 4.52/0.95  fof(f10306,plain,(
% 4.52/0.95    r4_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl9_337),
% 4.52/0.95    inference(subsumption_resolution,[],[f10305,f84])).
% 4.52/0.95  fof(f10305,plain,(
% 4.52/0.95    r4_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl9_337),
% 4.52/0.95    inference(subsumption_resolution,[],[f10143,f9978])).
% 4.52/0.95  fof(f10143,plain,(
% 4.52/0.95    ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | r4_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl9_337),
% 4.52/0.95    inference(superposition,[],[f137,f10030])).
% 4.52/0.95  fof(f137,plain,(
% 4.52/0.95    ( ! [X0,X1] : (~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 4.52/0.95    inference(duplicate_literal_removal,[],[f131])).
% 4.52/0.95  fof(f131,plain,(
% 4.52/0.95    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.52/0.95    inference(equality_resolution,[],[f114])).
% 4.52/0.95  fof(f114,plain,(
% 4.52/0.95    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.52/0.95    inference(cnf_transformation,[],[f72])).
% 4.52/0.95  fof(f72,plain,(
% 4.52/0.95    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK6(X0,X1,X2)) & r4_lattice3(X0,sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f70,f71])).
% 4.52/0.95  fof(f71,plain,(
% 4.52/0.95    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK6(X0,X1,X2)) & r4_lattice3(X0,sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 4.52/0.95    introduced(choice_axiom,[])).
% 4.52/0.95  fof(f70,plain,(
% 4.52/0.95    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(rectify,[],[f69])).
% 4.52/0.95  fof(f69,plain,(
% 4.52/0.95    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(flattening,[],[f68])).
% 4.52/0.95  fof(f68,plain,(
% 4.52/0.95    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(nnf_transformation,[],[f44])).
% 4.52/0.95  fof(f44,plain,(
% 4.52/0.95    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(flattening,[],[f43])).
% 4.52/0.95  fof(f43,plain,(
% 4.52/0.95    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 4.52/0.95    inference(ennf_transformation,[],[f9])).
% 4.52/0.95  fof(f9,axiom,(
% 4.52/0.95    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 4.52/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 4.52/0.95  fof(f10703,plain,(
% 4.52/0.95    spl9_3 | ~spl9_6 | ~spl9_66 | ~spl9_337 | ~spl9_377),
% 4.52/0.95    inference(avatar_contradiction_clause,[],[f10702])).
% 4.52/0.95  fof(f10702,plain,(
% 4.52/0.95    $false | (spl9_3 | ~spl9_6 | ~spl9_66 | ~spl9_337 | ~spl9_377)),
% 4.52/0.95    inference(subsumption_resolution,[],[f10701,f81])).
% 4.52/0.95  fof(f10701,plain,(
% 4.52/0.95    v2_struct_0(sK0) | (spl9_3 | ~spl9_6 | ~spl9_66 | ~spl9_337 | ~spl9_377)),
% 4.52/0.95    inference(subsumption_resolution,[],[f10700,f165])).
% 4.52/0.95  fof(f165,plain,(
% 4.52/0.95    v8_lattices(sK0)),
% 4.52/0.95    inference(global_subsumption,[],[f84,f164])).
% 4.52/0.95  fof(f164,plain,(
% 4.52/0.95    v8_lattices(sK0) | ~l3_lattices(sK0)),
% 4.52/0.95    inference(subsumption_resolution,[],[f160,f81])).
% 4.52/0.95  fof(f160,plain,(
% 4.52/0.95    v8_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 4.52/0.95    inference(resolution,[],[f82,f90])).
% 4.52/0.95  fof(f90,plain,(
% 4.52/0.95    ( ! [X0] : (~v10_lattices(X0) | v8_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 4.52/0.95    inference(cnf_transformation,[],[f26])).
% 4.52/0.95  fof(f26,plain,(
% 4.52/0.95    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 4.52/0.95    inference(flattening,[],[f25])).
% 4.52/0.95  fof(f25,plain,(
% 4.52/0.95    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 4.52/0.95    inference(ennf_transformation,[],[f21])).
% 4.52/0.95  fof(f21,plain,(
% 4.52/0.95    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 4.52/0.95    inference(pure_predicate_removal,[],[f20])).
% 4.52/0.95  fof(f20,plain,(
% 4.52/0.95    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 4.52/0.95    inference(pure_predicate_removal,[],[f19])).
% 4.52/0.95  fof(f19,plain,(
% 4.52/0.95    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 4.52/0.95    inference(pure_predicate_removal,[],[f2])).
% 4.52/0.95  fof(f2,axiom,(
% 4.52/0.95    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 4.52/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 4.52/0.95  fof(f10700,plain,(
% 4.52/0.95    ~v8_lattices(sK0) | v2_struct_0(sK0) | (spl9_3 | ~spl9_6 | ~spl9_66 | ~spl9_337 | ~spl9_377)),
% 4.52/0.95    inference(subsumption_resolution,[],[f10699,f167])).
% 4.52/0.95  fof(f167,plain,(
% 4.52/0.95    v9_lattices(sK0)),
% 4.52/0.95    inference(global_subsumption,[],[f84,f166])).
% 4.52/0.95  fof(f166,plain,(
% 4.52/0.95    v9_lattices(sK0) | ~l3_lattices(sK0)),
% 4.52/0.95    inference(subsumption_resolution,[],[f161,f81])).
% 4.52/0.95  fof(f161,plain,(
% 4.52/0.95    v9_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 4.52/0.95    inference(resolution,[],[f82,f91])).
% 4.52/0.95  fof(f91,plain,(
% 4.52/0.95    ( ! [X0] : (~v10_lattices(X0) | v9_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 4.52/0.95    inference(cnf_transformation,[],[f26])).
% 4.52/0.95  fof(f10699,plain,(
% 4.52/0.95    ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (spl9_3 | ~spl9_6 | ~spl9_66 | ~spl9_337 | ~spl9_377)),
% 4.52/0.95    inference(subsumption_resolution,[],[f10698,f84])).
% 4.52/0.95  fof(f10698,plain,(
% 4.52/0.95    ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (spl9_3 | ~spl9_6 | ~spl9_66 | ~spl9_337 | ~spl9_377)),
% 4.52/0.95    inference(subsumption_resolution,[],[f10697,f356])).
% 4.52/0.95  fof(f10697,plain,(
% 4.52/0.95    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (spl9_3 | ~spl9_6 | ~spl9_66 | ~spl9_337 | ~spl9_377)),
% 4.52/0.95    inference(subsumption_resolution,[],[f10696,f9978])).
% 4.52/0.95  fof(f10696,plain,(
% 4.52/0.95    ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (spl9_3 | ~spl9_6 | ~spl9_66 | ~spl9_377)),
% 4.52/0.95    inference(subsumption_resolution,[],[f10695,f9970])).
% 4.52/0.95  fof(f9970,plain,(
% 4.52/0.95    k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | (spl9_3 | ~spl9_6 | ~spl9_66)),
% 4.52/0.95    inference(subsumption_resolution,[],[f9969,f81])).
% 4.52/0.95  fof(f9969,plain,(
% 4.52/0.95    k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | v2_struct_0(sK0) | (spl9_3 | ~spl9_6 | ~spl9_66)),
% 4.52/0.95    inference(subsumption_resolution,[],[f9968,f176])).
% 4.52/0.95  fof(f176,plain,(
% 4.52/0.95    l1_lattices(sK0)),
% 4.52/0.95    inference(resolution,[],[f84,f87])).
% 4.52/0.95  fof(f87,plain,(
% 4.52/0.95    ( ! [X0] : (~l3_lattices(X0) | l1_lattices(X0)) )),
% 4.52/0.95    inference(cnf_transformation,[],[f24])).
% 4.52/0.95  fof(f24,plain,(
% 4.52/0.95    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 4.52/0.95    inference(ennf_transformation,[],[f18])).
% 4.52/0.95  fof(f18,plain,(
% 4.52/0.95    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 4.52/0.95    inference(pure_predicate_removal,[],[f5])).
% 4.52/0.95  fof(f5,axiom,(
% 4.52/0.95    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 4.52/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 4.52/0.95  fof(f9968,plain,(
% 4.52/0.95    k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (spl9_3 | ~spl9_6 | ~spl9_66)),
% 4.52/0.95    inference(subsumption_resolution,[],[f9967,f356])).
% 4.52/0.95  fof(f9967,plain,(
% 4.52/0.95    k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (spl9_3 | ~spl9_6 | ~spl9_66)),
% 4.52/0.95    inference(subsumption_resolution,[],[f9966,f149])).
% 4.52/0.95  fof(f149,plain,(
% 4.52/0.95    ~v13_lattices(sK0) | spl9_3),
% 4.52/0.95    inference(avatar_component_clause,[],[f147])).
% 4.52/0.95  fof(f147,plain,(
% 4.52/0.95    spl9_3 <=> v13_lattices(sK0)),
% 4.52/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 4.52/0.95  fof(f9966,plain,(
% 4.52/0.95    k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | v13_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (~spl9_6 | ~spl9_66)),
% 4.52/0.95    inference(duplicate_literal_removal,[],[f9964])).
% 4.52/0.95  fof(f9964,plain,(
% 4.52/0.95    k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | v13_lattices(sK0) | k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (~spl9_6 | ~spl9_66)),
% 4.52/0.95    inference(superposition,[],[f103,f9720])).
% 4.52/0.95  fof(f9720,plain,(
% 4.52/0.95    k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),k15_lattice3(sK0,k1_xboole_0)) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | (~spl9_6 | ~spl9_66)),
% 4.52/0.95    inference(resolution,[],[f2566,f356])).
% 4.52/0.95  fof(f2566,plain,(
% 4.52/0.95    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,sK2(sK0,X2),k15_lattice3(sK0,k1_xboole_0)) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2))) ) | ~spl9_66),
% 4.52/0.95    inference(avatar_component_clause,[],[f2565])).
% 4.52/0.95  fof(f2565,plain,(
% 4.52/0.95    spl9_66 <=> ! [X2] : (k2_lattices(sK0,sK2(sK0,X2),k15_lattice3(sK0,k1_xboole_0)) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0)))),
% 4.52/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).
% 4.52/0.95  fof(f103,plain,(
% 4.52/0.95    ( ! [X0,X1] : (k2_lattices(X0,sK2(X0,X1),X1) != X1 | v13_lattices(X0) | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 4.52/0.95    inference(cnf_transformation,[],[f62])).
% 4.52/0.95  fof(f62,plain,(
% 4.52/0.95    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f59,f61,f60])).
% 4.52/0.95  fof(f60,plain,(
% 4.52/0.95    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 4.52/0.95    introduced(choice_axiom,[])).
% 4.52/0.95  fof(f61,plain,(
% 4.52/0.95    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 4.52/0.95    introduced(choice_axiom,[])).
% 4.52/0.95  fof(f59,plain,(
% 4.52/0.95    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(rectify,[],[f58])).
% 4.52/0.95  fof(f58,plain,(
% 4.52/0.95    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(nnf_transformation,[],[f34])).
% 4.52/0.95  fof(f34,plain,(
% 4.52/0.95    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(flattening,[],[f33])).
% 4.52/0.95  fof(f33,plain,(
% 4.52/0.95    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 4.52/0.95    inference(ennf_transformation,[],[f7])).
% 4.52/0.95  fof(f7,axiom,(
% 4.52/0.95    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 4.52/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).
% 4.52/0.95  fof(f10695,plain,(
% 4.52/0.95    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | ~spl9_377),
% 4.52/0.95    inference(resolution,[],[f10665,f92])).
% 4.52/0.95  fof(f92,plain,(
% 4.52/0.95    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) = X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 4.52/0.95    inference(cnf_transformation,[],[f53])).
% 4.52/0.95  fof(f53,plain,(
% 4.52/0.95    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(nnf_transformation,[],[f28])).
% 4.52/0.95  fof(f28,plain,(
% 4.52/0.95    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(flattening,[],[f27])).
% 4.52/0.95  fof(f27,plain,(
% 4.52/0.95    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 4.52/0.95    inference(ennf_transformation,[],[f6])).
% 4.52/0.95  fof(f6,axiom,(
% 4.52/0.95    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 4.52/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 4.52/0.95  fof(f10665,plain,(
% 4.52/0.95    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~spl9_377),
% 4.52/0.95    inference(avatar_component_clause,[],[f10663])).
% 4.52/0.95  fof(f9994,plain,(
% 4.52/0.95    spl9_3 | ~spl9_6 | spl9_337),
% 4.52/0.95    inference(avatar_contradiction_clause,[],[f9993])).
% 4.52/0.95  fof(f9993,plain,(
% 4.52/0.95    $false | (spl9_3 | ~spl9_6 | spl9_337)),
% 4.52/0.95    inference(subsumption_resolution,[],[f9992,f81])).
% 4.52/0.95  fof(f9992,plain,(
% 4.52/0.95    v2_struct_0(sK0) | (spl9_3 | ~spl9_6 | spl9_337)),
% 4.52/0.95    inference(subsumption_resolution,[],[f9991,f176])).
% 4.52/0.95  fof(f9991,plain,(
% 4.52/0.95    ~l1_lattices(sK0) | v2_struct_0(sK0) | (spl9_3 | ~spl9_6 | spl9_337)),
% 4.52/0.95    inference(subsumption_resolution,[],[f9990,f356])).
% 4.52/0.95  fof(f9990,plain,(
% 4.52/0.95    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (spl9_3 | spl9_337)),
% 4.52/0.95    inference(subsumption_resolution,[],[f9989,f149])).
% 4.52/0.95  fof(f9989,plain,(
% 4.52/0.95    v13_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | spl9_337),
% 4.52/0.95    inference(resolution,[],[f9979,f102])).
% 4.52/0.95  fof(f102,plain,(
% 4.52/0.95    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 4.52/0.95    inference(cnf_transformation,[],[f62])).
% 4.52/0.95  fof(f9979,plain,(
% 4.52/0.95    ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | spl9_337),
% 4.52/0.95    inference(avatar_component_clause,[],[f9977])).
% 4.52/0.95  fof(f5128,plain,(
% 4.52/0.95    spl9_5 | ~spl9_6 | ~spl9_12 | ~spl9_13 | ~spl9_59),
% 4.52/0.95    inference(avatar_contradiction_clause,[],[f5127])).
% 4.52/0.95  fof(f5127,plain,(
% 4.52/0.95    $false | (spl9_5 | ~spl9_6 | ~spl9_12 | ~spl9_13 | ~spl9_59)),
% 4.52/0.95    inference(subsumption_resolution,[],[f5123,f157])).
% 4.52/0.95  fof(f157,plain,(
% 4.52/0.95    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl9_5),
% 4.52/0.95    inference(avatar_component_clause,[],[f155])).
% 4.52/0.95  fof(f155,plain,(
% 4.52/0.95    spl9_5 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 4.52/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 4.52/0.95  fof(f5123,plain,(
% 4.52/0.95    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | (~spl9_6 | ~spl9_12 | ~spl9_13 | ~spl9_59)),
% 4.52/0.95    inference(backward_demodulation,[],[f4417,f4840])).
% 4.52/0.95  fof(f4840,plain,(
% 4.52/0.95    k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (~spl9_6 | ~spl9_59)),
% 4.52/0.95    inference(resolution,[],[f2499,f356])).
% 4.52/0.95  fof(f2499,plain,(
% 4.52/0.95    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0))) ) | ~spl9_59),
% 4.52/0.95    inference(avatar_component_clause,[],[f2498])).
% 4.52/0.95  fof(f2498,plain,(
% 4.52/0.95    spl9_59 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0)))),
% 4.52/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).
% 4.52/0.95  fof(f4417,plain,(
% 4.52/0.95    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (~spl9_6 | ~spl9_12 | ~spl9_13)),
% 4.52/0.95    inference(subsumption_resolution,[],[f4416,f81])).
% 4.52/0.95  fof(f4416,plain,(
% 4.52/0.95    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | v2_struct_0(sK0) | (~spl9_6 | ~spl9_12 | ~spl9_13)),
% 4.52/0.95    inference(subsumption_resolution,[],[f4415,f165])).
% 4.52/0.95  fof(f4415,plain,(
% 4.52/0.95    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (~spl9_6 | ~spl9_12 | ~spl9_13)),
% 4.52/0.95    inference(subsumption_resolution,[],[f4414,f167])).
% 4.52/0.95  fof(f4414,plain,(
% 4.52/0.95    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (~spl9_6 | ~spl9_12 | ~spl9_13)),
% 4.52/0.95    inference(subsumption_resolution,[],[f4413,f84])).
% 4.52/0.95  fof(f4413,plain,(
% 4.52/0.95    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (~spl9_6 | ~spl9_12 | ~spl9_13)),
% 4.52/0.95    inference(subsumption_resolution,[],[f4412,f356])).
% 4.52/0.95  fof(f4412,plain,(
% 4.52/0.95    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (~spl9_12 | ~spl9_13)),
% 4.52/0.95    inference(subsumption_resolution,[],[f4411,f726])).
% 4.52/0.95  fof(f726,plain,(
% 4.52/0.95    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl9_12),
% 4.52/0.95    inference(avatar_component_clause,[],[f725])).
% 4.52/0.95  fof(f725,plain,(
% 4.52/0.95    spl9_12 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 4.52/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 4.52/0.95  fof(f4411,plain,(
% 4.52/0.95    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | ~spl9_13),
% 4.52/0.95    inference(resolution,[],[f731,f92])).
% 4.52/0.95  fof(f731,plain,(
% 4.52/0.95    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~spl9_13),
% 4.52/0.95    inference(avatar_component_clause,[],[f729])).
% 4.52/0.95  fof(f729,plain,(
% 4.52/0.95    spl9_13 <=> r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 4.52/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 4.52/0.95  fof(f4913,plain,(
% 4.52/0.95    ~spl9_1),
% 4.52/0.95    inference(avatar_contradiction_clause,[],[f4912])).
% 4.52/0.95  fof(f4912,plain,(
% 4.52/0.95    $false | ~spl9_1),
% 4.52/0.95    inference(subsumption_resolution,[],[f141,f81])).
% 4.52/0.95  fof(f141,plain,(
% 4.52/0.95    v2_struct_0(sK0) | ~spl9_1),
% 4.52/0.95    inference(avatar_component_clause,[],[f139])).
% 4.52/0.95  fof(f139,plain,(
% 4.52/0.95    spl9_1 <=> v2_struct_0(sK0)),
% 4.52/0.95    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 4.52/0.95  fof(f2585,plain,(
% 4.52/0.95    spl9_13 | ~spl9_6 | ~spl9_7 | ~spl9_12),
% 4.52/0.95    inference(avatar_split_clause,[],[f1351,f725,f359,f355,f729])).
% 4.52/0.95  fof(f1351,plain,(
% 4.52/0.95    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (~spl9_7 | ~spl9_12)),
% 4.52/0.95    inference(resolution,[],[f885,f827])).
% 4.52/0.95  fof(f827,plain,(
% 4.52/0.95    r2_hidden(k15_lattice3(sK0,k1_xboole_0),a_2_3_lattice3(sK0,k5_lattices(sK0))) | (~spl9_7 | ~spl9_12)),
% 4.52/0.95    inference(subsumption_resolution,[],[f810,f726])).
% 4.52/0.95  fof(f810,plain,(
% 4.52/0.95    r2_hidden(k15_lattice3(sK0,k1_xboole_0),a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | (~spl9_7 | ~spl9_12)),
% 4.52/0.95    inference(superposition,[],[f360,f780])).
% 4.52/0.95  fof(f780,plain,(
% 4.52/0.95    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~spl9_12),
% 4.52/0.95    inference(subsumption_resolution,[],[f779,f81])).
% 4.52/0.95  fof(f779,plain,(
% 4.52/0.95    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | ~spl9_12),
% 4.52/0.95    inference(subsumption_resolution,[],[f778,f82])).
% 4.52/0.95  fof(f778,plain,(
% 4.52/0.95    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl9_12),
% 4.52/0.95    inference(subsumption_resolution,[],[f777,f83])).
% 4.52/0.95  fof(f777,plain,(
% 4.52/0.95    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl9_12),
% 4.52/0.95    inference(subsumption_resolution,[],[f770,f84])).
% 4.52/0.95  fof(f770,plain,(
% 4.52/0.95    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl9_12),
% 4.52/0.95    inference(resolution,[],[f726,f110])).
% 4.52/0.95  fof(f885,plain,(
% 4.52/0.95    ( ! [X0] : (~r2_hidden(X0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,k5_lattices(sK0))) ) | ~spl9_12),
% 4.52/0.95    inference(subsumption_resolution,[],[f884,f81])).
% 4.52/0.95  fof(f884,plain,(
% 4.52/0.95    ( ! [X0] : (~r2_hidden(X0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,k5_lattices(sK0)) | v2_struct_0(sK0)) ) | ~spl9_12),
% 4.52/0.95    inference(subsumption_resolution,[],[f883,f84])).
% 4.52/0.95  fof(f883,plain,(
% 4.52/0.95    ( ! [X0] : (~r2_hidden(X0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,k5_lattices(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_12),
% 4.52/0.95    inference(subsumption_resolution,[],[f881,f726])).
% 4.52/0.95  fof(f881,plain,(
% 4.52/0.95    ( ! [X0] : (~r2_hidden(X0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_12),
% 4.52/0.95    inference(resolution,[],[f841,f119])).
% 4.52/0.95  fof(f841,plain,(
% 4.52/0.95    r4_lattice3(sK0,k5_lattices(sK0),a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~spl9_12),
% 4.52/0.95    inference(subsumption_resolution,[],[f840,f81])).
% 4.52/0.95  fof(f840,plain,(
% 4.52/0.95    r4_lattice3(sK0,k5_lattices(sK0),a_2_3_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | ~spl9_12),
% 4.52/0.95    inference(subsumption_resolution,[],[f839,f82])).
% 4.52/0.95  fof(f839,plain,(
% 4.52/0.95    r4_lattice3(sK0,k5_lattices(sK0),a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl9_12),
% 4.52/0.95    inference(subsumption_resolution,[],[f838,f83])).
% 4.52/0.95  fof(f838,plain,(
% 4.52/0.95    r4_lattice3(sK0,k5_lattices(sK0),a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl9_12),
% 4.52/0.95    inference(subsumption_resolution,[],[f837,f84])).
% 4.52/0.95  fof(f837,plain,(
% 4.52/0.95    r4_lattice3(sK0,k5_lattices(sK0),a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl9_12),
% 4.52/0.95    inference(subsumption_resolution,[],[f814,f726])).
% 4.52/0.95  fof(f814,plain,(
% 4.52/0.95    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | r4_lattice3(sK0,k5_lattices(sK0),a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl9_12),
% 4.52/0.95    inference(superposition,[],[f137,f780])).
% 4.52/0.95  fof(f2583,plain,(
% 4.52/0.95    ~spl9_6 | spl9_7),
% 4.52/0.95    inference(avatar_split_clause,[],[f1910,f359,f355])).
% 4.52/0.95  fof(f1910,plain,(
% 4.52/0.95    ( ! [X0] : (r2_hidden(k15_lattice3(sK0,k1_xboole_0),a_2_3_lattice3(sK0,k15_lattice3(sK0,X0))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) )),
% 4.52/0.95    inference(resolution,[],[f968,f86])).
% 4.52/0.95  fof(f86,plain,(
% 4.52/0.95    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.52/0.95    inference(cnf_transformation,[],[f1])).
% 4.52/0.95  fof(f1,axiom,(
% 4.52/0.95    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.52/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 4.52/0.95  fof(f968,plain,(
% 4.52/0.95    ( ! [X0,X1] : (~r1_tarski(X1,a_2_5_lattice3(sK0,a_2_5_lattice3(sK0,a_2_5_lattice3(sK0,X0)))) | r2_hidden(k15_lattice3(sK0,X1),a_2_3_lattice3(sK0,k15_lattice3(sK0,X0))) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) )),
% 4.52/0.95    inference(superposition,[],[f273,f172])).
% 4.52/0.95  fof(f172,plain,(
% 4.52/0.95    ( ! [X0] : (k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))) )),
% 4.52/0.95    inference(global_subsumption,[],[f84,f171])).
% 4.52/0.95  fof(f171,plain,(
% 4.52/0.95    ( ! [X0] : (~l3_lattices(sK0) | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))) )),
% 4.52/0.95    inference(subsumption_resolution,[],[f170,f81])).
% 4.52/0.95  fof(f170,plain,(
% 4.52/0.95    ( ! [X0] : (~l3_lattices(sK0) | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0)) | v2_struct_0(sK0)) )),
% 4.52/0.95    inference(subsumption_resolution,[],[f168,f82])).
% 4.52/0.95  fof(f168,plain,(
% 4.52/0.95    ( ! [X0] : (~l3_lattices(sK0) | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.52/0.95    inference(resolution,[],[f83,f108])).
% 4.52/0.95  fof(f108,plain,(
% 4.52/0.95    ( ! [X0,X1] : (~v4_lattice3(X0) | ~l3_lattices(X0) | k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 4.52/0.95    inference(cnf_transformation,[],[f38])).
% 4.52/0.95  fof(f38,plain,(
% 4.52/0.95    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(flattening,[],[f37])).
% 4.52/0.95  fof(f37,plain,(
% 4.52/0.95    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 4.52/0.95    inference(ennf_transformation,[],[f15])).
% 4.52/0.95  fof(f15,axiom,(
% 4.52/0.95    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))))),
% 4.52/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattice3)).
% 4.52/0.95  fof(f273,plain,(
% 4.52/0.95    ( ! [X0,X1] : (r2_hidden(k15_lattice3(sK0,X0),a_2_3_lattice3(sK0,k15_lattice3(sK0,X1))) | ~r1_tarski(X0,a_2_5_lattice3(sK0,a_2_5_lattice3(sK0,X1))) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))) )),
% 4.52/0.95    inference(subsumption_resolution,[],[f272,f81])).
% 4.52/0.95  fof(f272,plain,(
% 4.52/0.95    ( ! [X0,X1] : (~r1_tarski(X0,a_2_5_lattice3(sK0,a_2_5_lattice3(sK0,X1))) | r2_hidden(k15_lattice3(sK0,X0),a_2_3_lattice3(sK0,k15_lattice3(sK0,X1))) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 4.52/0.95    inference(subsumption_resolution,[],[f271,f82])).
% 4.52/0.95  fof(f271,plain,(
% 4.52/0.95    ( ! [X0,X1] : (~r1_tarski(X0,a_2_5_lattice3(sK0,a_2_5_lattice3(sK0,X1))) | r2_hidden(k15_lattice3(sK0,X0),a_2_3_lattice3(sK0,k15_lattice3(sK0,X1))) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.52/0.95    inference(subsumption_resolution,[],[f270,f83])).
% 4.52/0.95  fof(f270,plain,(
% 4.52/0.95    ( ! [X0,X1] : (~r1_tarski(X0,a_2_5_lattice3(sK0,a_2_5_lattice3(sK0,X1))) | r2_hidden(k15_lattice3(sK0,X0),a_2_3_lattice3(sK0,k15_lattice3(sK0,X1))) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.52/0.95    inference(subsumption_resolution,[],[f267,f84])).
% 4.52/0.95  fof(f267,plain,(
% 4.52/0.95    ( ! [X0,X1] : (~r1_tarski(X0,a_2_5_lattice3(sK0,a_2_5_lattice3(sK0,X1))) | r2_hidden(k15_lattice3(sK0,X0),a_2_3_lattice3(sK0,k15_lattice3(sK0,X1))) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.52/0.95    inference(resolution,[],[f212,f132])).
% 4.52/0.95  fof(f132,plain,(
% 4.52/0.95    ( ! [X2,X3,X1] : (~r3_lattices(X1,X3,X2) | r2_hidden(X3,a_2_3_lattice3(X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 4.52/0.95    inference(equality_resolution,[],[f127])).
% 4.52/0.95  fof(f127,plain,(
% 4.52/0.95    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_3_lattice3(X1,X2)) | ~r3_lattices(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 4.52/0.95    inference(cnf_transformation,[],[f80])).
% 4.52/0.95  fof(f80,plain,(
% 4.52/0.95    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_3_lattice3(X1,X2)) | ! [X3] : (~r3_lattices(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattices(X1,sK8(X0,X1,X2),X2) & sK8(X0,X1,X2) = X0 & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_3_lattice3(X1,X2)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 4.52/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f78,f79])).
% 4.52/0.95  fof(f79,plain,(
% 4.52/0.95    ! [X2,X1,X0] : (? [X4] : (r3_lattices(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattices(X1,sK8(X0,X1,X2),X2) & sK8(X0,X1,X2) = X0 & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))))),
% 4.52/0.95    introduced(choice_axiom,[])).
% 4.52/0.95  fof(f78,plain,(
% 4.52/0.95    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_3_lattice3(X1,X2)) | ! [X3] : (~r3_lattices(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattices(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_3_lattice3(X1,X2)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 4.52/0.95    inference(rectify,[],[f77])).
% 4.52/0.95  fof(f77,plain,(
% 4.52/0.95    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_3_lattice3(X1,X2)) | ! [X3] : (~r3_lattices(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattices(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_3_lattice3(X1,X2)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 4.52/0.95    inference(nnf_transformation,[],[f50])).
% 4.52/0.95  fof(f50,plain,(
% 4.52/0.95    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_3_lattice3(X1,X2)) <=> ? [X3] : (r3_lattices(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 4.52/0.95    inference(flattening,[],[f49])).
% 4.52/0.95  fof(f49,plain,(
% 4.52/0.95    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_3_lattice3(X1,X2)) <=> ? [X3] : (r3_lattices(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 4.52/0.95    inference(ennf_transformation,[],[f12])).
% 4.52/0.95  fof(f12,axiom,(
% 4.52/0.95    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_3_lattice3(X1,X2)) <=> ? [X3] : (r3_lattices(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 4.52/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_3_lattice3)).
% 4.52/0.95  fof(f212,plain,(
% 4.52/0.95    ( ! [X0,X1] : (r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X0)) | ~r1_tarski(X1,a_2_5_lattice3(sK0,a_2_5_lattice3(sK0,X0)))) )),
% 4.52/0.95    inference(superposition,[],[f195,f172])).
% 4.52/0.95  fof(f195,plain,(
% 4.52/0.95    ( ! [X4,X5] : (r3_lattices(sK0,k15_lattice3(sK0,X5),k15_lattice3(sK0,X4)) | ~r1_tarski(X5,a_2_5_lattice3(sK0,X4))) )),
% 4.52/0.95    inference(subsumption_resolution,[],[f194,f81])).
% 4.52/0.95  fof(f194,plain,(
% 4.52/0.95    ( ! [X4,X5] : (r3_lattices(sK0,k15_lattice3(sK0,X5),k15_lattice3(sK0,X4)) | ~r1_tarski(X5,a_2_5_lattice3(sK0,X4)) | v2_struct_0(sK0)) )),
% 4.52/0.95    inference(subsumption_resolution,[],[f193,f82])).
% 4.52/0.95  fof(f193,plain,(
% 4.52/0.95    ( ! [X4,X5] : (r3_lattices(sK0,k15_lattice3(sK0,X5),k15_lattice3(sK0,X4)) | ~r1_tarski(X5,a_2_5_lattice3(sK0,X4)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.52/0.95    inference(subsumption_resolution,[],[f192,f83])).
% 4.52/0.95  fof(f192,plain,(
% 4.52/0.95    ( ! [X4,X5] : (r3_lattices(sK0,k15_lattice3(sK0,X5),k15_lattice3(sK0,X4)) | ~r1_tarski(X5,a_2_5_lattice3(sK0,X4)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.52/0.95    inference(subsumption_resolution,[],[f182,f84])).
% 4.52/0.95  fof(f182,plain,(
% 4.52/0.95    ( ! [X4,X5] : (r3_lattices(sK0,k15_lattice3(sK0,X5),k15_lattice3(sK0,X4)) | ~r1_tarski(X5,a_2_5_lattice3(sK0,X4)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.52/0.95    inference(superposition,[],[f112,f172])).
% 4.52/0.95  fof(f112,plain,(
% 4.52/0.95    ( ! [X2,X0,X1] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ~r1_tarski(X1,X2) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 4.52/0.95    inference(cnf_transformation,[],[f42])).
% 4.52/0.95  fof(f42,plain,(
% 4.52/0.95    ! [X0] : (! [X1,X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) | ~r1_tarski(X1,X2)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(flattening,[],[f41])).
% 4.52/0.95  fof(f41,plain,(
% 4.52/0.95    ! [X0] : (! [X1,X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) | ~r1_tarski(X1,X2)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 4.52/0.95    inference(ennf_transformation,[],[f14])).
% 4.52/0.95  fof(f14,axiom,(
% 4.52/0.95    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 4.52/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_lattice3)).
% 4.52/0.95  fof(f2567,plain,(
% 4.52/0.95    spl9_3 | spl9_66 | ~spl9_6),
% 4.52/0.95    inference(avatar_split_clause,[],[f2512,f355,f2565,f147])).
% 4.52/0.95  fof(f2512,plain,(
% 4.52/0.95    ( ! [X2] : (k2_lattices(sK0,sK2(sK0,X2),k15_lattice3(sK0,k1_xboole_0)) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2)) | v13_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl9_6),
% 4.52/0.95    inference(subsumption_resolution,[],[f2511,f81])).
% 4.52/0.95  fof(f2511,plain,(
% 4.52/0.95    ( ! [X2] : (k2_lattices(sK0,sK2(sK0,X2),k15_lattice3(sK0,k1_xboole_0)) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2)) | v13_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | ~spl9_6),
% 4.52/0.95    inference(subsumption_resolution,[],[f696,f176])).
% 4.52/0.95  fof(f696,plain,(
% 4.52/0.95    ( ! [X2] : (k2_lattices(sK0,sK2(sK0,X2),k15_lattice3(sK0,k1_xboole_0)) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2)) | v13_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_6),
% 4.52/0.95    inference(resolution,[],[f400,f102])).
% 4.52/0.95  fof(f400,plain,(
% 4.52/0.95    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X2) = k2_lattices(sK0,X2,k15_lattice3(sK0,k1_xboole_0))) ) | ~spl9_6),
% 4.52/0.95    inference(subsumption_resolution,[],[f399,f81])).
% 4.52/0.95  fof(f399,plain,(
% 4.52/0.95    ( ! [X2] : (k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X2) = k2_lattices(sK0,X2,k15_lattice3(sK0,k1_xboole_0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | ~spl9_6),
% 4.52/0.95    inference(subsumption_resolution,[],[f398,f176])).
% 4.52/0.95  fof(f398,plain,(
% 4.52/0.95    ( ! [X2] : (k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X2) = k2_lattices(sK0,X2,k15_lattice3(sK0,k1_xboole_0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_6),
% 4.52/0.95    inference(subsumption_resolution,[],[f385,f163])).
% 4.52/0.95  fof(f163,plain,(
% 4.52/0.95    v6_lattices(sK0)),
% 4.52/0.95    inference(global_subsumption,[],[f84,f162])).
% 4.52/0.95  fof(f162,plain,(
% 4.52/0.95    v6_lattices(sK0) | ~l3_lattices(sK0)),
% 4.52/0.95    inference(subsumption_resolution,[],[f159,f81])).
% 4.52/0.95  fof(f159,plain,(
% 4.52/0.95    v6_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 4.52/0.95    inference(resolution,[],[f82,f89])).
% 4.52/0.95  fof(f89,plain,(
% 4.52/0.95    ( ! [X0] : (~v10_lattices(X0) | v6_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 4.52/0.95    inference(cnf_transformation,[],[f26])).
% 4.52/0.95  fof(f385,plain,(
% 4.52/0.95    ( ! [X2] : (k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X2) = k2_lattices(sK0,X2,k15_lattice3(sK0,k1_xboole_0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_6),
% 4.52/0.95    inference(resolution,[],[f356,f104])).
% 4.52/0.95  fof(f104,plain,(
% 4.52/0.95    ( ! [X4,X0,X3] : (~m1_subset_1(X4,u1_struct_0(X0)) | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 4.52/0.95    inference(cnf_transformation,[],[f67])).
% 4.52/0.95  fof(f67,plain,(
% 4.52/0.95    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f64,f66,f65])).
% 4.52/0.95  fof(f65,plain,(
% 4.52/0.95    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 4.52/0.95    introduced(choice_axiom,[])).
% 4.52/0.96  % (30155)Time limit reached!
% 4.52/0.96  % (30155)------------------------------
% 4.52/0.96  % (30155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.52/0.96  fof(f66,plain,(
% 4.52/0.96    ! [X0] : (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 4.52/0.96    introduced(choice_axiom,[])).
% 4.52/0.96  fof(f64,plain,(
% 4.52/0.96    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.96    inference(rectify,[],[f63])).
% 4.52/0.96  fof(f63,plain,(
% 4.52/0.96    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.96    inference(nnf_transformation,[],[f36])).
% 4.52/0.96  fof(f36,plain,(
% 4.52/0.96    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.96    inference(flattening,[],[f35])).
% 4.52/0.96  fof(f35,plain,(
% 4.52/0.96    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 4.52/0.96    inference(ennf_transformation,[],[f10])).
% 4.52/0.96  fof(f10,axiom,(
% 4.52/0.96    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 4.52/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).
% 4.52/0.96  fof(f2540,plain,(
% 4.52/0.96    spl9_4),
% 4.52/0.96    inference(avatar_contradiction_clause,[],[f2539])).
% 4.52/0.96  fof(f2539,plain,(
% 4.52/0.96    $false | spl9_4),
% 4.52/0.96    inference(subsumption_resolution,[],[f153,f84])).
% 4.52/0.96  fof(f153,plain,(
% 4.52/0.96    ~l3_lattices(sK0) | spl9_4),
% 4.52/0.96    inference(avatar_component_clause,[],[f151])).
% 4.52/0.96  fof(f151,plain,(
% 4.52/0.96    spl9_4 <=> l3_lattices(sK0)),
% 4.52/0.96    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 4.52/0.96  fof(f2500,plain,(
% 4.52/0.96    ~spl9_3 | spl9_59 | ~spl9_12),
% 4.52/0.96    inference(avatar_split_clause,[],[f2496,f725,f2498,f147])).
% 4.52/0.96  fof(f2496,plain,(
% 4.52/0.96    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0)) | ~v13_lattices(sK0)) ) | ~spl9_12),
% 4.52/0.96    inference(subsumption_resolution,[],[f2495,f81])).
% 4.52/0.96  fof(f2495,plain,(
% 4.52/0.96    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0)) | ~v13_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_12),
% 4.52/0.96    inference(subsumption_resolution,[],[f764,f176])).
% 4.52/0.96  fof(f764,plain,(
% 4.52/0.96    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_12),
% 4.52/0.96    inference(resolution,[],[f726,f128])).
% 4.52/0.96  fof(f128,plain,(
% 4.52/0.96    ( ! [X0,X3] : (~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 4.52/0.96    inference(equality_resolution,[],[f96])).
% 4.52/0.96  fof(f96,plain,(
% 4.52/0.96    ( ! [X0,X3,X1] : (k2_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 4.52/0.96    inference(cnf_transformation,[],[f57])).
% 4.52/0.96  fof(f57,plain,(
% 4.52/0.96    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f55,f56])).
% 4.52/0.96  fof(f56,plain,(
% 4.52/0.96    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 4.52/0.96    introduced(choice_axiom,[])).
% 4.52/0.96  fof(f55,plain,(
% 4.52/0.96    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.96    inference(rectify,[],[f54])).
% 4.52/0.96  fof(f54,plain,(
% 4.52/0.96    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.96    inference(nnf_transformation,[],[f32])).
% 4.52/0.96  fof(f32,plain,(
% 4.52/0.96    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.96    inference(flattening,[],[f31])).
% 4.52/0.96  fof(f31,plain,(
% 4.52/0.96    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 4.52/0.96    inference(ennf_transformation,[],[f3])).
% 4.52/0.96  fof(f3,axiom,(
% 4.52/0.96    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 4.52/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).
% 4.52/0.96  fof(f740,plain,(
% 4.52/0.96    spl9_12),
% 4.52/0.96    inference(avatar_contradiction_clause,[],[f739])).
% 4.52/0.96  fof(f739,plain,(
% 4.52/0.96    $false | spl9_12),
% 4.52/0.96    inference(subsumption_resolution,[],[f738,f81])).
% 4.52/0.96  fof(f738,plain,(
% 4.52/0.96    v2_struct_0(sK0) | spl9_12),
% 4.52/0.96    inference(subsumption_resolution,[],[f737,f176])).
% 4.52/0.96  fof(f737,plain,(
% 4.52/0.96    ~l1_lattices(sK0) | v2_struct_0(sK0) | spl9_12),
% 4.52/0.96    inference(resolution,[],[f727,f94])).
% 4.52/0.96  fof(f94,plain,(
% 4.52/0.96    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 4.52/0.96    inference(cnf_transformation,[],[f30])).
% 4.52/0.96  fof(f30,plain,(
% 4.52/0.96    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.96    inference(flattening,[],[f29])).
% 4.52/0.96  fof(f29,plain,(
% 4.52/0.96    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 4.52/0.96    inference(ennf_transformation,[],[f4])).
% 4.52/0.96  fof(f4,axiom,(
% 4.52/0.96    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 4.52/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).
% 4.52/0.96  fof(f727,plain,(
% 4.52/0.96    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | spl9_12),
% 4.52/0.96    inference(avatar_component_clause,[],[f725])).
% 4.52/0.96  fof(f365,plain,(
% 4.52/0.96    spl9_6),
% 4.52/0.96    inference(avatar_contradiction_clause,[],[f364])).
% 4.52/0.96  fof(f364,plain,(
% 4.52/0.96    $false | spl9_6),
% 4.52/0.96    inference(subsumption_resolution,[],[f363,f81])).
% 4.52/0.96  fof(f363,plain,(
% 4.52/0.96    v2_struct_0(sK0) | spl9_6),
% 4.52/0.96    inference(subsumption_resolution,[],[f362,f84])).
% 4.52/0.96  fof(f362,plain,(
% 4.52/0.96    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl9_6),
% 4.52/0.96    inference(resolution,[],[f357,f123])).
% 4.52/0.96  fof(f123,plain,(
% 4.52/0.96    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.52/0.96    inference(cnf_transformation,[],[f48])).
% 4.52/0.96  fof(f48,plain,(
% 4.52/0.96    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.52/0.96    inference(flattening,[],[f47])).
% 4.52/0.96  fof(f47,plain,(
% 4.52/0.96    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 4.52/0.96    inference(ennf_transformation,[],[f11])).
% 4.52/0.96  fof(f11,axiom,(
% 4.52/0.96    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 4.52/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 4.52/0.96  fof(f357,plain,(
% 4.52/0.96    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | spl9_6),
% 4.52/0.96    inference(avatar_component_clause,[],[f355])).
% 4.52/0.96  fof(f178,plain,(
% 4.52/0.96    spl9_2),
% 4.52/0.96    inference(avatar_contradiction_clause,[],[f177])).
% 4.52/0.96  fof(f177,plain,(
% 4.52/0.96    $false | spl9_2),
% 4.52/0.96    inference(subsumption_resolution,[],[f145,f82])).
% 4.52/0.96  fof(f145,plain,(
% 4.52/0.96    ~v10_lattices(sK0) | spl9_2),
% 4.52/0.96    inference(avatar_component_clause,[],[f143])).
% 4.52/0.96  fof(f143,plain,(
% 4.52/0.96    spl9_2 <=> v10_lattices(sK0)),
% 4.52/0.96    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 4.52/0.96  fof(f158,plain,(
% 4.52/0.96    spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_5),
% 4.52/0.96    inference(avatar_split_clause,[],[f85,f155,f151,f147,f143,f139])).
% 4.52/0.96  fof(f85,plain,(
% 4.52/0.96    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 4.52/0.96    inference(cnf_transformation,[],[f52])).
% 4.52/0.96  % SZS output end Proof for theBenchmark
% 4.52/0.96  % (30142)------------------------------
% 4.52/0.96  % (30142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.52/0.96  % (30142)Termination reason: Refutation
% 4.52/0.96  
% 4.52/0.96  % (30142)Memory used [KB]: 15479
% 4.52/0.96  % (30142)Time elapsed: 0.529 s
% 4.52/0.96  % (30142)------------------------------
% 4.52/0.96  % (30142)------------------------------
% 4.52/0.96  % (30140)Success in time 0.608 s
%------------------------------------------------------------------------------
