%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:40 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  220 ( 539 expanded)
%              Number of leaves         :   31 ( 165 expanded)
%              Depth                    :   33
%              Number of atoms          : 1003 (2681 expanded)
%              Number of equality atoms :   70 ( 317 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1564,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1079,f1096,f1120,f1139,f1165,f1541])).

fof(f1541,plain,
    ( ~ spl18_2
    | ~ spl18_6 ),
    inference(avatar_contradiction_clause,[],[f1540])).

fof(f1540,plain,
    ( $false
    | ~ spl18_2
    | ~ spl18_6 ),
    inference(subsumption_resolution,[],[f1539,f76])).

fof(f76,plain,(
    v4_lattice3(sK11) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( k15_lattice3(sK11,sK12) != k16_lattice3(sK11,a_2_2_lattice3(sK11,sK12))
    & l3_lattices(sK11)
    & v4_lattice3(sK11)
    & v10_lattices(sK11)
    & ~ v2_struct_0(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f11,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] : k15_lattice3(sK11,X1) != k16_lattice3(sK11,a_2_2_lattice3(sK11,X1))
      & l3_lattices(sK11)
      & v4_lattice3(sK11)
      & v10_lattices(sK11)
      & ~ v2_struct_0(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] : k15_lattice3(sK11,X1) != k16_lattice3(sK11,a_2_2_lattice3(sK11,X1))
   => k15_lattice3(sK11,sK12) != k16_lattice3(sK11,a_2_2_lattice3(sK11,sK12)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).

fof(f1539,plain,
    ( ~ v4_lattice3(sK11)
    | ~ spl18_2
    | ~ spl18_6 ),
    inference(subsumption_resolution,[],[f1538,f77])).

fof(f77,plain,(
    l3_lattices(sK11) ),
    inference(cnf_transformation,[],[f44])).

fof(f1538,plain,
    ( ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | ~ spl18_2
    | ~ spl18_6 ),
    inference(subsumption_resolution,[],[f1537,f75])).

fof(f75,plain,(
    v10_lattices(sK11) ),
    inference(cnf_transformation,[],[f44])).

fof(f1537,plain,
    ( ~ v10_lattices(sK11)
    | ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | ~ spl18_2
    | ~ spl18_6 ),
    inference(subsumption_resolution,[],[f1536,f74])).

fof(f74,plain,(
    ~ v2_struct_0(sK11) ),
    inference(cnf_transformation,[],[f44])).

fof(f1536,plain,
    ( v2_struct_0(sK11)
    | ~ v10_lattices(sK11)
    | ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | ~ spl18_2
    | ~ spl18_6 ),
    inference(subsumption_resolution,[],[f1535,f1114])).

fof(f1114,plain,
    ( m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11))
    | ~ spl18_6 ),
    inference(avatar_component_clause,[],[f1113])).

fof(f1113,plain,
    ( spl18_6
  <=> m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_6])])).

fof(f1535,plain,
    ( ~ m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11))
    | v2_struct_0(sK11)
    | ~ v10_lattices(sK11)
    | ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | ~ spl18_2 ),
    inference(subsumption_resolution,[],[f1510,f1056])).

fof(f1056,plain,
    ( r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12))
    | ~ spl18_2 ),
    inference(avatar_component_clause,[],[f1055])).

fof(f1055,plain,
    ( spl18_2
  <=> r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).

fof(f1510,plain,
    ( ~ r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12))
    | ~ m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11))
    | v2_struct_0(sK11)
    | ~ v10_lattices(sK11)
    | ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11) ),
    inference(trivial_inequality_removal,[],[f1504])).

fof(f1504,plain,
    ( k15_lattice3(sK11,sK12) != k15_lattice3(sK11,sK12)
    | ~ r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12))
    | ~ m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11))
    | v2_struct_0(sK11)
    | ~ v10_lattices(sK11)
    | ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11) ),
    inference(resolution,[],[f1045,f353])).

fof(f353,plain,(
    ! [X4,X3] :
      ( r3_lattice3(X3,k15_lattice3(X3,X4),a_2_2_lattice3(X3,X4))
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | ~ l3_lattices(X3)
      | ~ v4_lattice3(X3) ) ),
    inference(subsumption_resolution,[],[f349,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( sP4(X0,k15_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( sP4(X0,k15_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f96,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP4(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP4(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f17,f31,f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( sP3(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X1,X3)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r3_lattice3(X0,X1,X2)
        <=> sP3(X1,X0,X2) )
      | ~ sP4(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

fof(f349,plain,(
    ! [X4,X3] :
      ( ~ v4_lattice3(X3)
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | ~ l3_lattices(X3)
      | r3_lattice3(X3,k15_lattice3(X3,X4),a_2_2_lattice3(X3,X4))
      | ~ sP4(X3,k15_lattice3(X3,X4)) ) ),
    inference(resolution,[],[f346,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X1,X0,X2)
      | r3_lattice3(X0,X1,X2)
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X0,X1,X2)
            | ~ sP3(X1,X0,X2) )
          & ( sP3(X1,X0,X2)
            | ~ r3_lattice3(X0,X1,X2) ) )
      | ~ sP4(X0,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f346,plain,(
    ! [X0,X1] :
      ( sP3(k15_lattice3(X0,X1),X0,a_2_2_lattice3(X0,X1))
      | ~ v4_lattice3(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f340])).

fof(f340,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | sP3(k15_lattice3(X0,X1),X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP3(k15_lattice3(X0,X1),X0,a_2_2_lattice3(X0,X1)) ) ),
    inference(resolution,[],[f252,f277])).

fof(f277,plain,(
    ! [X10,X8,X11,X9] :
      ( r4_lattice3(X10,sK14(X8,X9,a_2_2_lattice3(X10,X11)),X11)
      | ~ l3_lattices(X10)
      | ~ v4_lattice3(X10)
      | ~ v10_lattices(X10)
      | v2_struct_0(X10)
      | sP3(X8,X9,a_2_2_lattice3(X10,X11)) ) ),
    inference(resolution,[],[f267,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X0,X1,X2)
      | r4_lattice3(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,X2,X0)
      | ~ sP7(X0,X1,X2)
      | ~ sP7(X0,X1,X2) ) ),
    inference(superposition,[],[f109,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( sK16(X0,X1,X2) = X2
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ! [X3] :
            ( ~ r4_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r4_lattice3(X1,sK16(X0,X1,X2),X0)
          & sK16(X0,X1,X2) = X2
          & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f66,f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK16(X0,X1,X2),X0)
        & sK16(X0,X1,X2) = X2
        & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ! [X3] :
            ( ~ r4_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r4_lattice3(X1,X4,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ( sP7(X2,X1,X0)
        | ! [X3] :
            ( ~ r4_lattice3(X1,X3,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP7(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( sP7(X2,X1,X0)
    <=> ? [X3] :
          ( r4_lattice3(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK16(X0,X1,X2),X0)
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f267,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X0,X1,sK14(X2,X3,a_2_2_lattice3(X1,X0)))
      | sP3(X2,X3,a_2_2_lattice3(X1,X0))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f170,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( sP8(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( sP8(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f23,f37,f36])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> sP7(X2,X1,X0) )
      | ~ sP8(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

fof(f170,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP8(sK14(X2,X3,a_2_2_lattice3(X1,X0)),X1,X0)
      | sP7(X0,X1,sK14(X2,X3,a_2_2_lattice3(X1,X0)))
      | sP3(X2,X3,a_2_2_lattice3(X1,X0)) ) ),
    inference(resolution,[],[f105,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK14(X0,X1,X2),X2)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK14(X0,X1,X2))
          & r2_hidden(sK14(X0,X1,X2),X2)
          & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f56,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK14(X0,X1,X2))
        & r2_hidden(sK14(X0,X1,X2),X2)
        & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X1,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X1,X3)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | sP7(X2,X1,X0)
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ~ sP7(X2,X1,X0) )
        & ( sP7(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ sP8(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f252,plain,(
    ! [X4,X5,X3] :
      ( ~ r4_lattice3(X3,sK14(k15_lattice3(X3,X4),X3,X5),X4)
      | ~ l3_lattices(X3)
      | ~ v4_lattice3(X3)
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | sP3(k15_lattice3(X3,X4),X3,X5) ) ),
    inference(subsumption_resolution,[],[f247,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f247,plain,(
    ! [X4,X5,X3] :
      ( v2_struct_0(X3)
      | ~ l3_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ r4_lattice3(X3,sK14(k15_lattice3(X3,X4),X3,X5),X4)
      | ~ m1_subset_1(sK14(k15_lattice3(X3,X4),X3,X5),u1_struct_0(X3))
      | ~ v10_lattices(X3)
      | sP3(k15_lattice3(X3,X4),X3,X5) ) ),
    inference(resolution,[],[f209,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,sK14(X0,X1,X2))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f209,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X2),X1)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v10_lattices(X0) ) ),
    inference(resolution,[],[f202,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r4_lattice3(X1,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK13(X0,X1,X2))
          & r4_lattice3(X1,sK13(X0,X1,X2),X2)
          & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r4_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK13(X0,X1,X2))
        & r4_lattice3(X1,sK13(X0,X1,X2),X2)
        & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r4_lattice3(X1,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_lattices(X0,X2,X3)
            & r4_lattice3(X0,X3,X1)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X2,X3)
            | ~ r4_lattice3(X0,X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ! [X3] :
          ( r1_lattices(X0,X2,X3)
          | ~ r4_lattice3(X0,X3,X1)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f202,plain,(
    ! [X0,X1] :
      ( sP0(k15_lattice3(X0,X1),X0,X1)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0) ) ),
    inference(resolution,[],[f201,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ~ sP0(X2,X1,X0)
        | ~ r4_lattice3(X1,X2,X0) )
      & ( ( sP0(X2,X1,X0)
          & r4_lattice3(X1,X2,X0) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ~ sP0(X2,X0,X1)
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( sP0(X2,X0,X1)
          & r4_lattice3(X0,X2,X1) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ~ sP0(X2,X0,X1)
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( sP0(X2,X0,X1)
          & r4_lattice3(X0,X2,X1) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ( sP0(X2,X0,X1)
        & r4_lattice3(X0,X2,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f201,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0,k15_lattice3(X0,X1))
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f196,f104])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP1(X1,X0,k15_lattice3(X0,X1)) ) ),
    inference(resolution,[],[f122,f119])).

fof(f119,plain,(
    ! [X2,X1] :
      ( ~ sP2(k15_lattice3(X1,X2),X1,X2)
      | sP1(X2,X1,k15_lattice3(X1,X2)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | k15_lattice3(X1,X2) != X0
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( k15_lattice3(X1,X2) = X0
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | k15_lattice3(X1,X2) != X0 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ( ( k15_lattice3(X0,X1) = X2
          | ~ sP1(X1,X0,X2) )
        & ( sP1(X1,X0,X2)
          | k15_lattice3(X0,X1) != X2 ) )
      | ~ sP2(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ( k15_lattice3(X0,X1) = X2
      <=> sP1(X1,X0,X2) )
      | ~ sP2(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP2(X2,X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f13,f28,f27,f26])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f1045,plain,(
    ! [X0] :
      ( ~ r3_lattice3(sK11,X0,a_2_2_lattice3(sK11,sK12))
      | k15_lattice3(sK11,sK12) != X0
      | ~ r2_hidden(X0,a_2_2_lattice3(sK11,sK12))
      | ~ m1_subset_1(X0,u1_struct_0(sK11)) ) ),
    inference(resolution,[],[f1044,f121])).

fof(f121,plain,(
    ! [X0,X3,X1] :
      ( sP9(X0,X1,X3)
      | ~ r3_lattice3(X1,X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( sP9(X0,X1,X2)
      | ~ r3_lattice3(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( sP9(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r3_lattice3(X1,sK17(X0,X1,X2),X0)
          & sK17(X0,X1,X2) = X2
          & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP9(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f71,f72])).

fof(f72,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK17(X0,X1,X2),X0)
        & sK17(X0,X1,X2) = X2
        & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( sP9(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r3_lattice3(X1,X4,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP9(X0,X1,X2) ) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X2,X1,X0] :
      ( ( sP9(X2,X1,X0)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP9(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( sP9(X2,X1,X0)
    <=> ? [X3] :
          ( r3_lattice3(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f1044,plain,(
    ! [X0] :
      ( ~ sP9(a_2_2_lattice3(sK11,sK12),sK11,X0)
      | ~ r2_hidden(X0,a_2_2_lattice3(sK11,sK12))
      | k15_lattice3(sK11,sK12) != X0 ) ),
    inference(subsumption_resolution,[],[f1043,f76])).

fof(f1043,plain,(
    ! [X0] :
      ( k15_lattice3(sK11,sK12) != X0
      | ~ v4_lattice3(sK11)
      | ~ r2_hidden(X0,a_2_2_lattice3(sK11,sK12))
      | ~ sP9(a_2_2_lattice3(sK11,sK12),sK11,X0) ) ),
    inference(subsumption_resolution,[],[f1042,f77])).

fof(f1042,plain,(
    ! [X0] :
      ( k15_lattice3(sK11,sK12) != X0
      | ~ l3_lattices(sK11)
      | ~ v4_lattice3(sK11)
      | ~ r2_hidden(X0,a_2_2_lattice3(sK11,sK12))
      | ~ sP9(a_2_2_lattice3(sK11,sK12),sK11,X0) ) ),
    inference(subsumption_resolution,[],[f1041,f74])).

fof(f1041,plain,(
    ! [X0] :
      ( k15_lattice3(sK11,sK12) != X0
      | v2_struct_0(sK11)
      | ~ l3_lattices(sK11)
      | ~ v4_lattice3(sK11)
      | ~ r2_hidden(X0,a_2_2_lattice3(sK11,sK12))
      | ~ sP9(a_2_2_lattice3(sK11,sK12),sK11,X0) ) ),
    inference(subsumption_resolution,[],[f967,f75])).

fof(f967,plain,(
    ! [X0] :
      ( k15_lattice3(sK11,sK12) != X0
      | ~ v10_lattices(sK11)
      | v2_struct_0(sK11)
      | ~ l3_lattices(sK11)
      | ~ v4_lattice3(sK11)
      | ~ r2_hidden(X0,a_2_2_lattice3(sK11,sK12))
      | ~ sP9(a_2_2_lattice3(sK11,sK12),sK11,X0) ) ),
    inference(superposition,[],[f78,f963])).

fof(f963,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X1,X2) = X0
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ r2_hidden(X0,X2)
      | ~ sP9(X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f962,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( sP10(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( sP10(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f25,f40,f39])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> sP9(X2,X1,X0) )
      | ~ sP10(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

fof(f962,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | k16_lattice3(X1,X2) = X0
      | ~ r2_hidden(X0,X2)
      | ~ sP9(X2,X1,X0)
      | ~ sP10(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f959,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ sP9(X0,X1,X2)
      | m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X1))
      | ~ sP9(X0,X1,X2)
      | ~ sP9(X0,X1,X2) ) ),
    inference(superposition,[],[f114,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( sK17(X0,X1,X2) = X2
      | ~ sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1))
      | ~ sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f959,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | k16_lattice3(X1,X2) = X0
      | ~ r2_hidden(X0,X2)
      | ~ sP9(X2,X1,X0)
      | ~ sP10(X0,X1,X2) ) ),
    inference(resolution,[],[f953,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ sP9(X2,X1,X0)
      | ~ sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ~ sP9(X2,X1,X0) )
        & ( sP9(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ sP10(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f953,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,a_2_1_lattice3(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | k16_lattice3(X0,X1) = X2
      | ~ r2_hidden(X2,X1) ) ),
    inference(duplicate_literal_removal,[],[f940])).

fof(f940,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X1) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ r2_hidden(X2,a_2_1_lattice3(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f645,f329])).

fof(f329,plain,(
    ! [X6,X4,X5] :
      ( r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6))
      | ~ r2_hidden(X4,X6)
      | ~ l3_lattices(X5)
      | v2_struct_0(X5)
      | ~ m1_subset_1(X4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f328,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP6(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP6(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f19,f34,f33])).

fof(f33,plain,(
    ! [X1,X0,X2] :
      ( sP5(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X3,X1)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r4_lattice3(X0,X1,X2)
        <=> sP5(X1,X0,X2) )
      | ~ sP6(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f328,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ r2_hidden(X4,X6)
      | ~ l3_lattices(X5)
      | v2_struct_0(X5)
      | r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6))
      | ~ sP6(X5,X4) ) ),
    inference(resolution,[],[f326,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X1,X0,X2)
      | r4_lattice3(X0,X1,X2)
      | ~ sP6(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X0,X1,X2)
            | ~ sP5(X1,X0,X2) )
          & ( sP5(X1,X0,X2)
            | ~ r4_lattice3(X0,X1,X2) ) )
      | ~ sP6(X0,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f326,plain,(
    ! [X2,X0,X1] :
      ( sP5(X0,X2,a_2_1_lattice3(X2,X1))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f325,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( sP4(X1,sK15(X0,X1,X2))
      | sP5(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f100,f96])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))
      | sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ( ~ r1_lattices(X1,sK15(X0,X1,X2),X0)
          & r2_hidden(sK15(X0,X1,X2),X2)
          & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,sK15(X0,X1,X2),X0)
        & r2_hidden(sK15(X0,X1,X2),X2)
        & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X3,X0)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X1,X0,X2] :
      ( ( sP5(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X3,X1)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X3,X1)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP5(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f325,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ sP4(X2,sK15(X0,X2,a_2_1_lattice3(X2,X1)))
      | sP5(X0,X2,a_2_1_lattice3(X2,X1))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f324])).

fof(f324,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ sP4(X2,sK15(X0,X2,a_2_1_lattice3(X2,X1)))
      | sP5(X0,X2,a_2_1_lattice3(X2,X1))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | sP5(X0,X2,a_2_1_lattice3(X2,X1)) ) ),
    inference(resolution,[],[f221,f316])).

fof(f316,plain,(
    ! [X10,X8,X11,X9] :
      ( r3_lattice3(X10,sK15(X8,X9,a_2_1_lattice3(X10,X11)),X11)
      | ~ l3_lattices(X10)
      | v2_struct_0(X10)
      | sP5(X8,X9,a_2_1_lattice3(X10,X11)) ) ),
    inference(resolution,[],[f313,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ sP9(X0,X1,X2)
      | r3_lattice3(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,X2,X0)
      | ~ sP9(X0,X1,X2)
      | ~ sP9(X0,X1,X2) ) ),
    inference(superposition,[],[f116,f115])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK17(X0,X1,X2),X0)
      | ~ sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f313,plain,(
    ! [X2,X0,X3,X1] :
      ( sP9(X0,X1,sK15(X2,X3,a_2_1_lattice3(X1,X0)))
      | sP5(X2,X3,a_2_1_lattice3(X1,X0))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f179,f118])).

fof(f179,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ sP10(sK15(X6,X7,a_2_1_lattice3(X5,X4)),X5,X4)
      | sP9(X4,X5,sK15(X6,X7,a_2_1_lattice3(X5,X4)))
      | sP5(X6,X7,a_2_1_lattice3(X5,X4)) ) ),
    inference(resolution,[],[f112,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK15(X0,X1,X2),X2)
      | sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | sP9(X2,X1,X0)
      | ~ sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f221,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r3_lattice3(X9,sK15(X8,X9,X11),X10)
      | ~ r2_hidden(X8,X10)
      | ~ m1_subset_1(X8,u1_struct_0(X9))
      | ~ sP4(X9,sK15(X8,X9,X11))
      | sP5(X8,X9,X11) ) ),
    inference(resolution,[],[f182,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,sK15(X0,X1,X2),X0)
      | sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f182,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X2,X3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ r3_lattice3(X2,X3,X1)
      | ~ sP4(X2,X3) ) ),
    inference(resolution,[],[f92,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0,X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f92,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f645,plain,(
    ! [X6,X4,X5] :
      ( ~ r4_lattice3(X4,X6,a_2_1_lattice3(X4,X5))
      | k16_lattice3(X4,X5) = X6
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ v4_lattice3(X4)
      | ~ v10_lattices(X4)
      | v2_struct_0(X4)
      | ~ l3_lattices(X4)
      | ~ r2_hidden(X6,a_2_1_lattice3(X4,X5)) ) ),
    inference(duplicate_literal_removal,[],[f644])).

fof(f644,plain,(
    ! [X6,X4,X5] :
      ( ~ l3_lattices(X4)
      | k16_lattice3(X4,X5) = X6
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ v4_lattice3(X4)
      | ~ v10_lattices(X4)
      | v2_struct_0(X4)
      | ~ r4_lattice3(X4,X6,a_2_1_lattice3(X4,X5))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ r2_hidden(X6,a_2_1_lattice3(X4,X5))
      | ~ l3_lattices(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f271,f362])).

fof(f362,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f361])).

fof(f361,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | sP0(X0,X2,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | sP0(X0,X2,X1) ) ),
    inference(resolution,[],[f359,f133])).

fof(f133,plain,(
    ! [X4,X2,X3] :
      ( sP6(X2,sK13(X3,X2,X4))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | sP0(X3,X2,X4) ) ),
    inference(resolution,[],[f103,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f359,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X1,sK13(X0,X1,X2))
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f357])).

fof(f357,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X2)
      | ~ sP6(X1,sK13(X0,X1,X2))
      | sP0(X0,X1,X2)
      | sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f232,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,sK13(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f232,plain,(
    ! [X6,X8,X7,X9] :
      ( r1_lattices(X7,X6,sK13(X8,X7,X9))
      | ~ m1_subset_1(X6,u1_struct_0(X7))
      | ~ r2_hidden(X6,X9)
      | ~ sP6(X7,sK13(X8,X7,X9))
      | sP0(X8,X7,X9) ) ),
    inference(resolution,[],[f183,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK13(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f183,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_lattice3(X2,X3,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | r1_lattices(X2,X0,X3)
      | ~ r2_hidden(X0,X1)
      | ~ sP6(X2,X3) ) ),
    inference(resolution,[],[f99,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( sP5(X1,X0,X2)
      | ~ r4_lattice3(X0,X1,X2)
      | ~ sP6(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f99,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f271,plain,(
    ! [X4,X2,X3] :
      ( ~ sP0(X4,X2,a_2_1_lattice3(X2,X3))
      | ~ l3_lattices(X2)
      | k16_lattice3(X2,X3) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ r4_lattice3(X2,X4,a_2_1_lattice3(X2,X3)) ) ),
    inference(resolution,[],[f240,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | ~ r4_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f240,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(a_2_1_lattice3(X0,X1),X0,X2)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | k16_lattice3(X0,X1) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f239])).

fof(f239,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ sP1(a_2_1_lattice3(X0,X1),X0,X2)
      | k16_lattice3(X0,X1) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f161,f122])).

fof(f161,plain,(
    ! [X4,X2,X3] :
      ( ~ sP2(X4,X2,a_2_1_lattice3(X2,X3))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | ~ sP1(a_2_1_lattice3(X2,X3),X2,X4)
      | k16_lattice3(X2,X3) = X4 ) ),
    inference(superposition,[],[f89,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X1,X2) = X0
      | ~ sP1(X2,X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d22_lattice3)).

fof(f78,plain,(
    k15_lattice3(sK11,sK12) != k16_lattice3(sK11,a_2_2_lattice3(sK11,sK12)) ),
    inference(cnf_transformation,[],[f44])).

fof(f1165,plain,(
    spl18_7 ),
    inference(avatar_contradiction_clause,[],[f1164])).

fof(f1164,plain,
    ( $false
    | spl18_7 ),
    inference(subsumption_resolution,[],[f1163,f76])).

fof(f1163,plain,
    ( ~ v4_lattice3(sK11)
    | spl18_7 ),
    inference(subsumption_resolution,[],[f1162,f77])).

fof(f1162,plain,
    ( ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | spl18_7 ),
    inference(subsumption_resolution,[],[f1161,f74])).

fof(f1161,plain,
    ( v2_struct_0(sK11)
    | ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | spl18_7 ),
    inference(subsumption_resolution,[],[f1156,f75])).

fof(f1156,plain,
    ( ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | spl18_7 ),
    inference(resolution,[],[f1119,f203])).

fof(f203,plain,(
    ! [X2,X3] :
      ( r4_lattice3(X2,k15_lattice3(X2,X3),X3)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2) ) ),
    inference(resolution,[],[f201,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | r4_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1119,plain,
    ( ~ r4_lattice3(sK11,k15_lattice3(sK11,sK12),sK12)
    | spl18_7 ),
    inference(avatar_component_clause,[],[f1117])).

fof(f1117,plain,
    ( spl18_7
  <=> r4_lattice3(sK11,k15_lattice3(sK11,sK12),sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_7])])).

fof(f1139,plain,(
    spl18_6 ),
    inference(avatar_contradiction_clause,[],[f1138])).

fof(f1138,plain,
    ( $false
    | spl18_6 ),
    inference(subsumption_resolution,[],[f1137,f74])).

fof(f1137,plain,
    ( v2_struct_0(sK11)
    | spl18_6 ),
    inference(subsumption_resolution,[],[f1131,f77])).

fof(f1131,plain,
    ( ~ l3_lattices(sK11)
    | v2_struct_0(sK11)
    | spl18_6 ),
    inference(resolution,[],[f1115,f104])).

fof(f1115,plain,
    ( ~ m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11))
    | spl18_6 ),
    inference(avatar_component_clause,[],[f1113])).

fof(f1120,plain,
    ( ~ spl18_6
    | ~ spl18_7
    | spl18_5 ),
    inference(avatar_split_clause,[],[f1108,f1076,f1117,f1113])).

fof(f1076,plain,
    ( spl18_5
  <=> sP7(sK12,sK11,k15_lattice3(sK11,sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_5])])).

fof(f1108,plain,
    ( ~ r4_lattice3(sK11,k15_lattice3(sK11,sK12),sK12)
    | ~ m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11))
    | spl18_5 ),
    inference(resolution,[],[f1078,f120])).

fof(f120,plain,(
    ! [X0,X3,X1] :
      ( sP7(X0,X1,X3)
      | ~ r4_lattice3(X1,X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X0,X1,X2)
      | ~ r4_lattice3(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1078,plain,
    ( ~ sP7(sK12,sK11,k15_lattice3(sK11,sK12))
    | spl18_5 ),
    inference(avatar_component_clause,[],[f1076])).

fof(f1096,plain,(
    spl18_4 ),
    inference(avatar_contradiction_clause,[],[f1095])).

fof(f1095,plain,
    ( $false
    | spl18_4 ),
    inference(subsumption_resolution,[],[f1094,f74])).

fof(f1094,plain,
    ( v2_struct_0(sK11)
    | spl18_4 ),
    inference(subsumption_resolution,[],[f1093,f75])).

fof(f1093,plain,
    ( ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | spl18_4 ),
    inference(subsumption_resolution,[],[f1092,f76])).

fof(f1092,plain,
    ( ~ v4_lattice3(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | spl18_4 ),
    inference(subsumption_resolution,[],[f1088,f77])).

fof(f1088,plain,
    ( ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | spl18_4 ),
    inference(resolution,[],[f1074,f111])).

fof(f1074,plain,
    ( ~ sP8(k15_lattice3(sK11,sK12),sK11,sK12)
    | spl18_4 ),
    inference(avatar_component_clause,[],[f1072])).

fof(f1072,plain,
    ( spl18_4
  <=> sP8(k15_lattice3(sK11,sK12),sK11,sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).

fof(f1079,plain,
    ( ~ spl18_4
    | ~ spl18_5
    | spl18_2 ),
    inference(avatar_split_clause,[],[f1067,f1055,f1076,f1072])).

fof(f1067,plain,
    ( ~ sP7(sK12,sK11,k15_lattice3(sK11,sK12))
    | ~ sP8(k15_lattice3(sK11,sK12),sK11,sK12)
    | spl18_2 ),
    inference(resolution,[],[f1057,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ sP7(X2,X1,X0)
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f1057,plain,
    ( ~ r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12))
    | spl18_2 ),
    inference(avatar_component_clause,[],[f1055])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:39:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (25321)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (25312)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (25327)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (25314)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (25311)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (25320)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (25313)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (25330)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (25328)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (25319)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (25324)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (25325)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (25315)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (25310)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (25329)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (25316)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (25309)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (25332)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (25334)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.53  % (25331)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (25309)Refutation not found, incomplete strategy% (25309)------------------------------
% 0.21/0.53  % (25309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (25309)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (25309)Memory used [KB]: 10746
% 0.21/0.53  % (25309)Time elapsed: 0.101 s
% 0.21/0.53  % (25309)------------------------------
% 0.21/0.53  % (25309)------------------------------
% 0.21/0.53  % (25316)Refutation not found, incomplete strategy% (25316)------------------------------
% 0.21/0.53  % (25316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (25316)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (25316)Memory used [KB]: 1663
% 0.21/0.53  % (25316)Time elapsed: 0.077 s
% 0.21/0.53  % (25316)------------------------------
% 0.21/0.53  % (25316)------------------------------
% 0.21/0.53  % (25317)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (25333)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (25323)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (25326)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.54  % (25322)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (25318)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.80/0.63  % (25313)Refutation found. Thanks to Tanya!
% 1.80/0.63  % SZS status Theorem for theBenchmark
% 1.80/0.63  % SZS output start Proof for theBenchmark
% 1.80/0.63  fof(f1564,plain,(
% 1.80/0.63    $false),
% 1.80/0.63    inference(avatar_sat_refutation,[],[f1079,f1096,f1120,f1139,f1165,f1541])).
% 1.80/0.63  fof(f1541,plain,(
% 1.80/0.63    ~spl18_2 | ~spl18_6),
% 1.80/0.63    inference(avatar_contradiction_clause,[],[f1540])).
% 1.80/0.63  fof(f1540,plain,(
% 1.80/0.63    $false | (~spl18_2 | ~spl18_6)),
% 1.80/0.63    inference(subsumption_resolution,[],[f1539,f76])).
% 1.80/0.63  fof(f76,plain,(
% 1.80/0.63    v4_lattice3(sK11)),
% 1.80/0.63    inference(cnf_transformation,[],[f44])).
% 1.80/0.63  fof(f44,plain,(
% 1.80/0.63    k15_lattice3(sK11,sK12) != k16_lattice3(sK11,a_2_2_lattice3(sK11,sK12)) & l3_lattices(sK11) & v4_lattice3(sK11) & v10_lattices(sK11) & ~v2_struct_0(sK11)),
% 1.80/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f11,f43,f42])).
% 1.80/0.63  fof(f42,plain,(
% 1.80/0.63    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : k15_lattice3(sK11,X1) != k16_lattice3(sK11,a_2_2_lattice3(sK11,X1)) & l3_lattices(sK11) & v4_lattice3(sK11) & v10_lattices(sK11) & ~v2_struct_0(sK11))),
% 1.80/0.63    introduced(choice_axiom,[])).
% 1.80/0.63  fof(f43,plain,(
% 1.80/0.63    ? [X1] : k15_lattice3(sK11,X1) != k16_lattice3(sK11,a_2_2_lattice3(sK11,X1)) => k15_lattice3(sK11,sK12) != k16_lattice3(sK11,a_2_2_lattice3(sK11,sK12))),
% 1.80/0.63    introduced(choice_axiom,[])).
% 1.80/0.63  fof(f11,plain,(
% 1.80/0.63    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.80/0.63    inference(flattening,[],[f10])).
% 1.80/0.63  fof(f10,plain,(
% 1.80/0.63    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.80/0.63    inference(ennf_transformation,[],[f9])).
% 1.80/0.63  fof(f9,negated_conjecture,(
% 1.80/0.63    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 1.80/0.63    inference(negated_conjecture,[],[f8])).
% 1.80/0.63  fof(f8,conjecture,(
% 1.80/0.63    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 1.80/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).
% 1.80/0.63  fof(f1539,plain,(
% 1.80/0.63    ~v4_lattice3(sK11) | (~spl18_2 | ~spl18_6)),
% 1.80/0.63    inference(subsumption_resolution,[],[f1538,f77])).
% 1.80/0.63  fof(f77,plain,(
% 1.80/0.63    l3_lattices(sK11)),
% 1.80/0.63    inference(cnf_transformation,[],[f44])).
% 1.80/0.63  fof(f1538,plain,(
% 1.80/0.63    ~l3_lattices(sK11) | ~v4_lattice3(sK11) | (~spl18_2 | ~spl18_6)),
% 1.80/0.63    inference(subsumption_resolution,[],[f1537,f75])).
% 1.80/0.63  fof(f75,plain,(
% 1.80/0.63    v10_lattices(sK11)),
% 1.80/0.63    inference(cnf_transformation,[],[f44])).
% 1.80/0.63  fof(f1537,plain,(
% 1.80/0.63    ~v10_lattices(sK11) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | (~spl18_2 | ~spl18_6)),
% 1.80/0.63    inference(subsumption_resolution,[],[f1536,f74])).
% 1.80/0.63  fof(f74,plain,(
% 1.80/0.63    ~v2_struct_0(sK11)),
% 1.80/0.63    inference(cnf_transformation,[],[f44])).
% 1.80/0.63  fof(f1536,plain,(
% 1.80/0.63    v2_struct_0(sK11) | ~v10_lattices(sK11) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | (~spl18_2 | ~spl18_6)),
% 1.80/0.63    inference(subsumption_resolution,[],[f1535,f1114])).
% 1.80/0.63  fof(f1114,plain,(
% 1.80/0.63    m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11)) | ~spl18_6),
% 1.80/0.63    inference(avatar_component_clause,[],[f1113])).
% 1.80/0.63  fof(f1113,plain,(
% 1.80/0.63    spl18_6 <=> m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11))),
% 1.80/0.63    introduced(avatar_definition,[new_symbols(naming,[spl18_6])])).
% 1.80/0.63  fof(f1535,plain,(
% 1.80/0.63    ~m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11)) | v2_struct_0(sK11) | ~v10_lattices(sK11) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~spl18_2),
% 1.80/0.63    inference(subsumption_resolution,[],[f1510,f1056])).
% 1.80/0.63  fof(f1056,plain,(
% 1.80/0.63    r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12)) | ~spl18_2),
% 1.80/0.63    inference(avatar_component_clause,[],[f1055])).
% 1.80/0.63  fof(f1055,plain,(
% 1.80/0.63    spl18_2 <=> r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12))),
% 1.80/0.63    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).
% 1.80/0.63  fof(f1510,plain,(
% 1.80/0.63    ~r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12)) | ~m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11)) | v2_struct_0(sK11) | ~v10_lattices(sK11) | ~l3_lattices(sK11) | ~v4_lattice3(sK11)),
% 1.80/0.63    inference(trivial_inequality_removal,[],[f1504])).
% 1.80/0.63  fof(f1504,plain,(
% 1.80/0.63    k15_lattice3(sK11,sK12) != k15_lattice3(sK11,sK12) | ~r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12)) | ~m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11)) | v2_struct_0(sK11) | ~v10_lattices(sK11) | ~l3_lattices(sK11) | ~v4_lattice3(sK11)),
% 1.80/0.63    inference(resolution,[],[f1045,f353])).
% 1.80/0.63  fof(f353,plain,(
% 1.80/0.63    ( ! [X4,X3] : (r3_lattice3(X3,k15_lattice3(X3,X4),a_2_2_lattice3(X3,X4)) | v2_struct_0(X3) | ~v10_lattices(X3) | ~l3_lattices(X3) | ~v4_lattice3(X3)) )),
% 1.80/0.63    inference(subsumption_resolution,[],[f349,f128])).
% 1.80/0.63  fof(f128,plain,(
% 1.80/0.63    ( ! [X0,X1] : (sP4(X0,k15_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.80/0.63    inference(duplicate_literal_removal,[],[f125])).
% 1.80/0.63  fof(f125,plain,(
% 1.80/0.63    ( ! [X0,X1] : (sP4(X0,k15_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.80/0.63    inference(resolution,[],[f96,f104])).
% 1.80/0.63  fof(f104,plain,(
% 1.80/0.63    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f21])).
% 1.80/0.63  fof(f21,plain,(
% 1.80/0.63    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.80/0.63    inference(flattening,[],[f20])).
% 1.80/0.63  fof(f20,plain,(
% 1.80/0.63    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.80/0.63    inference(ennf_transformation,[],[f5])).
% 1.80/0.63  fof(f5,axiom,(
% 1.80/0.63    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.80/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 1.80/0.63  fof(f96,plain,(
% 1.80/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP4(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f32])).
% 1.80/0.63  fof(f32,plain,(
% 1.80/0.63    ! [X0] : (! [X1] : (sP4(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.80/0.63    inference(definition_folding,[],[f17,f31,f30])).
% 1.80/0.63  fof(f30,plain,(
% 1.80/0.63    ! [X1,X0,X2] : (sP3(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 1.80/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.80/0.63  fof(f31,plain,(
% 1.80/0.63    ! [X0,X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> sP3(X1,X0,X2)) | ~sP4(X0,X1))),
% 1.80/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.80/0.63  fof(f17,plain,(
% 1.80/0.63    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.80/0.63    inference(flattening,[],[f16])).
% 1.80/0.63  fof(f16,plain,(
% 1.80/0.63    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.80/0.63    inference(ennf_transformation,[],[f1])).
% 1.80/0.63  fof(f1,axiom,(
% 1.80/0.63    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 1.80/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
% 1.80/0.63  fof(f349,plain,(
% 1.80/0.63    ( ! [X4,X3] : (~v4_lattice3(X3) | v2_struct_0(X3) | ~v10_lattices(X3) | ~l3_lattices(X3) | r3_lattice3(X3,k15_lattice3(X3,X4),a_2_2_lattice3(X3,X4)) | ~sP4(X3,k15_lattice3(X3,X4))) )),
% 1.80/0.63    inference(resolution,[],[f346,f91])).
% 1.80/0.63  fof(f91,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~sP3(X1,X0,X2) | r3_lattice3(X0,X1,X2) | ~sP4(X0,X1)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f54])).
% 1.80/0.63  fof(f54,plain,(
% 1.80/0.63    ! [X0,X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ~sP3(X1,X0,X2)) & (sP3(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) | ~sP4(X0,X1))),
% 1.80/0.63    inference(nnf_transformation,[],[f31])).
% 1.80/0.63  fof(f346,plain,(
% 1.80/0.63    ( ! [X0,X1] : (sP3(k15_lattice3(X0,X1),X0,a_2_2_lattice3(X0,X1)) | ~v4_lattice3(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.80/0.63    inference(duplicate_literal_removal,[],[f340])).
% 1.80/0.63  fof(f340,plain,(
% 1.80/0.63    ( ! [X0,X1] : (~l3_lattices(X0) | ~v4_lattice3(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | sP3(k15_lattice3(X0,X1),X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP3(k15_lattice3(X0,X1),X0,a_2_2_lattice3(X0,X1))) )),
% 1.80/0.63    inference(resolution,[],[f252,f277])).
% 1.80/0.63  fof(f277,plain,(
% 1.80/0.63    ( ! [X10,X8,X11,X9] : (r4_lattice3(X10,sK14(X8,X9,a_2_2_lattice3(X10,X11)),X11) | ~l3_lattices(X10) | ~v4_lattice3(X10) | ~v10_lattices(X10) | v2_struct_0(X10) | sP3(X8,X9,a_2_2_lattice3(X10,X11))) )),
% 1.80/0.63    inference(resolution,[],[f267,f142])).
% 1.80/0.63  fof(f142,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~sP7(X0,X1,X2) | r4_lattice3(X1,X2,X0)) )),
% 1.80/0.63    inference(duplicate_literal_removal,[],[f141])).
% 1.80/0.63  fof(f141,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (r4_lattice3(X1,X2,X0) | ~sP7(X0,X1,X2) | ~sP7(X0,X1,X2)) )),
% 1.80/0.63    inference(superposition,[],[f109,f108])).
% 1.80/0.63  fof(f108,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (sK16(X0,X1,X2) = X2 | ~sP7(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f68])).
% 1.80/0.63  fof(f68,plain,(
% 1.80/0.63    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | ! [X3] : (~r4_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK16(X0,X1,X2),X0) & sK16(X0,X1,X2) = X2 & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 1.80/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f66,f67])).
% 1.80/0.63  fof(f67,plain,(
% 1.80/0.63    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK16(X0,X1,X2),X0) & sK16(X0,X1,X2) = X2 & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1))))),
% 1.80/0.63    introduced(choice_axiom,[])).
% 1.80/0.63  fof(f66,plain,(
% 1.80/0.63    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | ! [X3] : (~r4_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 1.80/0.63    inference(rectify,[],[f65])).
% 1.80/0.63  fof(f65,plain,(
% 1.80/0.63    ! [X2,X1,X0] : ((sP7(X2,X1,X0) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP7(X2,X1,X0)))),
% 1.80/0.63    inference(nnf_transformation,[],[f36])).
% 1.80/0.63  fof(f36,plain,(
% 1.80/0.63    ! [X2,X1,X0] : (sP7(X2,X1,X0) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 1.80/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 1.80/0.63  fof(f109,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK16(X0,X1,X2),X0) | ~sP7(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f68])).
% 1.80/0.63  fof(f267,plain,(
% 1.80/0.63    ( ! [X2,X0,X3,X1] : (sP7(X0,X1,sK14(X2,X3,a_2_2_lattice3(X1,X0))) | sP3(X2,X3,a_2_2_lattice3(X1,X0)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.80/0.63    inference(resolution,[],[f170,f111])).
% 1.80/0.63  fof(f111,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (sP8(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f38])).
% 1.80/0.63  fof(f38,plain,(
% 1.80/0.63    ! [X0,X1,X2] : (sP8(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.80/0.63    inference(definition_folding,[],[f23,f37,f36])).
% 1.80/0.63  fof(f37,plain,(
% 1.80/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> sP7(X2,X1,X0)) | ~sP8(X0,X1,X2))),
% 1.80/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 1.80/0.63  fof(f23,plain,(
% 1.80/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.80/0.63    inference(flattening,[],[f22])).
% 1.80/0.63  fof(f22,plain,(
% 1.80/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 1.80/0.63    inference(ennf_transformation,[],[f7])).
% 1.80/0.63  fof(f7,axiom,(
% 1.80/0.63    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.80/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).
% 1.80/0.63  fof(f170,plain,(
% 1.80/0.63    ( ! [X2,X0,X3,X1] : (~sP8(sK14(X2,X3,a_2_2_lattice3(X1,X0)),X1,X0) | sP7(X0,X1,sK14(X2,X3,a_2_2_lattice3(X1,X0))) | sP3(X2,X3,a_2_2_lattice3(X1,X0))) )),
% 1.80/0.63    inference(resolution,[],[f105,f94])).
% 1.80/0.63  fof(f94,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK14(X0,X1,X2),X2) | sP3(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f58])).
% 1.80/0.63  fof(f58,plain,(
% 1.80/0.63    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | (~r1_lattices(X1,X0,sK14(X0,X1,X2)) & r2_hidden(sK14(X0,X1,X2),X2) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 1.80/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f56,f57])).
% 1.80/0.63  fof(f57,plain,(
% 1.80/0.63    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK14(X0,X1,X2)) & r2_hidden(sK14(X0,X1,X2),X2) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1))))),
% 1.80/0.63    introduced(choice_axiom,[])).
% 1.80/0.63  fof(f56,plain,(
% 1.80/0.63    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 1.80/0.63    inference(rectify,[],[f55])).
% 1.80/0.63  fof(f55,plain,(
% 1.80/0.63    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP3(X1,X0,X2)))),
% 1.80/0.63    inference(nnf_transformation,[],[f30])).
% 1.80/0.63  fof(f105,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | sP7(X2,X1,X0) | ~sP8(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f64])).
% 1.80/0.63  fof(f64,plain,(
% 1.80/0.63    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~sP7(X2,X1,X0)) & (sP7(X2,X1,X0) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~sP8(X0,X1,X2))),
% 1.80/0.63    inference(nnf_transformation,[],[f37])).
% 1.80/0.63  fof(f252,plain,(
% 1.80/0.63    ( ! [X4,X5,X3] : (~r4_lattice3(X3,sK14(k15_lattice3(X3,X4),X3,X5),X4) | ~l3_lattices(X3) | ~v4_lattice3(X3) | v2_struct_0(X3) | ~v10_lattices(X3) | sP3(k15_lattice3(X3,X4),X3,X5)) )),
% 1.80/0.63    inference(subsumption_resolution,[],[f247,f93])).
% 1.80/0.63  fof(f93,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) | sP3(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f58])).
% 1.80/0.63  fof(f247,plain,(
% 1.80/0.63    ( ! [X4,X5,X3] : (v2_struct_0(X3) | ~l3_lattices(X3) | ~v4_lattice3(X3) | ~r4_lattice3(X3,sK14(k15_lattice3(X3,X4),X3,X5),X4) | ~m1_subset_1(sK14(k15_lattice3(X3,X4),X3,X5),u1_struct_0(X3)) | ~v10_lattices(X3) | sP3(k15_lattice3(X3,X4),X3,X5)) )),
% 1.80/0.63    inference(resolution,[],[f209,f95])).
% 1.80/0.63  fof(f95,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~r1_lattices(X1,X0,sK14(X0,X1,X2)) | sP3(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f58])).
% 1.80/0.63  fof(f209,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X2),X1) | v2_struct_0(X0) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v10_lattices(X0)) )),
% 1.80/0.63    inference(resolution,[],[f202,f84])).
% 1.80/0.63  fof(f84,plain,(
% 1.80/0.63    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f53])).
% 1.80/0.63  fof(f53,plain,(
% 1.80/0.63    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r1_lattices(X1,X0,sK13(X0,X1,X2)) & r4_lattice3(X1,sK13(X0,X1,X2),X2) & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 1.80/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f51,f52])).
% 1.80/0.63  fof(f52,plain,(
% 1.80/0.63    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK13(X0,X1,X2)) & r4_lattice3(X1,sK13(X0,X1,X2),X2) & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))))),
% 1.80/0.63    introduced(choice_axiom,[])).
% 1.80/0.63  fof(f51,plain,(
% 1.80/0.63    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 1.80/0.63    inference(rectify,[],[f50])).
% 1.80/0.63  fof(f50,plain,(
% 1.80/0.63    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X2,X0,X1)))),
% 1.80/0.63    inference(nnf_transformation,[],[f26])).
% 1.80/0.63  fof(f26,plain,(
% 1.80/0.63    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> ! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 1.80/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.80/0.63  fof(f202,plain,(
% 1.80/0.63    ( ! [X0,X1] : (sP0(k15_lattice3(X0,X1),X0,X1) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~v4_lattice3(X0)) )),
% 1.80/0.63    inference(resolution,[],[f201,f82])).
% 1.80/0.63  fof(f82,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | sP0(X2,X1,X0)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f49])).
% 1.80/0.63  fof(f49,plain,(
% 1.80/0.63    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | ~r4_lattice3(X1,X2,X0)) & ((sP0(X2,X1,X0) & r4_lattice3(X1,X2,X0)) | ~sP1(X0,X1,X2)))),
% 1.80/0.63    inference(rectify,[],[f48])).
% 1.80/0.63  fof(f48,plain,(
% 1.80/0.63    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ~sP0(X2,X0,X1) | ~r4_lattice3(X0,X2,X1)) & ((sP0(X2,X0,X1) & r4_lattice3(X0,X2,X1)) | ~sP1(X1,X0,X2)))),
% 1.80/0.63    inference(flattening,[],[f47])).
% 1.80/0.63  fof(f47,plain,(
% 1.80/0.63    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | (~sP0(X2,X0,X1) | ~r4_lattice3(X0,X2,X1))) & ((sP0(X2,X0,X1) & r4_lattice3(X0,X2,X1)) | ~sP1(X1,X0,X2)))),
% 1.80/0.63    inference(nnf_transformation,[],[f27])).
% 1.80/0.63  fof(f27,plain,(
% 1.80/0.63    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> (sP0(X2,X0,X1) & r4_lattice3(X0,X2,X1)))),
% 1.80/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.80/0.63  fof(f201,plain,(
% 1.80/0.63    ( ! [X0,X1] : (sP1(X1,X0,k15_lattice3(X0,X1)) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.80/0.63    inference(subsumption_resolution,[],[f196,f104])).
% 1.80/0.63  fof(f196,plain,(
% 1.80/0.63    ( ! [X0,X1] : (~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP1(X1,X0,k15_lattice3(X0,X1))) )),
% 1.80/0.63    inference(resolution,[],[f122,f119])).
% 1.80/0.63  fof(f119,plain,(
% 1.80/0.63    ( ! [X2,X1] : (~sP2(k15_lattice3(X1,X2),X1,X2) | sP1(X2,X1,k15_lattice3(X1,X2))) )),
% 1.80/0.63    inference(equality_resolution,[],[f79])).
% 1.80/0.63  fof(f79,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (sP1(X2,X1,X0) | k15_lattice3(X1,X2) != X0 | ~sP2(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f46])).
% 1.80/0.63  fof(f46,plain,(
% 1.80/0.63    ! [X0,X1,X2] : (((k15_lattice3(X1,X2) = X0 | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | k15_lattice3(X1,X2) != X0)) | ~sP2(X0,X1,X2))),
% 1.80/0.63    inference(rectify,[],[f45])).
% 1.80/0.63  fof(f45,plain,(
% 1.80/0.63    ! [X2,X0,X1] : (((k15_lattice3(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k15_lattice3(X0,X1) != X2)) | ~sP2(X2,X0,X1))),
% 1.80/0.63    inference(nnf_transformation,[],[f28])).
% 1.80/0.63  fof(f28,plain,(
% 1.80/0.63    ! [X2,X0,X1] : ((k15_lattice3(X0,X1) = X2 <=> sP1(X1,X0,X2)) | ~sP2(X2,X0,X1))),
% 1.80/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.80/0.63  fof(f122,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (sP2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.80/0.63    inference(duplicate_literal_removal,[],[f88])).
% 1.80/0.63  fof(f88,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (sP2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f29])).
% 1.80/0.63  fof(f29,plain,(
% 1.80/0.63    ! [X0] : (! [X1,X2] : (sP2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.80/0.63    inference(definition_folding,[],[f13,f28,f27,f26])).
% 1.80/0.63  fof(f13,plain,(
% 1.80/0.63    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.80/0.63    inference(flattening,[],[f12])).
% 1.80/0.63  fof(f12,plain,(
% 1.80/0.63    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.80/0.63    inference(ennf_transformation,[],[f3])).
% 1.80/0.63  fof(f3,axiom,(
% 1.80/0.63    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 1.80/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 1.80/0.63  fof(f1045,plain,(
% 1.80/0.63    ( ! [X0] : (~r3_lattice3(sK11,X0,a_2_2_lattice3(sK11,sK12)) | k15_lattice3(sK11,sK12) != X0 | ~r2_hidden(X0,a_2_2_lattice3(sK11,sK12)) | ~m1_subset_1(X0,u1_struct_0(sK11))) )),
% 1.80/0.63    inference(resolution,[],[f1044,f121])).
% 1.80/0.63  fof(f121,plain,(
% 1.80/0.63    ( ! [X0,X3,X1] : (sP9(X0,X1,X3) | ~r3_lattice3(X1,X3,X0) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 1.80/0.63    inference(equality_resolution,[],[f117])).
% 1.80/0.63  fof(f117,plain,(
% 1.80/0.63    ( ! [X2,X0,X3,X1] : (sP9(X0,X1,X2) | ~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 1.80/0.63    inference(cnf_transformation,[],[f73])).
% 1.80/0.63  fof(f73,plain,(
% 1.80/0.63    ! [X0,X1,X2] : ((sP9(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK17(X0,X1,X2),X0) & sK17(X0,X1,X2) = X2 & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1))) | ~sP9(X0,X1,X2)))),
% 1.80/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f71,f72])).
% 1.80/0.63  fof(f72,plain,(
% 1.80/0.63    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK17(X0,X1,X2),X0) & sK17(X0,X1,X2) = X2 & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1))))),
% 1.80/0.63    introduced(choice_axiom,[])).
% 1.80/0.63  fof(f71,plain,(
% 1.80/0.63    ! [X0,X1,X2] : ((sP9(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP9(X0,X1,X2)))),
% 1.80/0.63    inference(rectify,[],[f70])).
% 1.80/0.63  fof(f70,plain,(
% 1.80/0.63    ! [X2,X1,X0] : ((sP9(X2,X1,X0) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP9(X2,X1,X0)))),
% 1.80/0.63    inference(nnf_transformation,[],[f39])).
% 1.80/0.63  fof(f39,plain,(
% 1.80/0.63    ! [X2,X1,X0] : (sP9(X2,X1,X0) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 1.80/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).
% 1.80/0.63  fof(f1044,plain,(
% 1.80/0.63    ( ! [X0] : (~sP9(a_2_2_lattice3(sK11,sK12),sK11,X0) | ~r2_hidden(X0,a_2_2_lattice3(sK11,sK12)) | k15_lattice3(sK11,sK12) != X0) )),
% 1.80/0.63    inference(subsumption_resolution,[],[f1043,f76])).
% 1.80/0.63  fof(f1043,plain,(
% 1.80/0.63    ( ! [X0] : (k15_lattice3(sK11,sK12) != X0 | ~v4_lattice3(sK11) | ~r2_hidden(X0,a_2_2_lattice3(sK11,sK12)) | ~sP9(a_2_2_lattice3(sK11,sK12),sK11,X0)) )),
% 1.80/0.63    inference(subsumption_resolution,[],[f1042,f77])).
% 1.80/0.63  fof(f1042,plain,(
% 1.80/0.63    ( ! [X0] : (k15_lattice3(sK11,sK12) != X0 | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~r2_hidden(X0,a_2_2_lattice3(sK11,sK12)) | ~sP9(a_2_2_lattice3(sK11,sK12),sK11,X0)) )),
% 1.80/0.63    inference(subsumption_resolution,[],[f1041,f74])).
% 1.80/0.63  fof(f1041,plain,(
% 1.80/0.63    ( ! [X0] : (k15_lattice3(sK11,sK12) != X0 | v2_struct_0(sK11) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~r2_hidden(X0,a_2_2_lattice3(sK11,sK12)) | ~sP9(a_2_2_lattice3(sK11,sK12),sK11,X0)) )),
% 1.80/0.63    inference(subsumption_resolution,[],[f967,f75])).
% 1.80/0.63  fof(f967,plain,(
% 1.80/0.63    ( ! [X0] : (k15_lattice3(sK11,sK12) != X0 | ~v10_lattices(sK11) | v2_struct_0(sK11) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~r2_hidden(X0,a_2_2_lattice3(sK11,sK12)) | ~sP9(a_2_2_lattice3(sK11,sK12),sK11,X0)) )),
% 1.80/0.63    inference(superposition,[],[f78,f963])).
% 1.80/0.63  fof(f963,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (k16_lattice3(X1,X2) = X0 | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~r2_hidden(X0,X2) | ~sP9(X2,X1,X0)) )),
% 1.80/0.63    inference(subsumption_resolution,[],[f962,f118])).
% 1.80/0.63  fof(f118,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (sP10(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f41])).
% 1.80/0.63  fof(f41,plain,(
% 1.80/0.63    ! [X0,X1,X2] : (sP10(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 1.80/0.63    inference(definition_folding,[],[f25,f40,f39])).
% 1.80/0.63  fof(f40,plain,(
% 1.80/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> sP9(X2,X1,X0)) | ~sP10(X0,X1,X2))),
% 1.80/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).
% 1.80/0.63  fof(f25,plain,(
% 1.80/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 1.80/0.63    inference(flattening,[],[f24])).
% 1.80/0.63  fof(f24,plain,(
% 1.80/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 1.80/0.63    inference(ennf_transformation,[],[f6])).
% 1.80/0.63  fof(f6,axiom,(
% 1.80/0.63    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.80/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).
% 1.80/0.63  fof(f962,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1) | k16_lattice3(X1,X2) = X0 | ~r2_hidden(X0,X2) | ~sP9(X2,X1,X0) | ~sP10(X0,X1,X2)) )),
% 1.80/0.63    inference(subsumption_resolution,[],[f959,f146])).
% 1.80/0.63  fof(f146,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~sP9(X0,X1,X2) | m1_subset_1(X2,u1_struct_0(X1))) )),
% 1.80/0.63    inference(duplicate_literal_removal,[],[f145])).
% 1.80/0.63  fof(f145,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X1)) | ~sP9(X0,X1,X2) | ~sP9(X0,X1,X2)) )),
% 1.80/0.63    inference(superposition,[],[f114,f115])).
% 1.80/0.63  fof(f115,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (sK17(X0,X1,X2) = X2 | ~sP9(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f73])).
% 1.80/0.63  fof(f114,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) | ~sP9(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f73])).
% 1.80/0.63  fof(f959,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1) | k16_lattice3(X1,X2) = X0 | ~r2_hidden(X0,X2) | ~sP9(X2,X1,X0) | ~sP10(X0,X1,X2)) )),
% 1.80/0.63    inference(resolution,[],[f953,f113])).
% 1.80/0.63  fof(f113,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~sP9(X2,X1,X0) | ~sP10(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f69])).
% 1.80/0.63  fof(f69,plain,(
% 1.80/0.63    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~sP9(X2,X1,X0)) & (sP9(X2,X1,X0) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~sP10(X0,X1,X2))),
% 1.80/0.63    inference(nnf_transformation,[],[f40])).
% 1.80/0.63  fof(f953,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,a_2_1_lattice3(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | k16_lattice3(X0,X1) = X2 | ~r2_hidden(X2,X1)) )),
% 1.80/0.63    inference(duplicate_literal_removal,[],[f940])).
% 1.80/0.63  fof(f940,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (k16_lattice3(X0,X1) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~r2_hidden(X2,a_2_1_lattice3(X0,X1)) | ~r2_hidden(X2,X1) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 1.80/0.63    inference(resolution,[],[f645,f329])).
% 1.80/0.63  fof(f329,plain,(
% 1.80/0.63    ( ! [X6,X4,X5] : (r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6)) | ~r2_hidden(X4,X6) | ~l3_lattices(X5) | v2_struct_0(X5) | ~m1_subset_1(X4,u1_struct_0(X5))) )),
% 1.80/0.63    inference(subsumption_resolution,[],[f328,f103])).
% 1.80/0.63  fof(f103,plain,(
% 1.80/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP6(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f35])).
% 1.80/0.63  fof(f35,plain,(
% 1.80/0.63    ! [X0] : (! [X1] : (sP6(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.80/0.63    inference(definition_folding,[],[f19,f34,f33])).
% 1.80/0.63  fof(f33,plain,(
% 1.80/0.63    ! [X1,X0,X2] : (sP5(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 1.80/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 1.80/0.63  fof(f34,plain,(
% 1.80/0.63    ! [X0,X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> sP5(X1,X0,X2)) | ~sP6(X0,X1))),
% 1.80/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 1.80/0.63  fof(f19,plain,(
% 1.80/0.63    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.80/0.63    inference(flattening,[],[f18])).
% 1.80/0.63  fof(f18,plain,(
% 1.80/0.63    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.80/0.63    inference(ennf_transformation,[],[f2])).
% 1.80/0.63  fof(f2,axiom,(
% 1.80/0.63    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 1.80/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 1.80/0.63  fof(f328,plain,(
% 1.80/0.63    ( ! [X6,X4,X5] : (~m1_subset_1(X4,u1_struct_0(X5)) | ~r2_hidden(X4,X6) | ~l3_lattices(X5) | v2_struct_0(X5) | r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6)) | ~sP6(X5,X4)) )),
% 1.80/0.63    inference(resolution,[],[f326,f98])).
% 1.80/0.63  fof(f98,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~sP5(X1,X0,X2) | r4_lattice3(X0,X1,X2) | ~sP6(X0,X1)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f59])).
% 1.80/0.63  fof(f59,plain,(
% 1.80/0.63    ! [X0,X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ~sP5(X1,X0,X2)) & (sP5(X1,X0,X2) | ~r4_lattice3(X0,X1,X2))) | ~sP6(X0,X1))),
% 1.80/0.63    inference(nnf_transformation,[],[f34])).
% 1.80/0.63  fof(f326,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (sP5(X0,X2,a_2_1_lattice3(X2,X1)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 1.80/0.63    inference(subsumption_resolution,[],[f325,f131])).
% 1.80/0.63  fof(f131,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (sP4(X1,sK15(X0,X1,X2)) | sP5(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 1.80/0.63    inference(resolution,[],[f100,f96])).
% 1.80/0.63  fof(f100,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) | sP5(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f63])).
% 1.80/0.63  fof(f63,plain,(
% 1.80/0.63    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | (~r1_lattices(X1,sK15(X0,X1,X2),X0) & r2_hidden(sK15(X0,X1,X2),X2) & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP5(X0,X1,X2)))),
% 1.80/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f61,f62])).
% 1.80/0.63  fof(f62,plain,(
% 1.80/0.63    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,sK15(X0,X1,X2),X0) & r2_hidden(sK15(X0,X1,X2),X2) & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))))),
% 1.80/0.63    introduced(choice_axiom,[])).
% 1.80/0.63  fof(f61,plain,(
% 1.80/0.63    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP5(X0,X1,X2)))),
% 1.80/0.63    inference(rectify,[],[f60])).
% 1.80/0.63  fof(f60,plain,(
% 1.80/0.63    ! [X1,X0,X2] : ((sP5(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP5(X1,X0,X2)))),
% 1.80/0.63    inference(nnf_transformation,[],[f33])).
% 1.80/0.63  fof(f325,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~sP4(X2,sK15(X0,X2,a_2_1_lattice3(X2,X1))) | sP5(X0,X2,a_2_1_lattice3(X2,X1)) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 1.80/0.63    inference(duplicate_literal_removal,[],[f324])).
% 1.80/0.63  fof(f324,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~sP4(X2,sK15(X0,X2,a_2_1_lattice3(X2,X1))) | sP5(X0,X2,a_2_1_lattice3(X2,X1)) | ~l3_lattices(X2) | v2_struct_0(X2) | sP5(X0,X2,a_2_1_lattice3(X2,X1))) )),
% 1.80/0.63    inference(resolution,[],[f221,f316])).
% 1.80/0.63  fof(f316,plain,(
% 1.80/0.63    ( ! [X10,X8,X11,X9] : (r3_lattice3(X10,sK15(X8,X9,a_2_1_lattice3(X10,X11)),X11) | ~l3_lattices(X10) | v2_struct_0(X10) | sP5(X8,X9,a_2_1_lattice3(X10,X11))) )),
% 1.80/0.63    inference(resolution,[],[f313,f148])).
% 1.80/0.63  fof(f148,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~sP9(X0,X1,X2) | r3_lattice3(X1,X2,X0)) )),
% 1.80/0.63    inference(duplicate_literal_removal,[],[f147])).
% 1.80/0.63  fof(f147,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (r3_lattice3(X1,X2,X0) | ~sP9(X0,X1,X2) | ~sP9(X0,X1,X2)) )),
% 1.80/0.63    inference(superposition,[],[f116,f115])).
% 1.80/0.63  fof(f116,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK17(X0,X1,X2),X0) | ~sP9(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f73])).
% 1.80/0.63  fof(f313,plain,(
% 1.80/0.63    ( ! [X2,X0,X3,X1] : (sP9(X0,X1,sK15(X2,X3,a_2_1_lattice3(X1,X0))) | sP5(X2,X3,a_2_1_lattice3(X1,X0)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 1.80/0.63    inference(resolution,[],[f179,f118])).
% 1.80/0.63  fof(f179,plain,(
% 1.80/0.63    ( ! [X6,X4,X7,X5] : (~sP10(sK15(X6,X7,a_2_1_lattice3(X5,X4)),X5,X4) | sP9(X4,X5,sK15(X6,X7,a_2_1_lattice3(X5,X4))) | sP5(X6,X7,a_2_1_lattice3(X5,X4))) )),
% 1.80/0.63    inference(resolution,[],[f112,f101])).
% 1.80/0.63  fof(f101,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK15(X0,X1,X2),X2) | sP5(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f63])).
% 1.80/0.63  fof(f112,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | sP9(X2,X1,X0) | ~sP10(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f69])).
% 1.80/0.63  fof(f221,plain,(
% 1.80/0.63    ( ! [X10,X8,X11,X9] : (~r3_lattice3(X9,sK15(X8,X9,X11),X10) | ~r2_hidden(X8,X10) | ~m1_subset_1(X8,u1_struct_0(X9)) | ~sP4(X9,sK15(X8,X9,X11)) | sP5(X8,X9,X11)) )),
% 1.80/0.63    inference(resolution,[],[f182,f102])).
% 1.80/0.63  fof(f102,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~r1_lattices(X1,sK15(X0,X1,X2),X0) | sP5(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f63])).
% 1.80/0.63  fof(f182,plain,(
% 1.80/0.63    ( ! [X2,X0,X3,X1] : (r1_lattices(X2,X3,X0) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~r3_lattice3(X2,X3,X1) | ~sP4(X2,X3)) )),
% 1.80/0.63    inference(resolution,[],[f92,f90])).
% 1.80/0.63  fof(f90,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (sP3(X1,X0,X2) | ~r3_lattice3(X0,X1,X2) | ~sP4(X0,X1)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f54])).
% 1.80/0.63  fof(f92,plain,(
% 1.80/0.63    ( ! [X4,X2,X0,X1] : (~sP3(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f58])).
% 1.80/0.63  fof(f645,plain,(
% 1.80/0.63    ( ! [X6,X4,X5] : (~r4_lattice3(X4,X6,a_2_1_lattice3(X4,X5)) | k16_lattice3(X4,X5) = X6 | ~m1_subset_1(X6,u1_struct_0(X4)) | ~v4_lattice3(X4) | ~v10_lattices(X4) | v2_struct_0(X4) | ~l3_lattices(X4) | ~r2_hidden(X6,a_2_1_lattice3(X4,X5))) )),
% 1.80/0.63    inference(duplicate_literal_removal,[],[f644])).
% 1.80/0.63  fof(f644,plain,(
% 1.80/0.63    ( ! [X6,X4,X5] : (~l3_lattices(X4) | k16_lattice3(X4,X5) = X6 | ~m1_subset_1(X6,u1_struct_0(X4)) | ~v4_lattice3(X4) | ~v10_lattices(X4) | v2_struct_0(X4) | ~r4_lattice3(X4,X6,a_2_1_lattice3(X4,X5)) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~r2_hidden(X6,a_2_1_lattice3(X4,X5)) | ~l3_lattices(X4) | v2_struct_0(X4)) )),
% 1.80/0.63    inference(resolution,[],[f271,f362])).
% 1.80/0.63  fof(f362,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 1.80/0.63    inference(duplicate_literal_removal,[],[f361])).
% 1.80/0.63  fof(f361,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | sP0(X0,X2,X1) | ~l3_lattices(X2) | v2_struct_0(X2) | sP0(X0,X2,X1)) )),
% 1.80/0.63    inference(resolution,[],[f359,f133])).
% 1.80/0.63  fof(f133,plain,(
% 1.80/0.63    ( ! [X4,X2,X3] : (sP6(X2,sK13(X3,X2,X4)) | ~l3_lattices(X2) | v2_struct_0(X2) | sP0(X3,X2,X4)) )),
% 1.80/0.63    inference(resolution,[],[f103,f85])).
% 1.80/0.63  fof(f85,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f53])).
% 1.80/0.63  fof(f359,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~sP6(X1,sK13(X0,X1,X2)) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | sP0(X0,X1,X2)) )),
% 1.80/0.63    inference(duplicate_literal_removal,[],[f357])).
% 1.80/0.63  fof(f357,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X2) | ~sP6(X1,sK13(X0,X1,X2)) | sP0(X0,X1,X2) | sP0(X0,X1,X2)) )),
% 1.80/0.63    inference(resolution,[],[f232,f87])).
% 1.80/0.63  fof(f87,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~r1_lattices(X1,X0,sK13(X0,X1,X2)) | sP0(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f53])).
% 1.80/0.63  fof(f232,plain,(
% 1.80/0.63    ( ! [X6,X8,X7,X9] : (r1_lattices(X7,X6,sK13(X8,X7,X9)) | ~m1_subset_1(X6,u1_struct_0(X7)) | ~r2_hidden(X6,X9) | ~sP6(X7,sK13(X8,X7,X9)) | sP0(X8,X7,X9)) )),
% 1.80/0.63    inference(resolution,[],[f183,f86])).
% 1.80/0.63  fof(f86,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK13(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f53])).
% 1.80/0.63  fof(f183,plain,(
% 1.80/0.63    ( ! [X2,X0,X3,X1] : (~r4_lattice3(X2,X3,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | r1_lattices(X2,X0,X3) | ~r2_hidden(X0,X1) | ~sP6(X2,X3)) )),
% 1.80/0.63    inference(resolution,[],[f99,f97])).
% 1.80/0.63  fof(f97,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (sP5(X1,X0,X2) | ~r4_lattice3(X0,X1,X2) | ~sP6(X0,X1)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f59])).
% 1.80/0.63  fof(f99,plain,(
% 1.80/0.63    ( ! [X4,X2,X0,X1] : (~sP5(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X4,X0)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f63])).
% 1.80/0.63  fof(f271,plain,(
% 1.80/0.63    ( ! [X4,X2,X3] : (~sP0(X4,X2,a_2_1_lattice3(X2,X3)) | ~l3_lattices(X2) | k16_lattice3(X2,X3) = X4 | ~m1_subset_1(X4,u1_struct_0(X2)) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2) | ~r4_lattice3(X2,X4,a_2_1_lattice3(X2,X3))) )),
% 1.80/0.63    inference(resolution,[],[f240,f83])).
% 1.80/0.63  fof(f83,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | ~r4_lattice3(X1,X2,X0)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f49])).
% 1.80/0.63  fof(f240,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~sP1(a_2_1_lattice3(X0,X1),X0,X2) | v2_struct_0(X0) | ~l3_lattices(X0) | k16_lattice3(X0,X1) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~v10_lattices(X0)) )),
% 1.80/0.63    inference(duplicate_literal_removal,[],[f239])).
% 1.80/0.63  fof(f239,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~l3_lattices(X0) | v2_struct_0(X0) | ~sP1(a_2_1_lattice3(X0,X1),X0,X2) | k16_lattice3(X0,X1) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.80/0.63    inference(resolution,[],[f161,f122])).
% 1.80/0.63  fof(f161,plain,(
% 1.80/0.63    ( ! [X4,X2,X3] : (~sP2(X4,X2,a_2_1_lattice3(X2,X3)) | ~l3_lattices(X2) | v2_struct_0(X2) | ~sP1(a_2_1_lattice3(X2,X3),X2,X4) | k16_lattice3(X2,X3) = X4) )),
% 1.80/0.63    inference(superposition,[],[f89,f80])).
% 1.80/0.63  fof(f80,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (k15_lattice3(X1,X2) = X0 | ~sP1(X2,X1,X0) | ~sP2(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f46])).
% 1.80/0.63  fof(f89,plain,(
% 1.80/0.63    ( ! [X0,X1] : (k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f15])).
% 1.80/0.63  fof(f15,plain,(
% 1.80/0.63    ! [X0] : (! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.80/0.63    inference(flattening,[],[f14])).
% 1.80/0.63  fof(f14,plain,(
% 1.80/0.63    ! [X0] : (! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.80/0.63    inference(ennf_transformation,[],[f4])).
% 1.80/0.63  fof(f4,axiom,(
% 1.80/0.63    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)))),
% 1.80/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d22_lattice3)).
% 1.80/0.63  fof(f78,plain,(
% 1.80/0.63    k15_lattice3(sK11,sK12) != k16_lattice3(sK11,a_2_2_lattice3(sK11,sK12))),
% 1.80/0.63    inference(cnf_transformation,[],[f44])).
% 1.80/0.63  fof(f1165,plain,(
% 1.80/0.63    spl18_7),
% 1.80/0.63    inference(avatar_contradiction_clause,[],[f1164])).
% 1.80/0.63  fof(f1164,plain,(
% 1.80/0.63    $false | spl18_7),
% 1.80/0.63    inference(subsumption_resolution,[],[f1163,f76])).
% 1.80/0.63  fof(f1163,plain,(
% 1.80/0.63    ~v4_lattice3(sK11) | spl18_7),
% 1.80/0.63    inference(subsumption_resolution,[],[f1162,f77])).
% 1.80/0.63  fof(f1162,plain,(
% 1.80/0.63    ~l3_lattices(sK11) | ~v4_lattice3(sK11) | spl18_7),
% 1.80/0.63    inference(subsumption_resolution,[],[f1161,f74])).
% 1.80/0.63  fof(f1161,plain,(
% 1.80/0.63    v2_struct_0(sK11) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | spl18_7),
% 1.80/0.63    inference(subsumption_resolution,[],[f1156,f75])).
% 1.80/0.63  fof(f1156,plain,(
% 1.80/0.63    ~v10_lattices(sK11) | v2_struct_0(sK11) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | spl18_7),
% 1.80/0.63    inference(resolution,[],[f1119,f203])).
% 1.80/0.63  fof(f203,plain,(
% 1.80/0.63    ( ! [X2,X3] : (r4_lattice3(X2,k15_lattice3(X2,X3),X3) | ~v10_lattices(X2) | v2_struct_0(X2) | ~l3_lattices(X2) | ~v4_lattice3(X2)) )),
% 1.80/0.63    inference(resolution,[],[f201,f81])).
% 1.80/0.63  fof(f81,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | r4_lattice3(X1,X2,X0)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f49])).
% 1.80/0.63  fof(f1119,plain,(
% 1.80/0.63    ~r4_lattice3(sK11,k15_lattice3(sK11,sK12),sK12) | spl18_7),
% 1.80/0.63    inference(avatar_component_clause,[],[f1117])).
% 1.80/0.63  fof(f1117,plain,(
% 1.80/0.63    spl18_7 <=> r4_lattice3(sK11,k15_lattice3(sK11,sK12),sK12)),
% 1.80/0.63    introduced(avatar_definition,[new_symbols(naming,[spl18_7])])).
% 1.80/0.63  fof(f1139,plain,(
% 1.80/0.63    spl18_6),
% 1.80/0.63    inference(avatar_contradiction_clause,[],[f1138])).
% 1.80/0.63  fof(f1138,plain,(
% 1.80/0.63    $false | spl18_6),
% 1.80/0.63    inference(subsumption_resolution,[],[f1137,f74])).
% 1.80/0.63  fof(f1137,plain,(
% 1.80/0.63    v2_struct_0(sK11) | spl18_6),
% 1.80/0.63    inference(subsumption_resolution,[],[f1131,f77])).
% 1.80/0.63  fof(f1131,plain,(
% 1.80/0.63    ~l3_lattices(sK11) | v2_struct_0(sK11) | spl18_6),
% 1.80/0.63    inference(resolution,[],[f1115,f104])).
% 1.80/0.63  fof(f1115,plain,(
% 1.80/0.63    ~m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11)) | spl18_6),
% 1.80/0.63    inference(avatar_component_clause,[],[f1113])).
% 1.80/0.63  fof(f1120,plain,(
% 1.80/0.63    ~spl18_6 | ~spl18_7 | spl18_5),
% 1.80/0.63    inference(avatar_split_clause,[],[f1108,f1076,f1117,f1113])).
% 1.80/0.63  fof(f1076,plain,(
% 1.80/0.63    spl18_5 <=> sP7(sK12,sK11,k15_lattice3(sK11,sK12))),
% 1.80/0.63    introduced(avatar_definition,[new_symbols(naming,[spl18_5])])).
% 1.80/0.63  fof(f1108,plain,(
% 1.80/0.63    ~r4_lattice3(sK11,k15_lattice3(sK11,sK12),sK12) | ~m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11)) | spl18_5),
% 1.80/0.63    inference(resolution,[],[f1078,f120])).
% 1.80/0.63  fof(f120,plain,(
% 1.80/0.63    ( ! [X0,X3,X1] : (sP7(X0,X1,X3) | ~r4_lattice3(X1,X3,X0) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 1.80/0.63    inference(equality_resolution,[],[f110])).
% 1.80/0.63  fof(f110,plain,(
% 1.80/0.63    ( ! [X2,X0,X3,X1] : (sP7(X0,X1,X2) | ~r4_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 1.80/0.63    inference(cnf_transformation,[],[f68])).
% 1.80/0.63  fof(f1078,plain,(
% 1.80/0.63    ~sP7(sK12,sK11,k15_lattice3(sK11,sK12)) | spl18_5),
% 1.80/0.63    inference(avatar_component_clause,[],[f1076])).
% 1.80/0.63  fof(f1096,plain,(
% 1.80/0.63    spl18_4),
% 1.80/0.63    inference(avatar_contradiction_clause,[],[f1095])).
% 1.80/0.63  fof(f1095,plain,(
% 1.80/0.63    $false | spl18_4),
% 1.80/0.63    inference(subsumption_resolution,[],[f1094,f74])).
% 1.80/0.63  fof(f1094,plain,(
% 1.80/0.63    v2_struct_0(sK11) | spl18_4),
% 1.80/0.63    inference(subsumption_resolution,[],[f1093,f75])).
% 1.80/0.63  fof(f1093,plain,(
% 1.80/0.63    ~v10_lattices(sK11) | v2_struct_0(sK11) | spl18_4),
% 1.80/0.63    inference(subsumption_resolution,[],[f1092,f76])).
% 1.80/0.63  fof(f1092,plain,(
% 1.80/0.63    ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | spl18_4),
% 1.80/0.63    inference(subsumption_resolution,[],[f1088,f77])).
% 1.80/0.63  fof(f1088,plain,(
% 1.80/0.63    ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | spl18_4),
% 1.80/0.63    inference(resolution,[],[f1074,f111])).
% 1.80/0.63  fof(f1074,plain,(
% 1.80/0.63    ~sP8(k15_lattice3(sK11,sK12),sK11,sK12) | spl18_4),
% 1.80/0.63    inference(avatar_component_clause,[],[f1072])).
% 1.80/0.63  fof(f1072,plain,(
% 1.80/0.63    spl18_4 <=> sP8(k15_lattice3(sK11,sK12),sK11,sK12)),
% 1.80/0.63    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).
% 1.80/0.63  fof(f1079,plain,(
% 1.80/0.63    ~spl18_4 | ~spl18_5 | spl18_2),
% 1.80/0.63    inference(avatar_split_clause,[],[f1067,f1055,f1076,f1072])).
% 1.80/0.63  fof(f1067,plain,(
% 1.80/0.63    ~sP7(sK12,sK11,k15_lattice3(sK11,sK12)) | ~sP8(k15_lattice3(sK11,sK12),sK11,sK12) | spl18_2),
% 1.80/0.63    inference(resolution,[],[f1057,f106])).
% 1.80/0.63  fof(f106,plain,(
% 1.80/0.63    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~sP7(X2,X1,X0) | ~sP8(X0,X1,X2)) )),
% 1.80/0.63    inference(cnf_transformation,[],[f64])).
% 1.80/0.63  fof(f1057,plain,(
% 1.80/0.63    ~r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12)) | spl18_2),
% 1.80/0.63    inference(avatar_component_clause,[],[f1055])).
% 1.80/0.63  % SZS output end Proof for theBenchmark
% 1.80/0.63  % (25313)------------------------------
% 1.80/0.63  % (25313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.63  % (25313)Termination reason: Refutation
% 1.80/0.63  
% 1.80/0.63  % (25313)Memory used [KB]: 6908
% 1.80/0.63  % (25313)Time elapsed: 0.203 s
% 1.80/0.63  % (25313)------------------------------
% 1.80/0.63  % (25313)------------------------------
% 1.80/0.63  % (25308)Success in time 0.27 s
%------------------------------------------------------------------------------
