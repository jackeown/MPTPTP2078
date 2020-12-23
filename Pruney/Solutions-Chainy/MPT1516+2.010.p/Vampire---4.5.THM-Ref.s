%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:49 EST 2020

% Result     : Theorem 5.07s
% Output     : Refutation 5.07s
% Verified   : 
% Statistics : Number of formulae       :  285 (3153 expanded)
%              Number of leaves         :   42 ( 794 expanded)
%              Depth                    :   38
%              Number of atoms          : 1174 (21612 expanded)
%              Number of equality atoms :  153 (2310 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11603,plain,(
    $false ),
    inference(subsumption_resolution,[],[f11591,f5141])).

fof(f5141,plain,(
    ! [X2] : m1_subset_1(sK19(k15_lattice3(sK16,X2),sK16),u1_struct_0(sK16)) ),
    inference(resolution,[],[f5105,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | m1_subset_1(sK19(X0,X1),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( ( k2_lattices(X1,sK19(X0,X1),X0) != X0
            | k2_lattices(X1,X0,sK19(X0,X1)) != X0 )
          & m1_subset_1(sK19(X0,X1),u1_struct_0(X1)) ) )
      & ( ! [X3] :
            ( ( k2_lattices(X1,X3,X0) = X0
              & k2_lattices(X1,X0,X3) = X0 )
            | ~ m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f92,f93])).

fof(f93,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X1,X2,X0) != X0
            | k2_lattices(X1,X0,X2) != X0 )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ( k2_lattices(X1,sK19(X0,X1),X0) != X0
          | k2_lattices(X1,X0,sK19(X0,X1)) != X0 )
        & m1_subset_1(sK19(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2] :
            ( ( k2_lattices(X1,X2,X0) != X0
              | k2_lattices(X1,X0,X2) != X0 )
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ! [X3] :
            ( ( k2_lattices(X1,X3,X0) = X0
              & k2_lattices(X1,X0,X3) = X0 )
            | ~ m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP3(X0,X1) ) ) ),
    inference(rectify,[],[f91])).

fof(f91,plain,(
    ! [X1,X0] :
      ( ( sP3(X1,X0)
        | ? [X2] :
            ( ( k2_lattices(X0,X2,X1) != X1
              | k2_lattices(X0,X1,X2) != X1 )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ( k2_lattices(X0,X2,X1) = X1
              & k2_lattices(X0,X1,X2) = X1 )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP3(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( sP3(X1,X0)
    <=> ! [X2] :
          ( ( k2_lattices(X0,X2,X1) = X1
            & k2_lattices(X0,X1,X2) = X1 )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f5105,plain,(
    ! [X3] : ~ sP3(k15_lattice3(sK16,X3),sK16) ),
    inference(subsumption_resolution,[],[f5096,f624])).

fof(f624,plain,(
    ! [X0] :
      ( k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0)
      | ~ sP3(k15_lattice3(sK16,X0),sK16) ) ),
    inference(resolution,[],[f303,f461])).

fof(f461,plain,(
    ! [X13] :
      ( sP4(sK16)
      | ~ sP3(k15_lattice3(sK16,X13),sK16) ) ),
    inference(resolution,[],[f271,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( sP4(X0)
      | ~ sP3(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ( sP4(X0)
        | ! [X1] :
            ( ~ sP3(X1,X0)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ( sP3(sK18(X0),X0)
          & m1_subset_1(sK18(X0),u1_struct_0(X0)) )
        | ~ sP4(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f88,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sP3(X2,X0)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sP3(sK18(X0),X0)
        & m1_subset_1(sK18(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ! [X0] :
      ( ( sP4(X0)
        | ! [X1] :
            ( ~ sP3(X1,X0)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ? [X2] :
            ( sP3(X2,X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP4(X0) ) ) ),
    inference(rectify,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ( sP4(X0)
        | ! [X1] :
            ( ~ sP3(X1,X0)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ? [X1] :
            ( sP3(X1,X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ sP4(X0) ) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( sP4(X0)
    <=> ? [X1] :
          ( sP3(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f271,plain,(
    ! [X11] : m1_subset_1(k15_lattice3(sK16,X11),u1_struct_0(sK16)) ),
    inference(subsumption_resolution,[],[f251,f124])).

fof(f124,plain,(
    ~ v2_struct_0(sK16) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,
    ( ( k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0)
      | ~ l3_lattices(sK16)
      | ~ v13_lattices(sK16)
      | ~ v10_lattices(sK16)
      | v2_struct_0(sK16) )
    & l3_lattices(sK16)
    & v4_lattice3(sK16)
    & v10_lattices(sK16)
    & ~ v2_struct_0(sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f24,f77])).

fof(f77,plain,
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
   => ( ( k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0)
        | ~ l3_lattices(sK16)
        | ~ v13_lattices(sK16)
        | ~ v10_lattices(sK16)
        | v2_struct_0(sK16) )
      & l3_lattices(sK16)
      & v4_lattice3(sK16)
      & v10_lattices(sK16)
      & ~ v2_struct_0(sK16) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).

fof(f251,plain,(
    ! [X11] :
      ( m1_subset_1(k15_lattice3(sK16,X11),u1_struct_0(sK16))
      | v2_struct_0(sK16) ) ),
    inference(resolution,[],[f127,f187])).

fof(f187,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f127,plain,(
    l3_lattices(sK16) ),
    inference(cnf_transformation,[],[f78])).

fof(f303,plain,
    ( ~ sP4(sK16)
    | k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f302,f280])).

fof(f280,plain,(
    sP5(sK16) ),
    inference(subsumption_resolution,[],[f276,f124])).

fof(f276,plain,
    ( sP5(sK16)
    | v2_struct_0(sK16) ),
    inference(resolution,[],[f241,f155])).

fof(f155,plain,(
    ! [X0] :
      ( sP5(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( sP5(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f35,f60,f59,f58])).

fof(f60,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> sP4(X0) )
      | ~ sP5(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).

fof(f241,plain,(
    l1_lattices(sK16) ),
    inference(resolution,[],[f127,f130])).

fof(f130,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f302,plain,
    ( k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0)
    | ~ sP4(sK16)
    | ~ sP5(sK16) ),
    inference(resolution,[],[f289,f147])).

fof(f147,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | ~ sP4(X0)
      | ~ sP5(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ~ sP4(X0) )
        & ( sP4(X0)
          | ~ v13_lattices(X0) ) )
      | ~ sP5(X0) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f289,plain,
    ( ~ v13_lattices(sK16)
    | k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f288,f124])).

fof(f288,plain,
    ( k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0)
    | ~ v13_lattices(sK16)
    | v2_struct_0(sK16) ),
    inference(subsumption_resolution,[],[f287,f125])).

fof(f125,plain,(
    v10_lattices(sK16) ),
    inference(cnf_transformation,[],[f78])).

fof(f287,plain,
    ( k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0)
    | ~ v13_lattices(sK16)
    | ~ v10_lattices(sK16)
    | v2_struct_0(sK16) ),
    inference(subsumption_resolution,[],[f128,f127])).

fof(f128,plain,
    ( k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0)
    | ~ l3_lattices(sK16)
    | ~ v13_lattices(sK16)
    | ~ v10_lattices(sK16)
    | v2_struct_0(sK16) ),
    inference(cnf_transformation,[],[f78])).

fof(f5096,plain,(
    ! [X3] :
      ( k5_lattices(sK16) = k15_lattice3(sK16,k1_xboole_0)
      | ~ sP3(k15_lattice3(sK16,X3),sK16) ) ),
    inference(resolution,[],[f4915,f716])).

fof(f716,plain,(
    ! [X0] :
      ( sP1(k5_lattices(sK16),sK16)
      | ~ sP3(k15_lattice3(sK16,X0),sK16) ) ),
    inference(resolution,[],[f715,f461])).

fof(f715,plain,
    ( ~ sP4(sK16)
    | sP1(k5_lattices(sK16),sK16) ),
    inference(subsumption_resolution,[],[f714,f282])).

fof(f282,plain,(
    m1_subset_1(k5_lattices(sK16),u1_struct_0(sK16)) ),
    inference(subsumption_resolution,[],[f278,f124])).

fof(f278,plain,
    ( m1_subset_1(k5_lattices(sK16),u1_struct_0(sK16))
    | v2_struct_0(sK16) ),
    inference(resolution,[],[f241,f138])).

fof(f138,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f714,plain,
    ( ~ m1_subset_1(k5_lattices(sK16),u1_struct_0(sK16))
    | ~ sP4(sK16)
    | sP1(k5_lattices(sK16),sK16) ),
    inference(resolution,[],[f636,f196])).

fof(f196,plain,(
    ! [X0] :
      ( sP1(k5_lattices(X0),X0)
      | ~ sP2(X0,k5_lattices(X0)) ) ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | k5_lattices(X0) != X1
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( ( k5_lattices(X0) = X1
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | k5_lattices(X0) != X1 ) )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k5_lattices(X0) = X1
      <=> sP1(X1,X0) )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f636,plain,(
    ! [X0] :
      ( sP2(sK16,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK16))
      | ~ sP4(sK16) ) ),
    inference(subsumption_resolution,[],[f635,f280])).

fof(f635,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK16))
      | sP2(sK16,X0)
      | ~ sP4(sK16)
      | ~ sP5(sK16) ) ),
    inference(resolution,[],[f281,f147])).

fof(f281,plain,(
    ! [X0] :
      ( ~ v13_lattices(sK16)
      | ~ m1_subset_1(X0,u1_struct_0(sK16))
      | sP2(sK16,X0) ) ),
    inference(subsumption_resolution,[],[f277,f124])).

fof(f277,plain,(
    ! [X0] :
      ( sP2(sK16,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK16))
      | ~ v13_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(resolution,[],[f241,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f33,f56,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( sP1(X1,X0)
    <=> ! [X2] :
          ( ( k2_lattices(X0,X2,X1) = X1
            & k2_lattices(X0,X1,X2) = X1 )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(f4915,plain,
    ( ~ sP1(k5_lattices(sK16),sK16)
    | k5_lattices(sK16) = k15_lattice3(sK16,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f4905,f271])).

fof(f4905,plain,
    ( k5_lattices(sK16) = k15_lattice3(sK16,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(sK16,k1_xboole_0),u1_struct_0(sK16))
    | ~ sP1(k5_lattices(sK16),sK16) ),
    inference(superposition,[],[f4227,f142])).

fof(f142,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X1,X3,X0) = X0
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( k2_lattices(X1,sK17(X0,X1),X0) != X0
            | k2_lattices(X1,X0,sK17(X0,X1)) != X0 )
          & m1_subset_1(sK17(X0,X1),u1_struct_0(X1)) ) )
      & ( ! [X3] :
            ( ( k2_lattices(X1,X3,X0) = X0
              & k2_lattices(X1,X0,X3) = X0 )
            | ~ m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f83,f84])).

fof(f84,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X1,X2,X0) != X0
            | k2_lattices(X1,X0,X2) != X0 )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ( k2_lattices(X1,sK17(X0,X1),X0) != X0
          | k2_lattices(X1,X0,sK17(X0,X1)) != X0 )
        & m1_subset_1(sK17(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( k2_lattices(X1,X2,X0) != X0
              | k2_lattices(X1,X0,X2) != X0 )
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ! [X3] :
            ( ( k2_lattices(X1,X3,X0) = X0
              & k2_lattices(X1,X0,X3) = X0 )
            | ~ m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f82])).

fof(f82,plain,(
    ! [X1,X0] :
      ( ( sP1(X1,X0)
        | ? [X2] :
            ( ( k2_lattices(X0,X2,X1) != X1
              | k2_lattices(X0,X1,X2) != X1 )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ( k2_lattices(X0,X2,X1) = X1
              & k2_lattices(X0,X1,X2) = X1 )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f4227,plain,(
    k15_lattice3(sK16,k1_xboole_0) = k2_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),k5_lattices(sK16)) ),
    inference(subsumption_resolution,[],[f4223,f282])).

fof(f4223,plain,
    ( k15_lattice3(sK16,k1_xboole_0) = k2_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),k5_lattices(sK16))
    | ~ m1_subset_1(k5_lattices(sK16),u1_struct_0(sK16)) ),
    inference(resolution,[],[f4221,f479])).

fof(f479,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK16,k15_lattice3(sK16,X0),X1)
      | k15_lattice3(sK16,X0) = k2_lattices(sK16,k15_lattice3(sK16,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK16)) ) ),
    inference(subsumption_resolution,[],[f478,f124])).

fof(f478,plain,(
    ! [X0,X1] :
      ( k15_lattice3(sK16,X0) = k2_lattices(sK16,k15_lattice3(sK16,X0),X1)
      | ~ r1_lattices(sK16,k15_lattice3(sK16,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK16))
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f477,f285])).

fof(f285,plain,(
    v8_lattices(sK16) ),
    inference(resolution,[],[f254,f133])).

fof(f133,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f254,plain,(
    sP0(sK16) ),
    inference(subsumption_resolution,[],[f253,f124])).

fof(f253,plain,
    ( sP0(sK16)
    | v2_struct_0(sK16) ),
    inference(subsumption_resolution,[],[f242,f125])).

fof(f242,plain,
    ( sP0(sK16)
    | ~ v10_lattices(sK16)
    | v2_struct_0(sK16) ),
    inference(resolution,[],[f127,f135])).

fof(f135,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(definition_folding,[],[f27,f53])).

fof(f27,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
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
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
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

fof(f477,plain,(
    ! [X0,X1] :
      ( k15_lattice3(sK16,X0) = k2_lattices(sK16,k15_lattice3(sK16,X0),X1)
      | ~ r1_lattices(sK16,k15_lattice3(sK16,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK16))
      | ~ v8_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f476,f286])).

fof(f286,plain,(
    v9_lattices(sK16) ),
    inference(resolution,[],[f254,f134])).

fof(f134,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f476,plain,(
    ! [X0,X1] :
      ( k15_lattice3(sK16,X0) = k2_lattices(sK16,k15_lattice3(sK16,X0),X1)
      | ~ r1_lattices(sK16,k15_lattice3(sK16,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK16))
      | ~ v9_lattices(sK16)
      | ~ v8_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f454,f127])).

fof(f454,plain,(
    ! [X0,X1] :
      ( k15_lattice3(sK16,X0) = k2_lattices(sK16,k15_lattice3(sK16,X0),X1)
      | ~ r1_lattices(sK16,k15_lattice3(sK16,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK16))
      | ~ l3_lattices(sK16)
      | ~ v9_lattices(sK16)
      | ~ v8_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(resolution,[],[f271,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(f4221,plain,(
    r1_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),k5_lattices(sK16)) ),
    inference(forward_demodulation,[],[f4220,f503])).

fof(f503,plain,(
    ! [X23] : k15_lattice3(sK16,X23) = k16_lattice3(sK16,a_2_4_lattice3(sK16,k15_lattice3(sK16,X23))) ),
    inference(subsumption_resolution,[],[f502,f124])).

fof(f502,plain,(
    ! [X23] :
      ( k15_lattice3(sK16,X23) = k16_lattice3(sK16,a_2_4_lattice3(sK16,k15_lattice3(sK16,X23)))
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f501,f125])).

fof(f501,plain,(
    ! [X23] :
      ( k15_lattice3(sK16,X23) = k16_lattice3(sK16,a_2_4_lattice3(sK16,k15_lattice3(sK16,X23)))
      | ~ v10_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f500,f126])).

fof(f126,plain,(
    v4_lattice3(sK16) ),
    inference(cnf_transformation,[],[f78])).

fof(f500,plain,(
    ! [X23] :
      ( k15_lattice3(sK16,X23) = k16_lattice3(sK16,a_2_4_lattice3(sK16,k15_lattice3(sK16,X23)))
      | ~ v4_lattice3(sK16)
      | ~ v10_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f467,f127])).

fof(f467,plain,(
    ! [X23] :
      ( k15_lattice3(sK16,X23) = k16_lattice3(sK16,a_2_4_lattice3(sK16,k15_lattice3(sK16,X23)))
      | ~ l3_lattices(sK16)
      | ~ v4_lattice3(sK16)
      | ~ v10_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(resolution,[],[f271,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).

fof(f4220,plain,(
    r1_lattices(sK16,k16_lattice3(sK16,a_2_4_lattice3(sK16,k15_lattice3(sK16,k1_xboole_0))),k5_lattices(sK16)) ),
    inference(subsumption_resolution,[],[f4214,f282])).

fof(f4214,plain,
    ( r1_lattices(sK16,k16_lattice3(sK16,a_2_4_lattice3(sK16,k15_lattice3(sK16,k1_xboole_0))),k5_lattices(sK16))
    | ~ m1_subset_1(k5_lattices(sK16),u1_struct_0(sK16)) ),
    inference(resolution,[],[f4140,f572])).

fof(f572,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r1_lattices(sK16,k16_lattice3(sK16,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK16)) ) ),
    inference(resolution,[],[f550,f181])).

fof(f181,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X1,X0,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ sP12(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f118,plain,(
    ! [X0,X1,X2] :
      ( ( sP12(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK24(X0,X1,X2))
          & r2_hidden(sK24(X0,X1,X2),X2)
          & m1_subset_1(sK24(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP12(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24])],[f116,f117])).

fof(f117,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK24(X0,X1,X2))
        & r2_hidden(sK24(X0,X1,X2),X2)
        & m1_subset_1(sK24(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f116,plain,(
    ! [X0,X1,X2] :
      ( ( sP12(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP12(X0,X1,X2) ) ) ),
    inference(rectify,[],[f115])).

fof(f115,plain,(
    ! [X1,X0,X2] :
      ( ( sP12(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X1,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X1,X3)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP12(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X1,X0,X2] :
      ( sP12(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X1,X3)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP12])])).

fof(f550,plain,(
    ! [X0] : sP12(k16_lattice3(sK16,X0),sK16,X0) ),
    inference(subsumption_resolution,[],[f545,f441])).

fof(f441,plain,(
    ! [X34] : sP13(sK16,k16_lattice3(sK16,X34)) ),
    inference(subsumption_resolution,[],[f440,f124])).

fof(f440,plain,(
    ! [X34] :
      ( sP13(sK16,k16_lattice3(sK16,X34))
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f403,f127])).

fof(f403,plain,(
    ! [X34] :
      ( sP13(sK16,k16_lattice3(sK16,X34))
      | ~ l3_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(resolution,[],[f270,f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( sP13(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP13(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f45,f72,f71])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r3_lattice3(X0,X1,X2)
        <=> sP12(X1,X0,X2) )
      | ~ sP13(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP13])])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f270,plain,(
    ! [X10] : m1_subset_1(k16_lattice3(sK16,X10),u1_struct_0(sK16)) ),
    inference(subsumption_resolution,[],[f250,f124])).

fof(f250,plain,(
    ! [X10] :
      ( m1_subset_1(k16_lattice3(sK16,X10),u1_struct_0(sK16))
      | v2_struct_0(sK16) ) ),
    inference(resolution,[],[f127,f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f545,plain,(
    ! [X0] :
      ( sP12(k16_lattice3(sK16,X0),sK16,X0)
      | ~ sP13(sK16,k16_lattice3(sK16,X0)) ) ),
    inference(resolution,[],[f534,f179])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( sP12(X1,X0,X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ sP13(X0,X1) ) ),
    inference(cnf_transformation,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X0,X1,X2)
            | ~ sP12(X1,X0,X2) )
          & ( sP12(X1,X0,X2)
            | ~ r3_lattice3(X0,X1,X2) ) )
      | ~ sP13(X0,X1) ) ),
    inference(nnf_transformation,[],[f72])).

fof(f534,plain,(
    ! [X0] : r3_lattice3(sK16,k16_lattice3(sK16,X0),X0) ),
    inference(resolution,[],[f533,f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,X2,X0)
      | ~ sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0,X1,X2] :
      ( ( sP9(X0,X1,X2)
        | ~ sP8(X2,X1,X0)
        | ~ r3_lattice3(X1,X2,X0) )
      & ( ( sP8(X2,X1,X0)
          & r3_lattice3(X1,X2,X0) )
        | ~ sP9(X0,X1,X2) ) ) ),
    inference(rectify,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ( sP9(X2,X0,X1)
        | ~ sP8(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP8(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP9(X2,X0,X1) ) ) ),
    inference(flattening,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ( sP9(X2,X0,X1)
        | ~ sP8(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP8(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP9(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sP9(X2,X0,X1)
    <=> ( sP8(X1,X0,X2)
        & r3_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f533,plain,(
    ! [X2] : sP9(X2,sK16,k16_lattice3(sK16,X2)) ),
    inference(subsumption_resolution,[],[f532,f270])).

fof(f532,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k16_lattice3(sK16,X2),u1_struct_0(sK16))
      | sP9(X2,sK16,k16_lattice3(sK16,X2)) ) ),
    inference(resolution,[],[f265,f197])).

fof(f197,plain,(
    ! [X2,X1] :
      ( sP9(X2,X1,k16_lattice3(X1,X2))
      | ~ sP10(k16_lattice3(X1,X2),X1) ) ),
    inference(equality_resolution,[],[f165])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( sP9(X2,X1,X0)
      | k16_lattice3(X1,X2) != X0
      | ~ sP10(X0,X1) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k16_lattice3(X1,X2) = X0
            | ~ sP9(X2,X1,X0) )
          & ( sP9(X2,X1,X0)
            | k16_lattice3(X1,X2) != X0 ) )
      | ~ sP10(X0,X1) ) ),
    inference(rectify,[],[f101])).

fof(f101,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( ( k16_lattice3(X0,X2) = X1
            | ~ sP9(X2,X0,X1) )
          & ( sP9(X2,X0,X1)
            | k16_lattice3(X0,X2) != X1 ) )
      | ~ sP10(X1,X0) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( k16_lattice3(X0,X2) = X1
        <=> sP9(X2,X0,X1) )
      | ~ sP10(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).

fof(f265,plain,(
    ! [X6] :
      ( sP10(X6,sK16)
      | ~ m1_subset_1(X6,u1_struct_0(sK16)) ) ),
    inference(subsumption_resolution,[],[f264,f124])).

fof(f264,plain,(
    ! [X6] :
      ( sP10(X6,sK16)
      | ~ m1_subset_1(X6,u1_struct_0(sK16))
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f263,f125])).

fof(f263,plain,(
    ! [X6] :
      ( sP10(X6,sK16)
      | ~ m1_subset_1(X6,u1_struct_0(sK16))
      | ~ v10_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f247,f126])).

fof(f247,plain,(
    ! [X6] :
      ( sP10(X6,sK16)
      | ~ m1_subset_1(X6,u1_struct_0(sK16))
      | ~ v4_lattice3(sK16)
      | ~ v10_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(resolution,[],[f127,f174])).

fof(f174,plain,(
    ! [X0,X1] :
      ( sP10(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP10(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f41,f67,f66,f65])).

fof(f65,plain,(
    ! [X1,X0,X2] :
      ( sP8(X1,X0,X2)
    <=> ! [X3] :
          ( r3_lattices(X0,X3,X1)
          | ~ r3_lattice3(X0,X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f4140,plain,(
    r2_hidden(k5_lattices(sK16),a_2_4_lattice3(sK16,k15_lattice3(sK16,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f4138,f513])).

fof(f513,plain,(
    ! [X35,X36] : sP15(X35,sK16,k15_lattice3(sK16,X36)) ),
    inference(subsumption_resolution,[],[f512,f124])).

fof(f512,plain,(
    ! [X35,X36] :
      ( sP15(X35,sK16,k15_lattice3(sK16,X36))
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f511,f125])).

fof(f511,plain,(
    ! [X35,X36] :
      ( sP15(X35,sK16,k15_lattice3(sK16,X36))
      | ~ v10_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f510,f126])).

fof(f510,plain,(
    ! [X35,X36] :
      ( sP15(X35,sK16,k15_lattice3(sK16,X36))
      | ~ v4_lattice3(sK16)
      | ~ v10_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f473,f127])).

fof(f473,plain,(
    ! [X35,X36] :
      ( sP15(X35,sK16,k15_lattice3(sK16,X36))
      | ~ l3_lattices(sK16)
      | ~ v4_lattice3(sK16)
      | ~ v10_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(resolution,[],[f271,f195])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( sP15(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( sP15(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f52,f75,f74])).

fof(f74,plain,(
    ! [X2,X1,X0] :
      ( sP14(X2,X1,X0)
    <=> ? [X3] :
          ( r3_lattices(X1,X2,X3)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP14])])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> sP14(X2,X1,X0) )
      | ~ sP15(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP15])])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_4_lattice3)).

fof(f4138,plain,
    ( r2_hidden(k5_lattices(sK16),a_2_4_lattice3(sK16,k15_lattice3(sK16,k1_xboole_0)))
    | ~ sP15(k5_lattices(sK16),sK16,k15_lattice3(sK16,k1_xboole_0)) ),
    inference(resolution,[],[f4129,f190])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      | ~ sP14(X2,X1,X0)
      | ~ sP15(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f119,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
          | ~ sP14(X2,X1,X0) )
        & ( sP14(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2)) ) )
      | ~ sP15(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f75])).

fof(f4129,plain,(
    sP14(k15_lattice3(sK16,k1_xboole_0),sK16,k5_lattices(sK16)) ),
    inference(resolution,[],[f4120,f337])).

fof(f337,plain,(
    ! [X17] :
      ( ~ r3_lattices(sK16,X17,k5_lattices(sK16))
      | sP14(X17,sK16,k5_lattices(sK16)) ) ),
    inference(resolution,[],[f282,f198])).

fof(f198,plain,(
    ! [X0,X3,X1] :
      ( sP14(X0,X1,X3)
      | ~ r3_lattices(X1,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f194])).

fof(f194,plain,(
    ! [X2,X0,X3,X1] :
      ( sP14(X0,X1,X2)
      | ~ r3_lattices(X1,X0,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f123])).

fof(f123,plain,(
    ! [X0,X1,X2] :
      ( ( sP14(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattices(X1,X0,X3)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r3_lattices(X1,X0,sK25(X0,X1,X2))
          & sK25(X0,X1,X2) = X2
          & m1_subset_1(sK25(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP14(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25])],[f121,f122])).

fof(f122,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattices(X1,X0,X4)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattices(X1,X0,sK25(X0,X1,X2))
        & sK25(X0,X1,X2) = X2
        & m1_subset_1(sK25(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f121,plain,(
    ! [X0,X1,X2] :
      ( ( sP14(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattices(X1,X0,X3)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r3_lattices(X1,X0,X4)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP14(X0,X1,X2) ) ) ),
    inference(rectify,[],[f120])).

fof(f120,plain,(
    ! [X2,X1,X0] :
      ( ( sP14(X2,X1,X0)
        | ! [X3] :
            ( ~ r3_lattices(X1,X2,X3)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP14(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f74])).

fof(f4120,plain,(
    r3_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),k5_lattices(sK16)) ),
    inference(superposition,[],[f4118,f362])).

fof(f362,plain,(
    k5_lattices(sK16) = k15_lattice3(sK16,a_2_3_lattice3(sK16,k5_lattices(sK16))) ),
    inference(subsumption_resolution,[],[f361,f124])).

fof(f361,plain,
    ( k5_lattices(sK16) = k15_lattice3(sK16,a_2_3_lattice3(sK16,k5_lattices(sK16)))
    | v2_struct_0(sK16) ),
    inference(subsumption_resolution,[],[f360,f125])).

fof(f360,plain,
    ( k5_lattices(sK16) = k15_lattice3(sK16,a_2_3_lattice3(sK16,k5_lattices(sK16)))
    | ~ v10_lattices(sK16)
    | v2_struct_0(sK16) ),
    inference(subsumption_resolution,[],[f359,f126])).

fof(f359,plain,
    ( k5_lattices(sK16) = k15_lattice3(sK16,a_2_3_lattice3(sK16,k5_lattices(sK16)))
    | ~ v4_lattice3(sK16)
    | ~ v10_lattices(sK16)
    | v2_struct_0(sK16) ),
    inference(subsumption_resolution,[],[f329,f127])).

fof(f329,plain,
    ( k5_lattices(sK16) = k15_lattice3(sK16,a_2_3_lattice3(sK16,k5_lattices(sK16)))
    | ~ l3_lattices(sK16)
    | ~ v4_lattice3(sK16)
    | ~ v10_lattices(sK16)
    | v2_struct_0(sK16) ),
    inference(resolution,[],[f282,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4118,plain,(
    ! [X0] : r3_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),k15_lattice3(sK16,X0)) ),
    inference(resolution,[],[f1877,f129])).

fof(f129,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1877,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK23(X1,sK16,X0))
      | r3_lattices(sK16,k15_lattice3(sK16,X0),k15_lattice3(sK16,X1)) ) ),
    inference(resolution,[],[f762,f188])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f762,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK23(X3,sK16,X2),X2)
      | r3_lattices(sK16,k15_lattice3(sK16,X2),k15_lattice3(sK16,X3)) ) ),
    inference(resolution,[],[f268,f176])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK23(X0,X1,X2),X2)
      | ~ sP11(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X4] :
            ( ~ r2_hidden(X4,X0)
            | ~ r3_lattices(X1,sK23(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & r2_hidden(sK23(X0,X1,X2),X2)
        & m1_subset_1(sK23(X0,X1,X2),u1_struct_0(X1)) )
      | ~ sP11(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23])],[f111,f112])).

fof(f112,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(X4,X0)
              | ~ r3_lattices(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(X4,X0)
            | ~ r3_lattices(X1,sK23(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & r2_hidden(sK23(X0,X1,X2),X2)
        & m1_subset_1(sK23(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f111,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(X4,X0)
              | ~ r3_lattices(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
      | ~ sP11(X0,X1,X2) ) ),
    inference(rectify,[],[f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(X4,X2)
              | ~ r3_lattices(X0,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP11(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(X4,X2)
              | ~ r3_lattices(X0,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP11(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP11])])).

fof(f268,plain,(
    ! [X8,X7] :
      ( sP11(X8,sK16,X7)
      | r3_lattices(sK16,k15_lattice3(sK16,X7),k15_lattice3(sK16,X8)) ) ),
    inference(subsumption_resolution,[],[f267,f124])).

fof(f267,plain,(
    ! [X8,X7] :
      ( r3_lattices(sK16,k15_lattice3(sK16,X7),k15_lattice3(sK16,X8))
      | sP11(X8,sK16,X7)
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f266,f125])).

fof(f266,plain,(
    ! [X8,X7] :
      ( r3_lattices(sK16,k15_lattice3(sK16,X7),k15_lattice3(sK16,X8))
      | sP11(X8,sK16,X7)
      | ~ v10_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f248,f126])).

fof(f248,plain,(
    ! [X8,X7] :
      ( r3_lattices(sK16,k15_lattice3(sK16,X7),k15_lattice3(sK16,X8))
      | sP11(X8,sK16,X7)
      | ~ v4_lattice3(sK16)
      | ~ v10_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(resolution,[],[f127,f178])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | sP11(X2,X0,X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | sP11(X2,X0,X1) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f43,f69])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ? [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ? [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f11591,plain,(
    ~ m1_subset_1(sK19(k15_lattice3(sK16,k1_xboole_0),sK16),u1_struct_0(sK16)) ),
    inference(resolution,[],[f11550,f4289])).

fof(f4289,plain,(
    ! [X2] :
      ( r1_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK16)) ) ),
    inference(subsumption_resolution,[],[f4288,f124])).

fof(f4288,plain,(
    ! [X2] :
      ( r1_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK16))
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f4287,f125])).

fof(f4287,plain,(
    ! [X2] :
      ( r1_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK16))
      | ~ v10_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f4286,f126])).

fof(f4286,plain,(
    ! [X2] :
      ( r1_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK16))
      | ~ v4_lattice3(sK16)
      | ~ v10_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f4275,f127])).

fof(f4275,plain,(
    ! [X2] :
      ( r1_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK16))
      | ~ l3_lattices(sK16)
      | ~ v4_lattice3(sK16)
      | ~ v10_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(superposition,[],[f4248,f163])).

fof(f4248,plain,(
    ! [X1] : r1_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),k15_lattice3(sK16,X1)) ),
    inference(forward_demodulation,[],[f4247,f503])).

fof(f4247,plain,(
    ! [X1] : r1_lattices(sK16,k16_lattice3(sK16,a_2_4_lattice3(sK16,k15_lattice3(sK16,k1_xboole_0))),k15_lattice3(sK16,X1)) ),
    inference(subsumption_resolution,[],[f4238,f271])).

fof(f4238,plain,(
    ! [X1] :
      ( r1_lattices(sK16,k16_lattice3(sK16,a_2_4_lattice3(sK16,k15_lattice3(sK16,k1_xboole_0))),k15_lattice3(sK16,X1))
      | ~ m1_subset_1(k15_lattice3(sK16,X1),u1_struct_0(sK16)) ) ),
    inference(resolution,[],[f4192,f572])).

fof(f4192,plain,(
    ! [X5] : r2_hidden(k15_lattice3(sK16,X5),a_2_4_lattice3(sK16,k15_lattice3(sK16,k1_xboole_0))) ),
    inference(subsumption_resolution,[],[f4187,f513])).

fof(f4187,plain,(
    ! [X5] :
      ( r2_hidden(k15_lattice3(sK16,X5),a_2_4_lattice3(sK16,k15_lattice3(sK16,k1_xboole_0)))
      | ~ sP15(k15_lattice3(sK16,X5),sK16,k15_lattice3(sK16,k1_xboole_0)) ) ),
    inference(resolution,[],[f4124,f190])).

fof(f4124,plain,(
    ! [X0] : sP14(k15_lattice3(sK16,k1_xboole_0),sK16,k15_lattice3(sK16,X0)) ),
    inference(subsumption_resolution,[],[f4119,f271])).

fof(f4119,plain,(
    ! [X0] :
      ( sP14(k15_lattice3(sK16,k1_xboole_0),sK16,k15_lattice3(sK16,X0))
      | ~ m1_subset_1(k15_lattice3(sK16,X0),u1_struct_0(sK16)) ) ),
    inference(resolution,[],[f4118,f198])).

fof(f11550,plain,(
    ! [X0] : ~ r1_lattices(sK16,k15_lattice3(sK16,X0),sK19(k15_lattice3(sK16,X0),sK16)) ),
    inference(superposition,[],[f10606,f503])).

fof(f10606,plain,(
    ! [X5] : ~ r1_lattices(sK16,k16_lattice3(sK16,X5),sK19(k16_lattice3(sK16,X5),sK16)) ),
    inference(subsumption_resolution,[],[f10605,f124])).

fof(f10605,plain,(
    ! [X5] :
      ( ~ r1_lattices(sK16,k16_lattice3(sK16,X5),sK19(k16_lattice3(sK16,X5),sK16))
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f10604,f285])).

fof(f10604,plain,(
    ! [X5] :
      ( ~ r1_lattices(sK16,k16_lattice3(sK16,X5),sK19(k16_lattice3(sK16,X5),sK16))
      | ~ v8_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f10603,f286])).

fof(f10603,plain,(
    ! [X5] :
      ( ~ r1_lattices(sK16,k16_lattice3(sK16,X5),sK19(k16_lattice3(sK16,X5),sK16))
      | ~ v9_lattices(sK16)
      | ~ v8_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f10602,f127])).

fof(f10602,plain,(
    ! [X5] :
      ( ~ r1_lattices(sK16,k16_lattice3(sK16,X5),sK19(k16_lattice3(sK16,X5),sK16))
      | ~ l3_lattices(sK16)
      | ~ v9_lattices(sK16)
      | ~ v8_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f10601,f270])).

fof(f10601,plain,(
    ! [X5] :
      ( ~ r1_lattices(sK16,k16_lattice3(sK16,X5),sK19(k16_lattice3(sK16,X5),sK16))
      | ~ m1_subset_1(k16_lattice3(sK16,X5),u1_struct_0(sK16))
      | ~ l3_lattices(sK16)
      | ~ v9_lattices(sK16)
      | ~ v8_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(subsumption_resolution,[],[f10590,f5108])).

fof(f5108,plain,(
    ! [X2] : m1_subset_1(sK19(k16_lattice3(sK16,X2),sK16),u1_struct_0(sK16)) ),
    inference(resolution,[],[f5104,f153])).

fof(f5104,plain,(
    ! [X2] : ~ sP3(k16_lattice3(sK16,X2),sK16) ),
    inference(subsumption_resolution,[],[f5095,f625])).

fof(f625,plain,(
    ! [X1] :
      ( k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0)
      | ~ sP3(k16_lattice3(sK16,X1),sK16) ) ),
    inference(resolution,[],[f303,f392])).

fof(f392,plain,(
    ! [X13] :
      ( sP4(sK16)
      | ~ sP3(k16_lattice3(sK16,X13),sK16) ) ),
    inference(resolution,[],[f270,f150])).

fof(f5095,plain,(
    ! [X2] :
      ( k5_lattices(sK16) = k15_lattice3(sK16,k1_xboole_0)
      | ~ sP3(k16_lattice3(sK16,X2),sK16) ) ),
    inference(resolution,[],[f4915,f717])).

fof(f717,plain,(
    ! [X1] :
      ( sP1(k5_lattices(sK16),sK16)
      | ~ sP3(k16_lattice3(sK16,X1),sK16) ) ),
    inference(resolution,[],[f715,f392])).

fof(f10590,plain,(
    ! [X5] :
      ( ~ r1_lattices(sK16,k16_lattice3(sK16,X5),sK19(k16_lattice3(sK16,X5),sK16))
      | ~ m1_subset_1(sK19(k16_lattice3(sK16,X5),sK16),u1_struct_0(sK16))
      | ~ m1_subset_1(k16_lattice3(sK16,X5),u1_struct_0(sK16))
      | ~ l3_lattices(sK16)
      | ~ v9_lattices(sK16)
      | ~ v8_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(trivial_inequality_removal,[],[f10583])).

fof(f10583,plain,(
    ! [X5] :
      ( k16_lattice3(sK16,X5) != k16_lattice3(sK16,X5)
      | ~ r1_lattices(sK16,k16_lattice3(sK16,X5),sK19(k16_lattice3(sK16,X5),sK16))
      | ~ m1_subset_1(sK19(k16_lattice3(sK16,X5),sK16),u1_struct_0(sK16))
      | ~ m1_subset_1(k16_lattice3(sK16,X5),u1_struct_0(sK16))
      | ~ l3_lattices(sK16)
      | ~ v9_lattices(sK16)
      | ~ v8_lattices(sK16)
      | v2_struct_0(sK16) ) ),
    inference(superposition,[],[f9747,f136])).

fof(f9747,plain,(
    ! [X8] : k16_lattice3(sK16,X8) != k2_lattices(sK16,k16_lattice3(sK16,X8),sK19(k16_lattice3(sK16,X8),sK16)) ),
    inference(subsumption_resolution,[],[f9718,f5104])).

fof(f9718,plain,(
    ! [X8] :
      ( k16_lattice3(sK16,X8) != k2_lattices(sK16,k16_lattice3(sK16,X8),sK19(k16_lattice3(sK16,X8),sK16))
      | sP3(k16_lattice3(sK16,X8),sK16) ) ),
    inference(duplicate_literal_removal,[],[f9711])).

fof(f9711,plain,(
    ! [X8] :
      ( k16_lattice3(sK16,X8) != k2_lattices(sK16,k16_lattice3(sK16,X8),sK19(k16_lattice3(sK16,X8),sK16))
      | sP3(k16_lattice3(sK16,X8),sK16)
      | k16_lattice3(sK16,X8) != k2_lattices(sK16,k16_lattice3(sK16,X8),sK19(k16_lattice3(sK16,X8),sK16))
      | sP3(k16_lattice3(sK16,X8),sK16) ) ),
    inference(superposition,[],[f154,f2074])).

fof(f2074,plain,(
    ! [X14,X13] :
      ( k2_lattices(sK16,k16_lattice3(sK16,X13),sK19(X14,sK16)) = k2_lattices(sK16,sK19(X14,sK16),k16_lattice3(sK16,X13))
      | sP3(X14,sK16) ) ),
    inference(resolution,[],[f426,f153])).

fof(f426,plain,(
    ! [X19,X18] :
      ( ~ m1_subset_1(X19,u1_struct_0(sK16))
      | k2_lattices(sK16,k16_lattice3(sK16,X18),X19) = k2_lattices(sK16,X19,k16_lattice3(sK16,X18)) ) ),
    inference(subsumption_resolution,[],[f395,f295])).

fof(f295,plain,(
    sP6(sK16) ),
    inference(subsumption_resolution,[],[f294,f279])).

fof(f279,plain,(
    sP7(sK16) ),
    inference(subsumption_resolution,[],[f275,f124])).

fof(f275,plain,
    ( sP7(sK16)
    | v2_struct_0(sK16) ),
    inference(resolution,[],[f241,f162])).

fof(f162,plain,(
    ! [X0] :
      ( sP7(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( sP7(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f37,f63,f62])).

fof(f62,plain,(
    ! [X0] :
      ( sP6(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f63,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> sP6(X0) )
      | ~ sP7(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f37,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

fof(f294,plain,
    ( sP6(sK16)
    | ~ sP7(sK16) ),
    inference(resolution,[],[f284,f156])).

fof(f156,plain,(
    ! [X0] :
      ( sP6(X0)
      | ~ v6_lattices(X0)
      | ~ sP7(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ~ sP6(X0) )
        & ( sP6(X0)
          | ~ v6_lattices(X0) ) )
      | ~ sP7(X0) ) ),
    inference(nnf_transformation,[],[f63])).

fof(f284,plain,(
    v6_lattices(sK16) ),
    inference(resolution,[],[f254,f132])).

fof(f132,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f395,plain,(
    ! [X19,X18] :
      ( k2_lattices(sK16,k16_lattice3(sK16,X18),X19) = k2_lattices(sK16,X19,k16_lattice3(sK16,X18))
      | ~ m1_subset_1(X19,u1_struct_0(sK16))
      | ~ sP6(sK16) ) ),
    inference(resolution,[],[f270,f158])).

fof(f158,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP6(X0) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0] :
      ( ( sP6(X0)
        | ( k2_lattices(X0,sK20(X0),sK21(X0)) != k2_lattices(X0,sK21(X0),sK20(X0))
          & m1_subset_1(sK21(X0),u1_struct_0(X0))
          & m1_subset_1(sK20(X0),u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP6(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20,sK21])],[f97,f99,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK20(X0),X2) != k2_lattices(X0,X2,sK20(X0))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK20(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f99,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k2_lattices(X0,sK20(X0),X2) != k2_lattices(X0,X2,sK20(X0))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK20(X0),sK21(X0)) != k2_lattices(X0,sK21(X0),sK20(X0))
        & m1_subset_1(sK21(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X0] :
      ( ( sP6(X0)
        | ? [X1] :
            ( ? [X2] :
                ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP6(X0) ) ) ),
    inference(rectify,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( ( sP6(X0)
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
        | ~ sP6(X0) ) ) ),
    inference(nnf_transformation,[],[f62])).

fof(f154,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | k2_lattices(X1,sK19(X0,X1),X0) != X0
      | k2_lattices(X1,X0,sK19(X0,X1)) != X0 ) ),
    inference(cnf_transformation,[],[f94])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (24599)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.47  % (24607)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.48  % (24594)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.48  % (24595)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.48  % (24590)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.48  % (24612)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.48  % (24590)Refutation not found, incomplete strategy% (24590)------------------------------
% 0.21/0.48  % (24590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (24590)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (24590)Memory used [KB]: 10490
% 0.21/0.48  % (24590)Time elapsed: 0.002 s
% 0.21/0.48  % (24590)------------------------------
% 0.21/0.48  % (24590)------------------------------
% 0.21/0.48  % (24604)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (24598)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (24596)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (24605)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (24591)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (24610)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (24591)Refutation not found, incomplete strategy% (24591)------------------------------
% 0.21/0.50  % (24591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24591)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (24591)Memory used [KB]: 10618
% 0.21/0.50  % (24591)Time elapsed: 0.094 s
% 0.21/0.50  % (24591)------------------------------
% 0.21/0.50  % (24591)------------------------------
% 0.21/0.50  % (24597)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (24606)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (24609)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (24597)Refutation not found, incomplete strategy% (24597)------------------------------
% 0.21/0.51  % (24597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24603)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (24597)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24597)Memory used [KB]: 1918
% 0.21/0.51  % (24597)Time elapsed: 0.106 s
% 0.21/0.51  % (24597)------------------------------
% 0.21/0.51  % (24597)------------------------------
% 0.21/0.51  % (24603)Refutation not found, incomplete strategy% (24603)------------------------------
% 0.21/0.51  % (24603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24603)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24603)Memory used [KB]: 6140
% 0.21/0.51  % (24603)Time elapsed: 0.109 s
% 0.21/0.51  % (24603)------------------------------
% 0.21/0.51  % (24603)------------------------------
% 1.26/0.52  % (24600)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.26/0.52  % (24615)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.26/0.52  % (24593)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.26/0.52  % (24602)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.26/0.52  % (24592)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.26/0.53  % (24601)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.26/0.53  % (24601)Refutation not found, incomplete strategy% (24601)------------------------------
% 1.26/0.53  % (24601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (24601)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (24601)Memory used [KB]: 10490
% 1.26/0.53  % (24601)Time elapsed: 0.002 s
% 1.26/0.53  % (24601)------------------------------
% 1.26/0.53  % (24601)------------------------------
% 1.26/0.53  % (24608)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.26/0.53  % (24614)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.26/0.53  % (24611)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.46/0.53  % (24613)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.46/0.58  % (24599)Refutation not found, incomplete strategy% (24599)------------------------------
% 1.46/0.58  % (24599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.59  % (24599)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.59  
% 1.46/0.59  % (24599)Memory used [KB]: 6140
% 1.46/0.59  % (24599)Time elapsed: 0.176 s
% 1.46/0.59  % (24599)------------------------------
% 1.46/0.59  % (24599)------------------------------
% 1.46/0.62  % (24607)Refutation not found, incomplete strategy% (24607)------------------------------
% 1.46/0.62  % (24607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.62  % (24607)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.62  
% 1.46/0.62  % (24607)Memory used [KB]: 6780
% 1.46/0.62  % (24607)Time elapsed: 0.214 s
% 1.46/0.62  % (24607)------------------------------
% 1.46/0.62  % (24607)------------------------------
% 4.54/0.96  % (24604)Time limit reached!
% 4.54/0.96  % (24604)------------------------------
% 4.54/0.96  % (24604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/0.96  % (24604)Termination reason: Time limit
% 4.54/0.96  
% 4.54/0.96  % (24604)Memory used [KB]: 12409
% 4.54/0.96  % (24604)Time elapsed: 0.521 s
% 4.54/0.96  % (24604)------------------------------
% 4.54/0.96  % (24604)------------------------------
% 5.07/1.05  % (24596)Time limit reached!
% 5.07/1.05  % (24596)------------------------------
% 5.07/1.05  % (24596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.07/1.05  % (24596)Termination reason: Time limit
% 5.07/1.05  % (24596)Termination phase: Saturation
% 5.07/1.05  
% 5.07/1.05  % (24596)Memory used [KB]: 16630
% 5.07/1.05  % (24596)Time elapsed: 0.600 s
% 5.07/1.05  % (24596)------------------------------
% 5.07/1.05  % (24596)------------------------------
% 5.07/1.05  % (24598)Refutation found. Thanks to Tanya!
% 5.07/1.05  % SZS status Theorem for theBenchmark
% 5.07/1.05  % SZS output start Proof for theBenchmark
% 5.07/1.05  fof(f11603,plain,(
% 5.07/1.05    $false),
% 5.07/1.05    inference(subsumption_resolution,[],[f11591,f5141])).
% 5.07/1.05  fof(f5141,plain,(
% 5.07/1.05    ( ! [X2] : (m1_subset_1(sK19(k15_lattice3(sK16,X2),sK16),u1_struct_0(sK16))) )),
% 5.07/1.05    inference(resolution,[],[f5105,f153])).
% 5.07/1.05  fof(f153,plain,(
% 5.07/1.05    ( ! [X0,X1] : (sP3(X0,X1) | m1_subset_1(sK19(X0,X1),u1_struct_0(X1))) )),
% 5.07/1.05    inference(cnf_transformation,[],[f94])).
% 5.07/1.05  fof(f94,plain,(
% 5.07/1.05    ! [X0,X1] : ((sP3(X0,X1) | ((k2_lattices(X1,sK19(X0,X1),X0) != X0 | k2_lattices(X1,X0,sK19(X0,X1)) != X0) & m1_subset_1(sK19(X0,X1),u1_struct_0(X1)))) & (! [X3] : ((k2_lattices(X1,X3,X0) = X0 & k2_lattices(X1,X0,X3) = X0) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~sP3(X0,X1)))),
% 5.07/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f92,f93])).
% 5.07/1.05  fof(f93,plain,(
% 5.07/1.05    ! [X1,X0] : (? [X2] : ((k2_lattices(X1,X2,X0) != X0 | k2_lattices(X1,X0,X2) != X0) & m1_subset_1(X2,u1_struct_0(X1))) => ((k2_lattices(X1,sK19(X0,X1),X0) != X0 | k2_lattices(X1,X0,sK19(X0,X1)) != X0) & m1_subset_1(sK19(X0,X1),u1_struct_0(X1))))),
% 5.07/1.05    introduced(choice_axiom,[])).
% 5.07/1.05  fof(f92,plain,(
% 5.07/1.05    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((k2_lattices(X1,X2,X0) != X0 | k2_lattices(X1,X0,X2) != X0) & m1_subset_1(X2,u1_struct_0(X1)))) & (! [X3] : ((k2_lattices(X1,X3,X0) = X0 & k2_lattices(X1,X0,X3) = X0) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~sP3(X0,X1)))),
% 5.07/1.05    inference(rectify,[],[f91])).
% 5.07/1.05  fof(f91,plain,(
% 5.07/1.05    ! [X1,X0] : ((sP3(X1,X0) | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~sP3(X1,X0)))),
% 5.07/1.05    inference(nnf_transformation,[],[f58])).
% 5.07/1.05  fof(f58,plain,(
% 5.07/1.05    ! [X1,X0] : (sP3(X1,X0) <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 5.07/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 5.07/1.05  fof(f5105,plain,(
% 5.07/1.05    ( ! [X3] : (~sP3(k15_lattice3(sK16,X3),sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f5096,f624])).
% 5.07/1.05  fof(f624,plain,(
% 5.07/1.05    ( ! [X0] : (k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0) | ~sP3(k15_lattice3(sK16,X0),sK16)) )),
% 5.07/1.05    inference(resolution,[],[f303,f461])).
% 5.07/1.05  fof(f461,plain,(
% 5.07/1.05    ( ! [X13] : (sP4(sK16) | ~sP3(k15_lattice3(sK16,X13),sK16)) )),
% 5.07/1.05    inference(resolution,[],[f271,f150])).
% 5.07/1.05  fof(f150,plain,(
% 5.07/1.05    ( ! [X0,X1] : (sP4(X0) | ~sP3(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 5.07/1.05    inference(cnf_transformation,[],[f90])).
% 5.07/1.05  fof(f90,plain,(
% 5.07/1.05    ! [X0] : ((sP4(X0) | ! [X1] : (~sP3(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((sP3(sK18(X0),X0) & m1_subset_1(sK18(X0),u1_struct_0(X0))) | ~sP4(X0)))),
% 5.07/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f88,f89])).
% 5.07/1.05  fof(f89,plain,(
% 5.07/1.05    ! [X0] : (? [X2] : (sP3(X2,X0) & m1_subset_1(X2,u1_struct_0(X0))) => (sP3(sK18(X0),X0) & m1_subset_1(sK18(X0),u1_struct_0(X0))))),
% 5.07/1.05    introduced(choice_axiom,[])).
% 5.07/1.05  fof(f88,plain,(
% 5.07/1.05    ! [X0] : ((sP4(X0) | ! [X1] : (~sP3(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X2] : (sP3(X2,X0) & m1_subset_1(X2,u1_struct_0(X0))) | ~sP4(X0)))),
% 5.07/1.05    inference(rectify,[],[f87])).
% 5.07/1.05  fof(f87,plain,(
% 5.07/1.05    ! [X0] : ((sP4(X0) | ! [X1] : (~sP3(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (sP3(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) | ~sP4(X0)))),
% 5.07/1.05    inference(nnf_transformation,[],[f59])).
% 5.07/1.05  fof(f59,plain,(
% 5.07/1.05    ! [X0] : (sP4(X0) <=> ? [X1] : (sP3(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))))),
% 5.07/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 5.07/1.05  fof(f271,plain,(
% 5.07/1.05    ( ! [X11] : (m1_subset_1(k15_lattice3(sK16,X11),u1_struct_0(sK16))) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f251,f124])).
% 5.07/1.05  fof(f124,plain,(
% 5.07/1.05    ~v2_struct_0(sK16)),
% 5.07/1.05    inference(cnf_transformation,[],[f78])).
% 5.07/1.05  fof(f78,plain,(
% 5.07/1.05    (k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0) | ~l3_lattices(sK16) | ~v13_lattices(sK16) | ~v10_lattices(sK16) | v2_struct_0(sK16)) & l3_lattices(sK16) & v4_lattice3(sK16) & v10_lattices(sK16) & ~v2_struct_0(sK16)),
% 5.07/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f24,f77])).
% 5.07/1.05  fof(f77,plain,(
% 5.07/1.05    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0) | ~l3_lattices(sK16) | ~v13_lattices(sK16) | ~v10_lattices(sK16) | v2_struct_0(sK16)) & l3_lattices(sK16) & v4_lattice3(sK16) & v10_lattices(sK16) & ~v2_struct_0(sK16))),
% 5.07/1.05    introduced(choice_axiom,[])).
% 5.07/1.05  fof(f24,plain,(
% 5.07/1.05    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 5.07/1.05    inference(flattening,[],[f23])).
% 5.07/1.05  fof(f23,plain,(
% 5.07/1.05    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 5.07/1.05    inference(ennf_transformation,[],[f18])).
% 5.07/1.05  fof(f18,negated_conjecture,(
% 5.07/1.05    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 5.07/1.05    inference(negated_conjecture,[],[f17])).
% 5.07/1.05  fof(f17,conjecture,(
% 5.07/1.05    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 5.07/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).
% 5.07/1.05  fof(f251,plain,(
% 5.07/1.05    ( ! [X11] : (m1_subset_1(k15_lattice3(sK16,X11),u1_struct_0(sK16)) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(resolution,[],[f127,f187])).
% 5.07/1.05  fof(f187,plain,(
% 5.07/1.05    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f49])).
% 5.07/1.05  fof(f49,plain,(
% 5.07/1.05    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 5.07/1.05    inference(flattening,[],[f48])).
% 5.07/1.05  fof(f48,plain,(
% 5.07/1.05    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 5.07/1.05    inference(ennf_transformation,[],[f11])).
% 5.07/1.05  fof(f11,axiom,(
% 5.07/1.05    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 5.07/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 5.07/1.05  fof(f127,plain,(
% 5.07/1.05    l3_lattices(sK16)),
% 5.07/1.05    inference(cnf_transformation,[],[f78])).
% 5.07/1.05  fof(f303,plain,(
% 5.07/1.05    ~sP4(sK16) | k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0)),
% 5.07/1.05    inference(subsumption_resolution,[],[f302,f280])).
% 5.07/1.05  fof(f280,plain,(
% 5.07/1.05    sP5(sK16)),
% 5.07/1.05    inference(subsumption_resolution,[],[f276,f124])).
% 5.07/1.05  fof(f276,plain,(
% 5.07/1.05    sP5(sK16) | v2_struct_0(sK16)),
% 5.07/1.05    inference(resolution,[],[f241,f155])).
% 5.07/1.05  fof(f155,plain,(
% 5.07/1.05    ( ! [X0] : (sP5(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f61])).
% 5.07/1.05  fof(f61,plain,(
% 5.07/1.05    ! [X0] : (sP5(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.07/1.05    inference(definition_folding,[],[f35,f60,f59,f58])).
% 5.07/1.05  fof(f60,plain,(
% 5.07/1.05    ! [X0] : ((v13_lattices(X0) <=> sP4(X0)) | ~sP5(X0))),
% 5.07/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 5.07/1.05  fof(f35,plain,(
% 5.07/1.05    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.07/1.05    inference(flattening,[],[f34])).
% 5.07/1.05  fof(f34,plain,(
% 5.07/1.05    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 5.07/1.05    inference(ennf_transformation,[],[f8])).
% 5.07/1.05  fof(f8,axiom,(
% 5.07/1.05    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 5.07/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).
% 5.07/1.05  fof(f241,plain,(
% 5.07/1.05    l1_lattices(sK16)),
% 5.07/1.05    inference(resolution,[],[f127,f130])).
% 5.07/1.05  fof(f130,plain,(
% 5.07/1.05    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f25])).
% 5.07/1.05  fof(f25,plain,(
% 5.07/1.05    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 5.07/1.05    inference(ennf_transformation,[],[f19])).
% 5.07/1.05  fof(f19,plain,(
% 5.07/1.05    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 5.07/1.05    inference(pure_predicate_removal,[],[f6])).
% 5.07/1.05  fof(f6,axiom,(
% 5.07/1.05    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 5.07/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 5.07/1.05  fof(f302,plain,(
% 5.07/1.05    k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0) | ~sP4(sK16) | ~sP5(sK16)),
% 5.07/1.05    inference(resolution,[],[f289,f147])).
% 5.07/1.05  fof(f147,plain,(
% 5.07/1.05    ( ! [X0] : (v13_lattices(X0) | ~sP4(X0) | ~sP5(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f86])).
% 5.07/1.05  fof(f86,plain,(
% 5.07/1.05    ! [X0] : (((v13_lattices(X0) | ~sP4(X0)) & (sP4(X0) | ~v13_lattices(X0))) | ~sP5(X0))),
% 5.07/1.05    inference(nnf_transformation,[],[f60])).
% 5.07/1.05  fof(f289,plain,(
% 5.07/1.05    ~v13_lattices(sK16) | k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0)),
% 5.07/1.05    inference(subsumption_resolution,[],[f288,f124])).
% 5.07/1.05  fof(f288,plain,(
% 5.07/1.05    k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0) | ~v13_lattices(sK16) | v2_struct_0(sK16)),
% 5.07/1.05    inference(subsumption_resolution,[],[f287,f125])).
% 5.07/1.05  fof(f125,plain,(
% 5.07/1.05    v10_lattices(sK16)),
% 5.07/1.05    inference(cnf_transformation,[],[f78])).
% 5.07/1.05  fof(f287,plain,(
% 5.07/1.05    k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0) | ~v13_lattices(sK16) | ~v10_lattices(sK16) | v2_struct_0(sK16)),
% 5.07/1.05    inference(subsumption_resolution,[],[f128,f127])).
% 5.07/1.05  fof(f128,plain,(
% 5.07/1.05    k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0) | ~l3_lattices(sK16) | ~v13_lattices(sK16) | ~v10_lattices(sK16) | v2_struct_0(sK16)),
% 5.07/1.05    inference(cnf_transformation,[],[f78])).
% 5.07/1.05  fof(f5096,plain,(
% 5.07/1.05    ( ! [X3] : (k5_lattices(sK16) = k15_lattice3(sK16,k1_xboole_0) | ~sP3(k15_lattice3(sK16,X3),sK16)) )),
% 5.07/1.05    inference(resolution,[],[f4915,f716])).
% 5.07/1.05  fof(f716,plain,(
% 5.07/1.05    ( ! [X0] : (sP1(k5_lattices(sK16),sK16) | ~sP3(k15_lattice3(sK16,X0),sK16)) )),
% 5.07/1.05    inference(resolution,[],[f715,f461])).
% 5.07/1.05  fof(f715,plain,(
% 5.07/1.05    ~sP4(sK16) | sP1(k5_lattices(sK16),sK16)),
% 5.07/1.05    inference(subsumption_resolution,[],[f714,f282])).
% 5.07/1.05  fof(f282,plain,(
% 5.07/1.05    m1_subset_1(k5_lattices(sK16),u1_struct_0(sK16))),
% 5.07/1.05    inference(subsumption_resolution,[],[f278,f124])).
% 5.07/1.05  fof(f278,plain,(
% 5.07/1.05    m1_subset_1(k5_lattices(sK16),u1_struct_0(sK16)) | v2_struct_0(sK16)),
% 5.07/1.05    inference(resolution,[],[f241,f138])).
% 5.07/1.05  fof(f138,plain,(
% 5.07/1.05    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f31])).
% 5.07/1.05  fof(f31,plain,(
% 5.07/1.05    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.07/1.05    inference(flattening,[],[f30])).
% 5.07/1.05  fof(f30,plain,(
% 5.07/1.05    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 5.07/1.05    inference(ennf_transformation,[],[f5])).
% 5.07/1.05  fof(f5,axiom,(
% 5.07/1.05    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 5.07/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 5.07/1.05  fof(f714,plain,(
% 5.07/1.05    ~m1_subset_1(k5_lattices(sK16),u1_struct_0(sK16)) | ~sP4(sK16) | sP1(k5_lattices(sK16),sK16)),
% 5.07/1.05    inference(resolution,[],[f636,f196])).
% 5.07/1.05  fof(f196,plain,(
% 5.07/1.05    ( ! [X0] : (sP1(k5_lattices(X0),X0) | ~sP2(X0,k5_lattices(X0))) )),
% 5.07/1.05    inference(equality_resolution,[],[f139])).
% 5.07/1.05  fof(f139,plain,(
% 5.07/1.05    ( ! [X0,X1] : (sP1(X1,X0) | k5_lattices(X0) != X1 | ~sP2(X0,X1)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f81])).
% 5.07/1.05  fof(f81,plain,(
% 5.07/1.05    ! [X0,X1] : (((k5_lattices(X0) = X1 | ~sP1(X1,X0)) & (sP1(X1,X0) | k5_lattices(X0) != X1)) | ~sP2(X0,X1))),
% 5.07/1.05    inference(nnf_transformation,[],[f56])).
% 5.07/1.05  fof(f56,plain,(
% 5.07/1.05    ! [X0,X1] : ((k5_lattices(X0) = X1 <=> sP1(X1,X0)) | ~sP2(X0,X1))),
% 5.07/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 5.07/1.05  fof(f636,plain,(
% 5.07/1.05    ( ! [X0] : (sP2(sK16,X0) | ~m1_subset_1(X0,u1_struct_0(sK16)) | ~sP4(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f635,f280])).
% 5.07/1.05  fof(f635,plain,(
% 5.07/1.05    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK16)) | sP2(sK16,X0) | ~sP4(sK16) | ~sP5(sK16)) )),
% 5.07/1.05    inference(resolution,[],[f281,f147])).
% 5.07/1.05  fof(f281,plain,(
% 5.07/1.05    ( ! [X0] : (~v13_lattices(sK16) | ~m1_subset_1(X0,u1_struct_0(sK16)) | sP2(sK16,X0)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f277,f124])).
% 5.07/1.05  fof(f277,plain,(
% 5.07/1.05    ( ! [X0] : (sP2(sK16,X0) | ~m1_subset_1(X0,u1_struct_0(sK16)) | ~v13_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(resolution,[],[f241,f145])).
% 5.07/1.05  fof(f145,plain,(
% 5.07/1.05    ( ! [X0,X1] : (sP2(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f57])).
% 5.07/1.05  fof(f57,plain,(
% 5.07/1.05    ! [X0] : (! [X1] : (sP2(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.07/1.05    inference(definition_folding,[],[f33,f56,f55])).
% 5.07/1.05  fof(f55,plain,(
% 5.07/1.05    ! [X1,X0] : (sP1(X1,X0) <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 5.07/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 5.07/1.05  fof(f33,plain,(
% 5.07/1.05    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.07/1.05    inference(flattening,[],[f32])).
% 5.07/1.05  fof(f32,plain,(
% 5.07/1.05    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 5.07/1.05    inference(ennf_transformation,[],[f4])).
% 5.07/1.05  fof(f4,axiom,(
% 5.07/1.05    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 5.07/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).
% 5.07/1.05  fof(f4915,plain,(
% 5.07/1.05    ~sP1(k5_lattices(sK16),sK16) | k5_lattices(sK16) = k15_lattice3(sK16,k1_xboole_0)),
% 5.07/1.05    inference(subsumption_resolution,[],[f4905,f271])).
% 5.07/1.05  fof(f4905,plain,(
% 5.07/1.05    k5_lattices(sK16) = k15_lattice3(sK16,k1_xboole_0) | ~m1_subset_1(k15_lattice3(sK16,k1_xboole_0),u1_struct_0(sK16)) | ~sP1(k5_lattices(sK16),sK16)),
% 5.07/1.05    inference(superposition,[],[f4227,f142])).
% 5.07/1.05  fof(f142,plain,(
% 5.07/1.05    ( ! [X0,X3,X1] : (k2_lattices(X1,X3,X0) = X0 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~sP1(X0,X1)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f85])).
% 5.07/1.05  fof(f85,plain,(
% 5.07/1.05    ! [X0,X1] : ((sP1(X0,X1) | ((k2_lattices(X1,sK17(X0,X1),X0) != X0 | k2_lattices(X1,X0,sK17(X0,X1)) != X0) & m1_subset_1(sK17(X0,X1),u1_struct_0(X1)))) & (! [X3] : ((k2_lattices(X1,X3,X0) = X0 & k2_lattices(X1,X0,X3) = X0) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~sP1(X0,X1)))),
% 5.07/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f83,f84])).
% 5.07/1.05  fof(f84,plain,(
% 5.07/1.05    ! [X1,X0] : (? [X2] : ((k2_lattices(X1,X2,X0) != X0 | k2_lattices(X1,X0,X2) != X0) & m1_subset_1(X2,u1_struct_0(X1))) => ((k2_lattices(X1,sK17(X0,X1),X0) != X0 | k2_lattices(X1,X0,sK17(X0,X1)) != X0) & m1_subset_1(sK17(X0,X1),u1_struct_0(X1))))),
% 5.07/1.05    introduced(choice_axiom,[])).
% 5.07/1.05  fof(f83,plain,(
% 5.07/1.05    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((k2_lattices(X1,X2,X0) != X0 | k2_lattices(X1,X0,X2) != X0) & m1_subset_1(X2,u1_struct_0(X1)))) & (! [X3] : ((k2_lattices(X1,X3,X0) = X0 & k2_lattices(X1,X0,X3) = X0) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~sP1(X0,X1)))),
% 5.07/1.05    inference(rectify,[],[f82])).
% 5.07/1.05  fof(f82,plain,(
% 5.07/1.05    ! [X1,X0] : ((sP1(X1,X0) | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~sP1(X1,X0)))),
% 5.07/1.05    inference(nnf_transformation,[],[f55])).
% 5.07/1.05  fof(f4227,plain,(
% 5.07/1.05    k15_lattice3(sK16,k1_xboole_0) = k2_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),k5_lattices(sK16))),
% 5.07/1.05    inference(subsumption_resolution,[],[f4223,f282])).
% 5.07/1.05  fof(f4223,plain,(
% 5.07/1.05    k15_lattice3(sK16,k1_xboole_0) = k2_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),k5_lattices(sK16)) | ~m1_subset_1(k5_lattices(sK16),u1_struct_0(sK16))),
% 5.07/1.05    inference(resolution,[],[f4221,f479])).
% 5.07/1.05  fof(f479,plain,(
% 5.07/1.05    ( ! [X0,X1] : (~r1_lattices(sK16,k15_lattice3(sK16,X0),X1) | k15_lattice3(sK16,X0) = k2_lattices(sK16,k15_lattice3(sK16,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK16))) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f478,f124])).
% 5.07/1.05  fof(f478,plain,(
% 5.07/1.05    ( ! [X0,X1] : (k15_lattice3(sK16,X0) = k2_lattices(sK16,k15_lattice3(sK16,X0),X1) | ~r1_lattices(sK16,k15_lattice3(sK16,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK16)) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f477,f285])).
% 5.07/1.05  fof(f285,plain,(
% 5.07/1.05    v8_lattices(sK16)),
% 5.07/1.05    inference(resolution,[],[f254,f133])).
% 5.07/1.05  fof(f133,plain,(
% 5.07/1.05    ( ! [X0] : (v8_lattices(X0) | ~sP0(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f79])).
% 5.07/1.05  fof(f79,plain,(
% 5.07/1.05    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 5.07/1.05    inference(nnf_transformation,[],[f53])).
% 5.07/1.05  fof(f53,plain,(
% 5.07/1.05    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 5.07/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 5.07/1.05  fof(f254,plain,(
% 5.07/1.05    sP0(sK16)),
% 5.07/1.05    inference(subsumption_resolution,[],[f253,f124])).
% 5.07/1.05  fof(f253,plain,(
% 5.07/1.05    sP0(sK16) | v2_struct_0(sK16)),
% 5.07/1.05    inference(subsumption_resolution,[],[f242,f125])).
% 5.07/1.05  fof(f242,plain,(
% 5.07/1.05    sP0(sK16) | ~v10_lattices(sK16) | v2_struct_0(sK16)),
% 5.07/1.05    inference(resolution,[],[f127,f135])).
% 5.07/1.05  fof(f135,plain,(
% 5.07/1.05    ( ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f54])).
% 5.07/1.05  fof(f54,plain,(
% 5.07/1.05    ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 5.07/1.05    inference(definition_folding,[],[f27,f53])).
% 5.07/1.05  fof(f27,plain,(
% 5.07/1.05    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 5.07/1.05    inference(flattening,[],[f26])).
% 5.07/1.05  fof(f26,plain,(
% 5.07/1.05    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 5.07/1.05    inference(ennf_transformation,[],[f22])).
% 5.07/1.05  fof(f22,plain,(
% 5.07/1.05    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 5.07/1.05    inference(pure_predicate_removal,[],[f21])).
% 5.07/1.05  fof(f21,plain,(
% 5.07/1.05    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 5.07/1.05    inference(pure_predicate_removal,[],[f20])).
% 5.07/1.05  fof(f20,plain,(
% 5.07/1.05    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 5.07/1.05    inference(pure_predicate_removal,[],[f3])).
% 5.07/1.05  fof(f3,axiom,(
% 5.07/1.05    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 5.07/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 5.07/1.05  fof(f477,plain,(
% 5.07/1.05    ( ! [X0,X1] : (k15_lattice3(sK16,X0) = k2_lattices(sK16,k15_lattice3(sK16,X0),X1) | ~r1_lattices(sK16,k15_lattice3(sK16,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK16)) | ~v8_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f476,f286])).
% 5.07/1.05  fof(f286,plain,(
% 5.07/1.05    v9_lattices(sK16)),
% 5.07/1.05    inference(resolution,[],[f254,f134])).
% 5.07/1.05  fof(f134,plain,(
% 5.07/1.05    ( ! [X0] : (v9_lattices(X0) | ~sP0(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f79])).
% 5.07/1.05  fof(f476,plain,(
% 5.07/1.05    ( ! [X0,X1] : (k15_lattice3(sK16,X0) = k2_lattices(sK16,k15_lattice3(sK16,X0),X1) | ~r1_lattices(sK16,k15_lattice3(sK16,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK16)) | ~v9_lattices(sK16) | ~v8_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f454,f127])).
% 5.07/1.05  fof(f454,plain,(
% 5.07/1.05    ( ! [X0,X1] : (k15_lattice3(sK16,X0) = k2_lattices(sK16,k15_lattice3(sK16,X0),X1) | ~r1_lattices(sK16,k15_lattice3(sK16,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK16)) | ~l3_lattices(sK16) | ~v9_lattices(sK16) | ~v8_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(resolution,[],[f271,f136])).
% 5.07/1.05  fof(f136,plain,(
% 5.07/1.05    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f80])).
% 5.07/1.05  fof(f80,plain,(
% 5.07/1.05    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 5.07/1.05    inference(nnf_transformation,[],[f29])).
% 5.07/1.05  fof(f29,plain,(
% 5.07/1.05    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 5.07/1.05    inference(flattening,[],[f28])).
% 5.07/1.05  fof(f28,plain,(
% 5.07/1.05    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 5.07/1.05    inference(ennf_transformation,[],[f7])).
% 5.07/1.05  fof(f7,axiom,(
% 5.07/1.05    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 5.07/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 5.07/1.05  fof(f4221,plain,(
% 5.07/1.05    r1_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),k5_lattices(sK16))),
% 5.07/1.05    inference(forward_demodulation,[],[f4220,f503])).
% 5.07/1.05  fof(f503,plain,(
% 5.07/1.05    ( ! [X23] : (k15_lattice3(sK16,X23) = k16_lattice3(sK16,a_2_4_lattice3(sK16,k15_lattice3(sK16,X23)))) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f502,f124])).
% 5.07/1.05  fof(f502,plain,(
% 5.07/1.05    ( ! [X23] : (k15_lattice3(sK16,X23) = k16_lattice3(sK16,a_2_4_lattice3(sK16,k15_lattice3(sK16,X23))) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f501,f125])).
% 5.07/1.05  fof(f501,plain,(
% 5.07/1.05    ( ! [X23] : (k15_lattice3(sK16,X23) = k16_lattice3(sK16,a_2_4_lattice3(sK16,k15_lattice3(sK16,X23))) | ~v10_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f500,f126])).
% 5.07/1.05  fof(f126,plain,(
% 5.07/1.05    v4_lattice3(sK16)),
% 5.07/1.05    inference(cnf_transformation,[],[f78])).
% 5.07/1.05  fof(f500,plain,(
% 5.07/1.05    ( ! [X23] : (k15_lattice3(sK16,X23) = k16_lattice3(sK16,a_2_4_lattice3(sK16,k15_lattice3(sK16,X23))) | ~v4_lattice3(sK16) | ~v10_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f467,f127])).
% 5.07/1.05  fof(f467,plain,(
% 5.07/1.05    ( ! [X23] : (k15_lattice3(sK16,X23) = k16_lattice3(sK16,a_2_4_lattice3(sK16,k15_lattice3(sK16,X23))) | ~l3_lattices(sK16) | ~v4_lattice3(sK16) | ~v10_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(resolution,[],[f271,f164])).
% 5.07/1.05  fof(f164,plain,(
% 5.07/1.05    ( ! [X0,X1] : (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f39])).
% 5.07/1.05  fof(f39,plain,(
% 5.07/1.05    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 5.07/1.05    inference(flattening,[],[f38])).
% 5.07/1.05  fof(f38,plain,(
% 5.07/1.05    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 5.07/1.05    inference(ennf_transformation,[],[f15])).
% 5.07/1.05  fof(f15,axiom,(
% 5.07/1.05    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1)))),
% 5.07/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).
% 5.07/1.05  fof(f4220,plain,(
% 5.07/1.05    r1_lattices(sK16,k16_lattice3(sK16,a_2_4_lattice3(sK16,k15_lattice3(sK16,k1_xboole_0))),k5_lattices(sK16))),
% 5.07/1.05    inference(subsumption_resolution,[],[f4214,f282])).
% 5.07/1.05  fof(f4214,plain,(
% 5.07/1.05    r1_lattices(sK16,k16_lattice3(sK16,a_2_4_lattice3(sK16,k15_lattice3(sK16,k1_xboole_0))),k5_lattices(sK16)) | ~m1_subset_1(k5_lattices(sK16),u1_struct_0(sK16))),
% 5.07/1.05    inference(resolution,[],[f4140,f572])).
% 5.07/1.05  fof(f572,plain,(
% 5.07/1.05    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r1_lattices(sK16,k16_lattice3(sK16,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK16))) )),
% 5.07/1.05    inference(resolution,[],[f550,f181])).
% 5.07/1.05  fof(f181,plain,(
% 5.07/1.05    ( ! [X4,X2,X0,X1] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~sP12(X0,X1,X2)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f118])).
% 5.07/1.05  fof(f118,plain,(
% 5.07/1.05    ! [X0,X1,X2] : ((sP12(X0,X1,X2) | (~r1_lattices(X1,X0,sK24(X0,X1,X2)) & r2_hidden(sK24(X0,X1,X2),X2) & m1_subset_1(sK24(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP12(X0,X1,X2)))),
% 5.07/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24])],[f116,f117])).
% 5.07/1.05  fof(f117,plain,(
% 5.07/1.05    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK24(X0,X1,X2)) & r2_hidden(sK24(X0,X1,X2),X2) & m1_subset_1(sK24(X0,X1,X2),u1_struct_0(X1))))),
% 5.07/1.05    introduced(choice_axiom,[])).
% 5.07/1.05  fof(f116,plain,(
% 5.07/1.05    ! [X0,X1,X2] : ((sP12(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP12(X0,X1,X2)))),
% 5.07/1.05    inference(rectify,[],[f115])).
% 5.07/1.05  fof(f115,plain,(
% 5.07/1.05    ! [X1,X0,X2] : ((sP12(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP12(X1,X0,X2)))),
% 5.07/1.05    inference(nnf_transformation,[],[f71])).
% 5.07/1.05  fof(f71,plain,(
% 5.07/1.05    ! [X1,X0,X2] : (sP12(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 5.07/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP12])])).
% 5.07/1.05  fof(f550,plain,(
% 5.07/1.05    ( ! [X0] : (sP12(k16_lattice3(sK16,X0),sK16,X0)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f545,f441])).
% 5.07/1.05  fof(f441,plain,(
% 5.07/1.05    ( ! [X34] : (sP13(sK16,k16_lattice3(sK16,X34))) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f440,f124])).
% 5.07/1.05  fof(f440,plain,(
% 5.07/1.05    ( ! [X34] : (sP13(sK16,k16_lattice3(sK16,X34)) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f403,f127])).
% 5.07/1.05  fof(f403,plain,(
% 5.07/1.05    ( ! [X34] : (sP13(sK16,k16_lattice3(sK16,X34)) | ~l3_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(resolution,[],[f270,f185])).
% 5.07/1.05  fof(f185,plain,(
% 5.07/1.05    ( ! [X0,X1] : (sP13(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f73])).
% 5.07/1.05  fof(f73,plain,(
% 5.07/1.05    ! [X0] : (! [X1] : (sP13(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 5.07/1.05    inference(definition_folding,[],[f45,f72,f71])).
% 5.07/1.05  fof(f72,plain,(
% 5.07/1.05    ! [X0,X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> sP12(X1,X0,X2)) | ~sP13(X0,X1))),
% 5.07/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP13])])).
% 5.07/1.05  fof(f45,plain,(
% 5.07/1.05    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 5.07/1.05    inference(flattening,[],[f44])).
% 5.07/1.05  fof(f44,plain,(
% 5.07/1.05    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 5.07/1.05    inference(ennf_transformation,[],[f9])).
% 5.07/1.05  fof(f9,axiom,(
% 5.07/1.05    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 5.07/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).
% 5.07/1.05  fof(f270,plain,(
% 5.07/1.05    ( ! [X10] : (m1_subset_1(k16_lattice3(sK16,X10),u1_struct_0(sK16))) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f250,f124])).
% 5.07/1.05  fof(f250,plain,(
% 5.07/1.05    ( ! [X10] : (m1_subset_1(k16_lattice3(sK16,X10),u1_struct_0(sK16)) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(resolution,[],[f127,f186])).
% 5.07/1.05  fof(f186,plain,(
% 5.07/1.05    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f47])).
% 5.07/1.05  fof(f47,plain,(
% 5.07/1.05    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 5.07/1.05    inference(flattening,[],[f46])).
% 5.07/1.05  fof(f46,plain,(
% 5.07/1.05    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 5.07/1.05    inference(ennf_transformation,[],[f12])).
% 5.07/1.05  fof(f12,axiom,(
% 5.07/1.05    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 5.07/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 5.07/1.05  fof(f545,plain,(
% 5.07/1.05    ( ! [X0] : (sP12(k16_lattice3(sK16,X0),sK16,X0) | ~sP13(sK16,k16_lattice3(sK16,X0))) )),
% 5.07/1.05    inference(resolution,[],[f534,f179])).
% 5.07/1.05  fof(f179,plain,(
% 5.07/1.05    ( ! [X2,X0,X1] : (sP12(X1,X0,X2) | ~r3_lattice3(X0,X1,X2) | ~sP13(X0,X1)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f114])).
% 5.07/1.05  fof(f114,plain,(
% 5.07/1.05    ! [X0,X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ~sP12(X1,X0,X2)) & (sP12(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) | ~sP13(X0,X1))),
% 5.07/1.05    inference(nnf_transformation,[],[f72])).
% 5.07/1.05  fof(f534,plain,(
% 5.07/1.05    ( ! [X0] : (r3_lattice3(sK16,k16_lattice3(sK16,X0),X0)) )),
% 5.07/1.05    inference(resolution,[],[f533,f167])).
% 5.07/1.05  fof(f167,plain,(
% 5.07/1.05    ( ! [X2,X0,X1] : (r3_lattice3(X1,X2,X0) | ~sP9(X0,X1,X2)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f105])).
% 5.07/1.05  fof(f105,plain,(
% 5.07/1.05    ! [X0,X1,X2] : ((sP9(X0,X1,X2) | ~sP8(X2,X1,X0) | ~r3_lattice3(X1,X2,X0)) & ((sP8(X2,X1,X0) & r3_lattice3(X1,X2,X0)) | ~sP9(X0,X1,X2)))),
% 5.07/1.05    inference(rectify,[],[f104])).
% 5.07/1.05  fof(f104,plain,(
% 5.07/1.05    ! [X2,X0,X1] : ((sP9(X2,X0,X1) | ~sP8(X1,X0,X2) | ~r3_lattice3(X0,X1,X2)) & ((sP8(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP9(X2,X0,X1)))),
% 5.07/1.05    inference(flattening,[],[f103])).
% 5.07/1.05  fof(f103,plain,(
% 5.07/1.05    ! [X2,X0,X1] : ((sP9(X2,X0,X1) | (~sP8(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) & ((sP8(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP9(X2,X0,X1)))),
% 5.07/1.05    inference(nnf_transformation,[],[f66])).
% 5.07/1.05  fof(f66,plain,(
% 5.07/1.05    ! [X2,X0,X1] : (sP9(X2,X0,X1) <=> (sP8(X1,X0,X2) & r3_lattice3(X0,X1,X2)))),
% 5.07/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).
% 5.07/1.05  fof(f533,plain,(
% 5.07/1.05    ( ! [X2] : (sP9(X2,sK16,k16_lattice3(sK16,X2))) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f532,f270])).
% 5.07/1.05  fof(f532,plain,(
% 5.07/1.05    ( ! [X2] : (~m1_subset_1(k16_lattice3(sK16,X2),u1_struct_0(sK16)) | sP9(X2,sK16,k16_lattice3(sK16,X2))) )),
% 5.07/1.05    inference(resolution,[],[f265,f197])).
% 5.07/1.05  fof(f197,plain,(
% 5.07/1.05    ( ! [X2,X1] : (sP9(X2,X1,k16_lattice3(X1,X2)) | ~sP10(k16_lattice3(X1,X2),X1)) )),
% 5.07/1.05    inference(equality_resolution,[],[f165])).
% 5.07/1.05  fof(f165,plain,(
% 5.07/1.05    ( ! [X2,X0,X1] : (sP9(X2,X1,X0) | k16_lattice3(X1,X2) != X0 | ~sP10(X0,X1)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f102])).
% 5.07/1.05  fof(f102,plain,(
% 5.07/1.05    ! [X0,X1] : (! [X2] : ((k16_lattice3(X1,X2) = X0 | ~sP9(X2,X1,X0)) & (sP9(X2,X1,X0) | k16_lattice3(X1,X2) != X0)) | ~sP10(X0,X1))),
% 5.07/1.05    inference(rectify,[],[f101])).
% 5.07/1.05  fof(f101,plain,(
% 5.07/1.05    ! [X1,X0] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ~sP9(X2,X0,X1)) & (sP9(X2,X0,X1) | k16_lattice3(X0,X2) != X1)) | ~sP10(X1,X0))),
% 5.07/1.05    inference(nnf_transformation,[],[f67])).
% 5.07/1.05  fof(f67,plain,(
% 5.07/1.05    ! [X1,X0] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> sP9(X2,X0,X1)) | ~sP10(X1,X0))),
% 5.07/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).
% 5.07/1.05  fof(f265,plain,(
% 5.07/1.05    ( ! [X6] : (sP10(X6,sK16) | ~m1_subset_1(X6,u1_struct_0(sK16))) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f264,f124])).
% 5.07/1.05  fof(f264,plain,(
% 5.07/1.05    ( ! [X6] : (sP10(X6,sK16) | ~m1_subset_1(X6,u1_struct_0(sK16)) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f263,f125])).
% 5.07/1.05  fof(f263,plain,(
% 5.07/1.05    ( ! [X6] : (sP10(X6,sK16) | ~m1_subset_1(X6,u1_struct_0(sK16)) | ~v10_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f247,f126])).
% 5.07/1.05  fof(f247,plain,(
% 5.07/1.05    ( ! [X6] : (sP10(X6,sK16) | ~m1_subset_1(X6,u1_struct_0(sK16)) | ~v4_lattice3(sK16) | ~v10_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(resolution,[],[f127,f174])).
% 5.07/1.05  fof(f174,plain,(
% 5.07/1.05    ( ! [X0,X1] : (sP10(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f68])).
% 5.07/1.05  fof(f68,plain,(
% 5.07/1.05    ! [X0] : (! [X1] : (sP10(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 5.07/1.05    inference(definition_folding,[],[f41,f67,f66,f65])).
% 5.07/1.05  fof(f65,plain,(
% 5.07/1.05    ! [X1,X0,X2] : (sP8(X1,X0,X2) <=> ! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 5.07/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 5.07/1.05  fof(f41,plain,(
% 5.07/1.05    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 5.07/1.05    inference(flattening,[],[f40])).
% 5.07/1.05  fof(f40,plain,(
% 5.07/1.05    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 5.07/1.05    inference(ennf_transformation,[],[f14])).
% 5.07/1.05  fof(f14,axiom,(
% 5.07/1.05    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 5.07/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).
% 5.07/1.05  fof(f4140,plain,(
% 5.07/1.05    r2_hidden(k5_lattices(sK16),a_2_4_lattice3(sK16,k15_lattice3(sK16,k1_xboole_0)))),
% 5.07/1.05    inference(subsumption_resolution,[],[f4138,f513])).
% 5.07/1.05  fof(f513,plain,(
% 5.07/1.05    ( ! [X35,X36] : (sP15(X35,sK16,k15_lattice3(sK16,X36))) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f512,f124])).
% 5.07/1.05  fof(f512,plain,(
% 5.07/1.05    ( ! [X35,X36] : (sP15(X35,sK16,k15_lattice3(sK16,X36)) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f511,f125])).
% 5.07/1.05  fof(f511,plain,(
% 5.07/1.05    ( ! [X35,X36] : (sP15(X35,sK16,k15_lattice3(sK16,X36)) | ~v10_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f510,f126])).
% 5.07/1.05  fof(f510,plain,(
% 5.07/1.05    ( ! [X35,X36] : (sP15(X35,sK16,k15_lattice3(sK16,X36)) | ~v4_lattice3(sK16) | ~v10_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f473,f127])).
% 5.07/1.05  fof(f473,plain,(
% 5.07/1.05    ( ! [X35,X36] : (sP15(X35,sK16,k15_lattice3(sK16,X36)) | ~l3_lattices(sK16) | ~v4_lattice3(sK16) | ~v10_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(resolution,[],[f271,f195])).
% 5.07/1.05  fof(f195,plain,(
% 5.07/1.05    ( ! [X2,X0,X1] : (sP15(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f76])).
% 5.07/1.05  fof(f76,plain,(
% 5.07/1.05    ! [X0,X1,X2] : (sP15(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 5.07/1.05    inference(definition_folding,[],[f52,f75,f74])).
% 5.07/1.05  fof(f74,plain,(
% 5.07/1.05    ! [X2,X1,X0] : (sP14(X2,X1,X0) <=> ? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 5.07/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP14])])).
% 5.07/1.05  fof(f75,plain,(
% 5.07/1.05    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_4_lattice3(X1,X2)) <=> sP14(X2,X1,X0)) | ~sP15(X0,X1,X2))),
% 5.07/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP15])])).
% 5.07/1.05  fof(f52,plain,(
% 5.07/1.05    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_4_lattice3(X1,X2)) <=> ? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 5.07/1.05    inference(flattening,[],[f51])).
% 5.07/1.05  fof(f51,plain,(
% 5.07/1.05    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_4_lattice3(X1,X2)) <=> ? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 5.07/1.05    inference(ennf_transformation,[],[f13])).
% 5.07/1.05  fof(f13,axiom,(
% 5.07/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_4_lattice3(X1,X2)) <=> ? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 5.07/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_4_lattice3)).
% 5.07/1.05  fof(f4138,plain,(
% 5.07/1.05    r2_hidden(k5_lattices(sK16),a_2_4_lattice3(sK16,k15_lattice3(sK16,k1_xboole_0))) | ~sP15(k5_lattices(sK16),sK16,k15_lattice3(sK16,k1_xboole_0))),
% 5.07/1.05    inference(resolution,[],[f4129,f190])).
% 5.07/1.05  fof(f190,plain,(
% 5.07/1.05    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_4_lattice3(X1,X2)) | ~sP14(X2,X1,X0) | ~sP15(X0,X1,X2)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f119])).
% 5.07/1.05  fof(f119,plain,(
% 5.07/1.05    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_4_lattice3(X1,X2)) | ~sP14(X2,X1,X0)) & (sP14(X2,X1,X0) | ~r2_hidden(X0,a_2_4_lattice3(X1,X2)))) | ~sP15(X0,X1,X2))),
% 5.07/1.05    inference(nnf_transformation,[],[f75])).
% 5.07/1.05  fof(f4129,plain,(
% 5.07/1.05    sP14(k15_lattice3(sK16,k1_xboole_0),sK16,k5_lattices(sK16))),
% 5.07/1.05    inference(resolution,[],[f4120,f337])).
% 5.07/1.05  fof(f337,plain,(
% 5.07/1.05    ( ! [X17] : (~r3_lattices(sK16,X17,k5_lattices(sK16)) | sP14(X17,sK16,k5_lattices(sK16))) )),
% 5.07/1.05    inference(resolution,[],[f282,f198])).
% 5.07/1.05  fof(f198,plain,(
% 5.07/1.05    ( ! [X0,X3,X1] : (sP14(X0,X1,X3) | ~r3_lattices(X1,X0,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 5.07/1.05    inference(equality_resolution,[],[f194])).
% 5.07/1.05  fof(f194,plain,(
% 5.07/1.05    ( ! [X2,X0,X3,X1] : (sP14(X0,X1,X2) | ~r3_lattices(X1,X0,X3) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 5.07/1.05    inference(cnf_transformation,[],[f123])).
% 5.07/1.05  fof(f123,plain,(
% 5.07/1.05    ! [X0,X1,X2] : ((sP14(X0,X1,X2) | ! [X3] : (~r3_lattices(X1,X0,X3) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattices(X1,X0,sK25(X0,X1,X2)) & sK25(X0,X1,X2) = X2 & m1_subset_1(sK25(X0,X1,X2),u1_struct_0(X1))) | ~sP14(X0,X1,X2)))),
% 5.07/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25])],[f121,f122])).
% 5.07/1.05  fof(f122,plain,(
% 5.07/1.05    ! [X2,X1,X0] : (? [X4] : (r3_lattices(X1,X0,X4) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattices(X1,X0,sK25(X0,X1,X2)) & sK25(X0,X1,X2) = X2 & m1_subset_1(sK25(X0,X1,X2),u1_struct_0(X1))))),
% 5.07/1.05    introduced(choice_axiom,[])).
% 5.07/1.05  fof(f121,plain,(
% 5.07/1.05    ! [X0,X1,X2] : ((sP14(X0,X1,X2) | ! [X3] : (~r3_lattices(X1,X0,X3) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattices(X1,X0,X4) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP14(X0,X1,X2)))),
% 5.07/1.05    inference(rectify,[],[f120])).
% 5.07/1.05  fof(f120,plain,(
% 5.07/1.05    ! [X2,X1,X0] : ((sP14(X2,X1,X0) | ! [X3] : (~r3_lattices(X1,X2,X3) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP14(X2,X1,X0)))),
% 5.07/1.05    inference(nnf_transformation,[],[f74])).
% 5.07/1.05  fof(f4120,plain,(
% 5.07/1.05    r3_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),k5_lattices(sK16))),
% 5.07/1.05    inference(superposition,[],[f4118,f362])).
% 5.07/1.05  fof(f362,plain,(
% 5.07/1.05    k5_lattices(sK16) = k15_lattice3(sK16,a_2_3_lattice3(sK16,k5_lattices(sK16)))),
% 5.07/1.05    inference(subsumption_resolution,[],[f361,f124])).
% 5.07/1.05  fof(f361,plain,(
% 5.07/1.05    k5_lattices(sK16) = k15_lattice3(sK16,a_2_3_lattice3(sK16,k5_lattices(sK16))) | v2_struct_0(sK16)),
% 5.07/1.05    inference(subsumption_resolution,[],[f360,f125])).
% 5.07/1.05  fof(f360,plain,(
% 5.07/1.05    k5_lattices(sK16) = k15_lattice3(sK16,a_2_3_lattice3(sK16,k5_lattices(sK16))) | ~v10_lattices(sK16) | v2_struct_0(sK16)),
% 5.07/1.05    inference(subsumption_resolution,[],[f359,f126])).
% 5.07/1.05  fof(f359,plain,(
% 5.07/1.05    k5_lattices(sK16) = k15_lattice3(sK16,a_2_3_lattice3(sK16,k5_lattices(sK16))) | ~v4_lattice3(sK16) | ~v10_lattices(sK16) | v2_struct_0(sK16)),
% 5.07/1.05    inference(subsumption_resolution,[],[f329,f127])).
% 5.07/1.05  fof(f329,plain,(
% 5.07/1.05    k5_lattices(sK16) = k15_lattice3(sK16,a_2_3_lattice3(sK16,k5_lattices(sK16))) | ~l3_lattices(sK16) | ~v4_lattice3(sK16) | ~v10_lattices(sK16) | v2_struct_0(sK16)),
% 5.07/1.05    inference(resolution,[],[f282,f163])).
% 5.07/1.05  fof(f163,plain,(
% 5.07/1.05    ( ! [X0,X1] : (k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f39])).
% 5.07/1.05  fof(f4118,plain,(
% 5.07/1.05    ( ! [X0] : (r3_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),k15_lattice3(sK16,X0))) )),
% 5.07/1.05    inference(resolution,[],[f1877,f129])).
% 5.07/1.05  fof(f129,plain,(
% 5.07/1.05    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f1])).
% 5.07/1.05  fof(f1,axiom,(
% 5.07/1.05    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 5.07/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 5.07/1.05  fof(f1877,plain,(
% 5.07/1.05    ( ! [X0,X1] : (~r1_tarski(X0,sK23(X1,sK16,X0)) | r3_lattices(sK16,k15_lattice3(sK16,X0),k15_lattice3(sK16,X1))) )),
% 5.07/1.05    inference(resolution,[],[f762,f188])).
% 5.07/1.05  fof(f188,plain,(
% 5.07/1.05    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f50])).
% 5.07/1.05  fof(f50,plain,(
% 5.07/1.05    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 5.07/1.05    inference(ennf_transformation,[],[f2])).
% 5.07/1.05  fof(f2,axiom,(
% 5.07/1.05    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 5.07/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 5.07/1.05  fof(f762,plain,(
% 5.07/1.05    ( ! [X2,X3] : (r2_hidden(sK23(X3,sK16,X2),X2) | r3_lattices(sK16,k15_lattice3(sK16,X2),k15_lattice3(sK16,X3))) )),
% 5.07/1.05    inference(resolution,[],[f268,f176])).
% 5.07/1.05  fof(f176,plain,(
% 5.07/1.05    ( ! [X2,X0,X1] : (r2_hidden(sK23(X0,X1,X2),X2) | ~sP11(X0,X1,X2)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f113])).
% 5.07/1.05  fof(f113,plain,(
% 5.07/1.05    ! [X0,X1,X2] : ((! [X4] : (~r2_hidden(X4,X0) | ~r3_lattices(X1,sK23(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & r2_hidden(sK23(X0,X1,X2),X2) & m1_subset_1(sK23(X0,X1,X2),u1_struct_0(X1))) | ~sP11(X0,X1,X2))),
% 5.07/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23])],[f111,f112])).
% 5.07/1.05  fof(f112,plain,(
% 5.07/1.05    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(X4,X0) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(X4,X0) | ~r3_lattices(X1,sK23(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & r2_hidden(sK23(X0,X1,X2),X2) & m1_subset_1(sK23(X0,X1,X2),u1_struct_0(X1))))),
% 5.07/1.05    introduced(choice_axiom,[])).
% 5.07/1.05  fof(f111,plain,(
% 5.07/1.05    ! [X0,X1,X2] : (? [X3] : (! [X4] : (~r2_hidden(X4,X0) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) | ~sP11(X0,X1,X2))),
% 5.07/1.05    inference(rectify,[],[f110])).
% 5.07/1.05  fof(f110,plain,(
% 5.07/1.05    ! [X2,X0,X1] : (? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~sP11(X2,X0,X1))),
% 5.07/1.05    inference(nnf_transformation,[],[f69])).
% 5.07/1.05  fof(f69,plain,(
% 5.07/1.05    ! [X2,X0,X1] : (? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~sP11(X2,X0,X1))),
% 5.07/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP11])])).
% 5.07/1.05  fof(f268,plain,(
% 5.07/1.05    ( ! [X8,X7] : (sP11(X8,sK16,X7) | r3_lattices(sK16,k15_lattice3(sK16,X7),k15_lattice3(sK16,X8))) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f267,f124])).
% 5.07/1.05  fof(f267,plain,(
% 5.07/1.05    ( ! [X8,X7] : (r3_lattices(sK16,k15_lattice3(sK16,X7),k15_lattice3(sK16,X8)) | sP11(X8,sK16,X7) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f266,f125])).
% 5.07/1.05  fof(f266,plain,(
% 5.07/1.05    ( ! [X8,X7] : (r3_lattices(sK16,k15_lattice3(sK16,X7),k15_lattice3(sK16,X8)) | sP11(X8,sK16,X7) | ~v10_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f248,f126])).
% 5.07/1.05  fof(f248,plain,(
% 5.07/1.05    ( ! [X8,X7] : (r3_lattices(sK16,k15_lattice3(sK16,X7),k15_lattice3(sK16,X8)) | sP11(X8,sK16,X7) | ~v4_lattice3(sK16) | ~v10_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(resolution,[],[f127,f178])).
% 5.07/1.05  fof(f178,plain,(
% 5.07/1.05    ( ! [X2,X0,X1] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | sP11(X2,X0,X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f70])).
% 5.07/1.05  fof(f70,plain,(
% 5.07/1.05    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | sP11(X2,X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 5.07/1.05    inference(definition_folding,[],[f43,f69])).
% 5.07/1.05  fof(f43,plain,(
% 5.07/1.05    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 5.07/1.05    inference(flattening,[],[f42])).
% 5.07/1.05  fof(f42,plain,(
% 5.07/1.05    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : ((! [X4] : ((~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1)) & m1_subset_1(X3,u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 5.07/1.05    inference(ennf_transformation,[],[f16])).
% 5.07/1.05  fof(f16,axiom,(
% 5.07/1.05    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 5.07/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).
% 5.07/1.05  fof(f11591,plain,(
% 5.07/1.05    ~m1_subset_1(sK19(k15_lattice3(sK16,k1_xboole_0),sK16),u1_struct_0(sK16))),
% 5.07/1.05    inference(resolution,[],[f11550,f4289])).
% 5.07/1.05  fof(f4289,plain,(
% 5.07/1.05    ( ! [X2] : (r1_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),X2) | ~m1_subset_1(X2,u1_struct_0(sK16))) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f4288,f124])).
% 5.07/1.05  fof(f4288,plain,(
% 5.07/1.05    ( ! [X2] : (r1_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),X2) | ~m1_subset_1(X2,u1_struct_0(sK16)) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f4287,f125])).
% 5.07/1.05  fof(f4287,plain,(
% 5.07/1.05    ( ! [X2] : (r1_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),X2) | ~m1_subset_1(X2,u1_struct_0(sK16)) | ~v10_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f4286,f126])).
% 5.07/1.05  fof(f4286,plain,(
% 5.07/1.05    ( ! [X2] : (r1_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),X2) | ~m1_subset_1(X2,u1_struct_0(sK16)) | ~v4_lattice3(sK16) | ~v10_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f4275,f127])).
% 5.07/1.05  fof(f4275,plain,(
% 5.07/1.05    ( ! [X2] : (r1_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),X2) | ~m1_subset_1(X2,u1_struct_0(sK16)) | ~l3_lattices(sK16) | ~v4_lattice3(sK16) | ~v10_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(superposition,[],[f4248,f163])).
% 5.07/1.05  fof(f4248,plain,(
% 5.07/1.05    ( ! [X1] : (r1_lattices(sK16,k15_lattice3(sK16,k1_xboole_0),k15_lattice3(sK16,X1))) )),
% 5.07/1.05    inference(forward_demodulation,[],[f4247,f503])).
% 5.07/1.05  fof(f4247,plain,(
% 5.07/1.05    ( ! [X1] : (r1_lattices(sK16,k16_lattice3(sK16,a_2_4_lattice3(sK16,k15_lattice3(sK16,k1_xboole_0))),k15_lattice3(sK16,X1))) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f4238,f271])).
% 5.07/1.05  fof(f4238,plain,(
% 5.07/1.05    ( ! [X1] : (r1_lattices(sK16,k16_lattice3(sK16,a_2_4_lattice3(sK16,k15_lattice3(sK16,k1_xboole_0))),k15_lattice3(sK16,X1)) | ~m1_subset_1(k15_lattice3(sK16,X1),u1_struct_0(sK16))) )),
% 5.07/1.05    inference(resolution,[],[f4192,f572])).
% 5.07/1.05  fof(f4192,plain,(
% 5.07/1.05    ( ! [X5] : (r2_hidden(k15_lattice3(sK16,X5),a_2_4_lattice3(sK16,k15_lattice3(sK16,k1_xboole_0)))) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f4187,f513])).
% 5.07/1.05  fof(f4187,plain,(
% 5.07/1.05    ( ! [X5] : (r2_hidden(k15_lattice3(sK16,X5),a_2_4_lattice3(sK16,k15_lattice3(sK16,k1_xboole_0))) | ~sP15(k15_lattice3(sK16,X5),sK16,k15_lattice3(sK16,k1_xboole_0))) )),
% 5.07/1.05    inference(resolution,[],[f4124,f190])).
% 5.07/1.05  fof(f4124,plain,(
% 5.07/1.05    ( ! [X0] : (sP14(k15_lattice3(sK16,k1_xboole_0),sK16,k15_lattice3(sK16,X0))) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f4119,f271])).
% 5.07/1.05  fof(f4119,plain,(
% 5.07/1.05    ( ! [X0] : (sP14(k15_lattice3(sK16,k1_xboole_0),sK16,k15_lattice3(sK16,X0)) | ~m1_subset_1(k15_lattice3(sK16,X0),u1_struct_0(sK16))) )),
% 5.07/1.05    inference(resolution,[],[f4118,f198])).
% 5.07/1.05  fof(f11550,plain,(
% 5.07/1.05    ( ! [X0] : (~r1_lattices(sK16,k15_lattice3(sK16,X0),sK19(k15_lattice3(sK16,X0),sK16))) )),
% 5.07/1.05    inference(superposition,[],[f10606,f503])).
% 5.07/1.05  fof(f10606,plain,(
% 5.07/1.05    ( ! [X5] : (~r1_lattices(sK16,k16_lattice3(sK16,X5),sK19(k16_lattice3(sK16,X5),sK16))) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f10605,f124])).
% 5.07/1.05  fof(f10605,plain,(
% 5.07/1.05    ( ! [X5] : (~r1_lattices(sK16,k16_lattice3(sK16,X5),sK19(k16_lattice3(sK16,X5),sK16)) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f10604,f285])).
% 5.07/1.05  fof(f10604,plain,(
% 5.07/1.05    ( ! [X5] : (~r1_lattices(sK16,k16_lattice3(sK16,X5),sK19(k16_lattice3(sK16,X5),sK16)) | ~v8_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f10603,f286])).
% 5.07/1.05  fof(f10603,plain,(
% 5.07/1.05    ( ! [X5] : (~r1_lattices(sK16,k16_lattice3(sK16,X5),sK19(k16_lattice3(sK16,X5),sK16)) | ~v9_lattices(sK16) | ~v8_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f10602,f127])).
% 5.07/1.05  fof(f10602,plain,(
% 5.07/1.05    ( ! [X5] : (~r1_lattices(sK16,k16_lattice3(sK16,X5),sK19(k16_lattice3(sK16,X5),sK16)) | ~l3_lattices(sK16) | ~v9_lattices(sK16) | ~v8_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f10601,f270])).
% 5.07/1.05  fof(f10601,plain,(
% 5.07/1.05    ( ! [X5] : (~r1_lattices(sK16,k16_lattice3(sK16,X5),sK19(k16_lattice3(sK16,X5),sK16)) | ~m1_subset_1(k16_lattice3(sK16,X5),u1_struct_0(sK16)) | ~l3_lattices(sK16) | ~v9_lattices(sK16) | ~v8_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f10590,f5108])).
% 5.07/1.05  fof(f5108,plain,(
% 5.07/1.05    ( ! [X2] : (m1_subset_1(sK19(k16_lattice3(sK16,X2),sK16),u1_struct_0(sK16))) )),
% 5.07/1.05    inference(resolution,[],[f5104,f153])).
% 5.07/1.05  fof(f5104,plain,(
% 5.07/1.05    ( ! [X2] : (~sP3(k16_lattice3(sK16,X2),sK16)) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f5095,f625])).
% 5.07/1.05  fof(f625,plain,(
% 5.07/1.05    ( ! [X1] : (k5_lattices(sK16) != k15_lattice3(sK16,k1_xboole_0) | ~sP3(k16_lattice3(sK16,X1),sK16)) )),
% 5.07/1.05    inference(resolution,[],[f303,f392])).
% 5.07/1.05  fof(f392,plain,(
% 5.07/1.05    ( ! [X13] : (sP4(sK16) | ~sP3(k16_lattice3(sK16,X13),sK16)) )),
% 5.07/1.05    inference(resolution,[],[f270,f150])).
% 5.07/1.05  fof(f5095,plain,(
% 5.07/1.05    ( ! [X2] : (k5_lattices(sK16) = k15_lattice3(sK16,k1_xboole_0) | ~sP3(k16_lattice3(sK16,X2),sK16)) )),
% 5.07/1.05    inference(resolution,[],[f4915,f717])).
% 5.07/1.05  fof(f717,plain,(
% 5.07/1.05    ( ! [X1] : (sP1(k5_lattices(sK16),sK16) | ~sP3(k16_lattice3(sK16,X1),sK16)) )),
% 5.07/1.05    inference(resolution,[],[f715,f392])).
% 5.07/1.05  fof(f10590,plain,(
% 5.07/1.05    ( ! [X5] : (~r1_lattices(sK16,k16_lattice3(sK16,X5),sK19(k16_lattice3(sK16,X5),sK16)) | ~m1_subset_1(sK19(k16_lattice3(sK16,X5),sK16),u1_struct_0(sK16)) | ~m1_subset_1(k16_lattice3(sK16,X5),u1_struct_0(sK16)) | ~l3_lattices(sK16) | ~v9_lattices(sK16) | ~v8_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(trivial_inequality_removal,[],[f10583])).
% 5.07/1.05  fof(f10583,plain,(
% 5.07/1.05    ( ! [X5] : (k16_lattice3(sK16,X5) != k16_lattice3(sK16,X5) | ~r1_lattices(sK16,k16_lattice3(sK16,X5),sK19(k16_lattice3(sK16,X5),sK16)) | ~m1_subset_1(sK19(k16_lattice3(sK16,X5),sK16),u1_struct_0(sK16)) | ~m1_subset_1(k16_lattice3(sK16,X5),u1_struct_0(sK16)) | ~l3_lattices(sK16) | ~v9_lattices(sK16) | ~v8_lattices(sK16) | v2_struct_0(sK16)) )),
% 5.07/1.05    inference(superposition,[],[f9747,f136])).
% 5.07/1.05  fof(f9747,plain,(
% 5.07/1.05    ( ! [X8] : (k16_lattice3(sK16,X8) != k2_lattices(sK16,k16_lattice3(sK16,X8),sK19(k16_lattice3(sK16,X8),sK16))) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f9718,f5104])).
% 5.07/1.05  fof(f9718,plain,(
% 5.07/1.05    ( ! [X8] : (k16_lattice3(sK16,X8) != k2_lattices(sK16,k16_lattice3(sK16,X8),sK19(k16_lattice3(sK16,X8),sK16)) | sP3(k16_lattice3(sK16,X8),sK16)) )),
% 5.07/1.05    inference(duplicate_literal_removal,[],[f9711])).
% 5.07/1.05  fof(f9711,plain,(
% 5.07/1.05    ( ! [X8] : (k16_lattice3(sK16,X8) != k2_lattices(sK16,k16_lattice3(sK16,X8),sK19(k16_lattice3(sK16,X8),sK16)) | sP3(k16_lattice3(sK16,X8),sK16) | k16_lattice3(sK16,X8) != k2_lattices(sK16,k16_lattice3(sK16,X8),sK19(k16_lattice3(sK16,X8),sK16)) | sP3(k16_lattice3(sK16,X8),sK16)) )),
% 5.07/1.05    inference(superposition,[],[f154,f2074])).
% 5.07/1.05  fof(f2074,plain,(
% 5.07/1.05    ( ! [X14,X13] : (k2_lattices(sK16,k16_lattice3(sK16,X13),sK19(X14,sK16)) = k2_lattices(sK16,sK19(X14,sK16),k16_lattice3(sK16,X13)) | sP3(X14,sK16)) )),
% 5.07/1.05    inference(resolution,[],[f426,f153])).
% 5.07/1.05  fof(f426,plain,(
% 5.07/1.05    ( ! [X19,X18] : (~m1_subset_1(X19,u1_struct_0(sK16)) | k2_lattices(sK16,k16_lattice3(sK16,X18),X19) = k2_lattices(sK16,X19,k16_lattice3(sK16,X18))) )),
% 5.07/1.05    inference(subsumption_resolution,[],[f395,f295])).
% 5.07/1.05  fof(f295,plain,(
% 5.07/1.05    sP6(sK16)),
% 5.07/1.05    inference(subsumption_resolution,[],[f294,f279])).
% 5.07/1.05  fof(f279,plain,(
% 5.07/1.05    sP7(sK16)),
% 5.07/1.05    inference(subsumption_resolution,[],[f275,f124])).
% 5.07/1.05  fof(f275,plain,(
% 5.07/1.05    sP7(sK16) | v2_struct_0(sK16)),
% 5.07/1.05    inference(resolution,[],[f241,f162])).
% 5.07/1.05  fof(f162,plain,(
% 5.07/1.05    ( ! [X0] : (sP7(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f64])).
% 5.07/1.05  fof(f64,plain,(
% 5.07/1.05    ! [X0] : (sP7(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.07/1.05    inference(definition_folding,[],[f37,f63,f62])).
% 5.07/1.05  fof(f62,plain,(
% 5.07/1.05    ! [X0] : (sP6(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))))),
% 5.07/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 5.07/1.05  fof(f63,plain,(
% 5.07/1.05    ! [X0] : ((v6_lattices(X0) <=> sP6(X0)) | ~sP7(X0))),
% 5.07/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 5.07/1.05  fof(f37,plain,(
% 5.07/1.05    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.07/1.05    inference(flattening,[],[f36])).
% 5.07/1.05  fof(f36,plain,(
% 5.07/1.05    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 5.07/1.05    inference(ennf_transformation,[],[f10])).
% 5.07/1.05  fof(f10,axiom,(
% 5.07/1.05    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 5.07/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).
% 5.07/1.05  fof(f294,plain,(
% 5.07/1.05    sP6(sK16) | ~sP7(sK16)),
% 5.07/1.05    inference(resolution,[],[f284,f156])).
% 5.07/1.05  fof(f156,plain,(
% 5.07/1.05    ( ! [X0] : (sP6(X0) | ~v6_lattices(X0) | ~sP7(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f95])).
% 5.07/1.05  fof(f95,plain,(
% 5.07/1.05    ! [X0] : (((v6_lattices(X0) | ~sP6(X0)) & (sP6(X0) | ~v6_lattices(X0))) | ~sP7(X0))),
% 5.07/1.05    inference(nnf_transformation,[],[f63])).
% 5.07/1.05  fof(f284,plain,(
% 5.07/1.05    v6_lattices(sK16)),
% 5.07/1.05    inference(resolution,[],[f254,f132])).
% 5.07/1.05  fof(f132,plain,(
% 5.07/1.05    ( ! [X0] : (v6_lattices(X0) | ~sP0(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f79])).
% 5.07/1.05  fof(f395,plain,(
% 5.07/1.05    ( ! [X19,X18] : (k2_lattices(sK16,k16_lattice3(sK16,X18),X19) = k2_lattices(sK16,X19,k16_lattice3(sK16,X18)) | ~m1_subset_1(X19,u1_struct_0(sK16)) | ~sP6(sK16)) )),
% 5.07/1.05    inference(resolution,[],[f270,f158])).
% 5.07/1.05  fof(f158,plain,(
% 5.07/1.05    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~sP6(X0)) )),
% 5.07/1.05    inference(cnf_transformation,[],[f100])).
% 5.07/1.05  fof(f100,plain,(
% 5.07/1.05    ! [X0] : ((sP6(X0) | ((k2_lattices(X0,sK20(X0),sK21(X0)) != k2_lattices(X0,sK21(X0),sK20(X0)) & m1_subset_1(sK21(X0),u1_struct_0(X0))) & m1_subset_1(sK20(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP6(X0)))),
% 5.07/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20,sK21])],[f97,f99,f98])).
% 5.07/1.05  fof(f98,plain,(
% 5.07/1.05    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK20(X0),X2) != k2_lattices(X0,X2,sK20(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK20(X0),u1_struct_0(X0))))),
% 5.07/1.05    introduced(choice_axiom,[])).
% 5.07/1.05  fof(f99,plain,(
% 5.07/1.05    ! [X0] : (? [X2] : (k2_lattices(X0,sK20(X0),X2) != k2_lattices(X0,X2,sK20(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK20(X0),sK21(X0)) != k2_lattices(X0,sK21(X0),sK20(X0)) & m1_subset_1(sK21(X0),u1_struct_0(X0))))),
% 5.07/1.05    introduced(choice_axiom,[])).
% 5.07/1.05  fof(f97,plain,(
% 5.07/1.05    ! [X0] : ((sP6(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,X4) = k2_lattices(X0,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP6(X0)))),
% 5.07/1.05    inference(rectify,[],[f96])).
% 5.07/1.05  fof(f96,plain,(
% 5.07/1.05    ! [X0] : ((sP6(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~sP6(X0)))),
% 5.07/1.05    inference(nnf_transformation,[],[f62])).
% 5.07/1.05  fof(f154,plain,(
% 5.07/1.05    ( ! [X0,X1] : (sP3(X0,X1) | k2_lattices(X1,sK19(X0,X1),X0) != X0 | k2_lattices(X1,X0,sK19(X0,X1)) != X0) )),
% 5.07/1.05    inference(cnf_transformation,[],[f94])).
% 5.07/1.05  % SZS output end Proof for theBenchmark
% 5.07/1.05  % (24598)------------------------------
% 5.07/1.05  % (24598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.07/1.05  % (24598)Termination reason: Refutation
% 5.07/1.05  
% 5.07/1.05  % (24598)Memory used [KB]: 5500
% 5.07/1.05  % (24598)Time elapsed: 0.632 s
% 5.07/1.05  % (24598)------------------------------
% 5.07/1.05  % (24598)------------------------------
% 5.07/1.05  % (24589)Success in time 0.702 s
%------------------------------------------------------------------------------
