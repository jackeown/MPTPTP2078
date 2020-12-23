%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1516+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:59 EST 2020

% Result     : Theorem 17.58s
% Output     : Refutation 17.58s
% Verified   : 
% Statistics : Number of formulae       :  261 (3491 expanded)
%              Number of leaves         :   27 ( 817 expanded)
%              Depth                    :   36
%              Number of atoms          : 1346 (26450 expanded)
%              Number of equality atoms :  167 (2724 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47375,plain,(
    $false ),
    inference(resolution,[],[f47299,f81])).

fof(f81,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f47299,plain,(
    ! [X0] : ~ v1_xboole_0(X0) ),
    inference(resolution,[],[f47298,f110])).

fof(f110,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f12,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f47298,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f47165,f121])).

fof(f121,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP7(X1) ) ),
    inference(cnf_transformation,[],[f121_D])).

fof(f121_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP7(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f47165,plain,(
    ! [X437] : ~ sP7(X437) ),
    inference(subsumption_resolution,[],[f47164,f25578])).

fof(f25578,plain,(
    ! [X35] :
      ( m1_subset_1(sK2(sK0,k15_lattice3(sK0,X35)),u1_struct_0(sK0))
      | ~ sP7(X35) ) ),
    inference(subsumption_resolution,[],[f25513,f246])).

fof(f246,plain,(
    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f233,f76])).

fof(f76,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f54])).

fof(f54,plain,
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f233,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f187,f91])).

fof(f91,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f187,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f79,f83])).

fof(f83,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f79,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f25513,plain,(
    ! [X35] :
      ( m1_subset_1(sK2(sK0,k15_lattice3(sK0,X35)),u1_struct_0(sK0))
      | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
      | ~ sP7(X35) ) ),
    inference(superposition,[],[f14243,f25342])).

fof(f25342,plain,(
    ! [X4] :
      ( k15_lattice3(sK0,X4) = k4_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X4))
      | ~ sP7(X4) ) ),
    inference(subsumption_resolution,[],[f25341,f246])).

fof(f25341,plain,(
    ! [X4] :
      ( ~ sP7(X4)
      | k15_lattice3(sK0,X4) = k4_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X4))
      | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f25339,f214])).

fof(f214,plain,(
    ! [X11] : m1_subset_1(k15_lattice3(sK0,X11),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f197,f76])).

fof(f197,plain,(
    ! [X11] :
      ( m1_subset_1(k15_lattice3(sK0,X11),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f79,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f25339,plain,(
    ! [X4] :
      ( ~ sP7(X4)
      | ~ m1_subset_1(k15_lattice3(sK0,X4),u1_struct_0(sK0))
      | k15_lattice3(sK0,X4) = k4_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X4))
      | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f25299])).

fof(f25299,plain,(
    ! [X4] :
      ( ~ sP7(X4)
      | ~ m1_subset_1(k15_lattice3(sK0,X4),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,X4),u1_struct_0(sK0))
      | k15_lattice3(sK0,X4) = k4_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X4))
      | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f11940,f3996])).

fof(f3996,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X1,k4_lattices(sK0,X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,X0,X1) = X1
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3995,f1285])).

fof(f1285,plain,(
    ! [X21,X20] :
      ( m1_subset_1(k4_lattices(sK0,X20,X21),u1_struct_0(sK0))
      | ~ m1_subset_1(X21,u1_struct_0(sK0))
      | ~ m1_subset_1(X20,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1284,f206])).

fof(f206,plain,(
    v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f205,f76])).

fof(f205,plain,
    ( v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f190,f77])).

fof(f77,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f190,plain,
    ( v6_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f79,f87])).

fof(f87,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,plain,(
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

fof(f1284,plain,(
    ! [X21,X20] :
      ( m1_subset_1(k4_lattices(sK0,X20,X21),u1_struct_0(sK0))
      | ~ m1_subset_1(X21,u1_struct_0(sK0))
      | ~ m1_subset_1(X20,u1_struct_0(sK0))
      | ~ v6_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f146,f187])).

fof(f146,plain,(
    ! [X21,X20] :
      ( m1_subset_1(k4_lattices(sK0,X20,X21),u1_struct_0(sK0))
      | ~ m1_subset_1(X21,u1_struct_0(sK0))
      | ~ m1_subset_1(X20,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0) ) ),
    inference(resolution,[],[f76,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(f3995,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,X0,X1) = X1
      | ~ r1_lattices(sK0,X1,k4_lattices(sK0,X0,X1))
      | ~ m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f3974])).

fof(f3974,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,X0,X1) = X1
      | ~ r1_lattices(sK0,X1,k4_lattices(sK0,X0,X1))
      | ~ m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f1443,f2018])).

fof(f2018,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X1,X0)
      | X0 = X1
      | ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f2017,f204])).

fof(f204,plain,(
    v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f203,f76])).

fof(f203,plain,
    ( v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f189,f77])).

fof(f189,plain,
    ( v4_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f79,f86])).

fof(f86,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2017,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_lattices(sK0,X1,X0)
      | ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f131,f188])).

fof(f188,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f79,f84])).

fof(f84,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f131,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_lattices(sK0,X1,X0)
      | ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0) ) ),
    inference(resolution,[],[f76,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_lattices(X0,X2,X1)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).

fof(f1443,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k4_lattices(sK0,X1,X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1442,f76])).

fof(f1442,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k4_lattices(sK0,X1,X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1441,f206])).

fof(f1441,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k4_lattices(sK0,X1,X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1430,f187])).

fof(f1430,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k4_lattices(sK0,X1,X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1427])).

fof(f1427,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k4_lattices(sK0,X1,X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f1396,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f1396,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k4_lattices(sK0,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1395,f206])).

fof(f1395,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k4_lattices(sK0,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v6_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f209,f208])).

fof(f208,plain,(
    v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f207,f76])).

fof(f207,plain,
    ( v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f191,f77])).

fof(f191,plain,
    ( v8_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f79,f88])).

fof(f88,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f209,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k4_lattices(sK0,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f192,f76])).

fof(f192,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k4_lattices(sK0,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f79,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).

fof(f11940,plain,(
    ! [X10,X9] :
      ( r1_lattices(sK0,k15_lattice3(sK0,X10),k4_lattices(sK0,k5_lattices(sK0),X9))
      | ~ sP7(X10)
      | ~ m1_subset_1(X9,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f11939,f365])).

fof(f365,plain,(
    ! [X13] :
      ( m1_subset_1(k4_lattices(sK0,k5_lattices(sK0),X13),u1_struct_0(sK0))
      | ~ m1_subset_1(X13,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f364,f76])).

fof(f364,plain,(
    ! [X13] :
      ( m1_subset_1(k4_lattices(sK0,k5_lattices(sK0),X13),u1_struct_0(sK0))
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f363,f206])).

fof(f363,plain,(
    ! [X13] :
      ( m1_subset_1(k4_lattices(sK0,k5_lattices(sK0),X13),u1_struct_0(sK0))
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f313,f187])).

fof(f313,plain,(
    ! [X13] :
      ( m1_subset_1(k4_lattices(sK0,k5_lattices(sK0),X13),u1_struct_0(sK0))
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f246,f113])).

fof(f11939,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ sP7(X10)
      | r1_lattices(sK0,k15_lattice3(sK0,X10),k4_lattices(sK0,k5_lattices(sK0),X9))
      | ~ m1_subset_1(k4_lattices(sK0,k5_lattices(sK0),X9),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f11938,f76])).

fof(f11938,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ sP7(X10)
      | r1_lattices(sK0,k15_lattice3(sK0,X10),k4_lattices(sK0,k5_lattices(sK0),X9))
      | ~ m1_subset_1(k4_lattices(sK0,k5_lattices(sK0),X9),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f11937,f77])).

fof(f11937,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ sP7(X10)
      | r1_lattices(sK0,k15_lattice3(sK0,X10),k4_lattices(sK0,k5_lattices(sK0),X9))
      | ~ m1_subset_1(k4_lattices(sK0,k5_lattices(sK0),X9),u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f11936,f78])).

fof(f78,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f11936,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ sP7(X10)
      | r1_lattices(sK0,k15_lattice3(sK0,X10),k4_lattices(sK0,k5_lattices(sK0),X9))
      | ~ m1_subset_1(k4_lattices(sK0,k5_lattices(sK0),X9),u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f11935,f79])).

fof(f11935,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ sP7(X10)
      | r1_lattices(sK0,k15_lattice3(sK0,X10),k4_lattices(sK0,k5_lattices(sK0),X9))
      | ~ m1_subset_1(k4_lattices(sK0,k5_lattices(sK0),X9),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f11914,f214])).

fof(f11914,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ sP7(X10)
      | r1_lattices(sK0,k15_lattice3(sK0,X10),k4_lattices(sK0,k5_lattices(sK0),X9))
      | ~ m1_subset_1(k4_lattices(sK0,k5_lattices(sK0),X9),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,X10),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f9591,f126])).

fof(f126,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X2,X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
                & r4_lattice3(X0,sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f67,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
        & r4_lattice3(X0,sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
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
    inference(rectify,[],[f66])).

fof(f66,plain,(
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
    inference(flattening,[],[f65])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

fof(f9591,plain,(
    ! [X0,X1] :
      ( r4_lattice3(sK0,k4_lattices(sK0,k5_lattices(sK0),X0),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ sP7(X1) ) ),
    inference(resolution,[],[f365,f773])).

fof(f773,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | r4_lattice3(sK0,X6,X7)
      | ~ sP7(X7) ) ),
    inference(resolution,[],[f212,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP7(X1) ) ),
    inference(general_splitting,[],[f116,f121_D])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f212,plain,(
    ! [X8,X7] :
      ( r2_hidden(sK5(sK0,X7,X8),X8)
      | r4_lattice3(sK0,X7,X8)
      | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f195,f76])).

fof(f195,plain,(
    ! [X8,X7] :
      ( r4_lattice3(sK0,X7,X8)
      | r2_hidden(sK5(sK0,X7,X8),X8)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f79,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK5(X0,X1,X2),X1)
                  & r2_hidden(sK5(X0,X1,X2),X2)
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f71,f72])).

fof(f72,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK5(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),X2)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
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
    inference(rectify,[],[f70])).

fof(f70,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

fof(f14243,plain,(
    ! [X26,X27] :
      ( m1_subset_1(sK2(sK0,k4_lattices(sK0,X26,k15_lattice3(sK0,X27))),u1_struct_0(sK0))
      | ~ m1_subset_1(X26,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f2644,f6188])).

fof(f6188,plain,(
    ~ v13_lattices(sK0) ),
    inference(resolution,[],[f5941,f81])).

fof(f5941,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ v13_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f5925,f1248])).

fof(f1248,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,k5_lattices(sK0),X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f771,f246])).

fof(f771,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r4_lattice3(sK0,X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f212,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f5925,plain,(
    ! [X0] :
      ( ~ r4_lattice3(sK0,k5_lattices(sK0),X0)
      | ~ v13_lattices(sK0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f5774,f82])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f5774,plain,
    ( ~ r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0)
    | ~ v13_lattices(sK0) ),
    inference(subsumption_resolution,[],[f5773,f1922])).

fof(f1922,plain,
    ( m1_subset_1(sK4(sK0,k1_xboole_0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ v13_lattices(sK0)
    | ~ r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1915,f246])).

fof(f1915,plain,
    ( ~ v13_lattices(sK0)
    | m1_subset_1(sK4(sK0,k1_xboole_0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(equality_resolution,[],[f266])).

fof(f266,plain,(
    ! [X0] :
      ( k5_lattices(sK0) != X0
      | ~ v13_lattices(sK0)
      | m1_subset_1(sK4(sK0,k1_xboole_0,X0),u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X0,k1_xboole_0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f265,f76])).

fof(f265,plain,(
    ! [X0] :
      ( k5_lattices(sK0) != X0
      | ~ v13_lattices(sK0)
      | m1_subset_1(sK4(sK0,k1_xboole_0,X0),u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X0,k1_xboole_0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f264,f77])).

fof(f264,plain,(
    ! [X0] :
      ( k5_lattices(sK0) != X0
      | ~ v13_lattices(sK0)
      | m1_subset_1(sK4(sK0,k1_xboole_0,X0),u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X0,k1_xboole_0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f263,f78])).

fof(f263,plain,(
    ! [X0] :
      ( k5_lattices(sK0) != X0
      | ~ v13_lattices(sK0)
      | m1_subset_1(sK4(sK0,k1_xboole_0,X0),u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X0,k1_xboole_0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f260,f79])).

fof(f260,plain,(
    ! [X0] :
      ( k5_lattices(sK0) != X0
      | ~ v13_lattices(sK0)
      | m1_subset_1(sK4(sK0,k1_xboole_0,X0),u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X0,k1_xboole_0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f232,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f232,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0) ),
    inference(subsumption_resolution,[],[f231,f76])).

fof(f231,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f230,f77])).

fof(f230,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f80,f79])).

fof(f80,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f5773,plain,
    ( ~ m1_subset_1(sK4(sK0,k1_xboole_0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ v13_lattices(sK0)
    | ~ r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f5759])).

fof(f5759,plain,
    ( ~ m1_subset_1(sK4(sK0,k1_xboole_0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ v13_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0) ),
    inference(resolution,[],[f3519,f1942])).

fof(f1942,plain,
    ( ~ r1_lattices(sK0,k5_lattices(sK0),sK4(sK0,k1_xboole_0,k5_lattices(sK0)))
    | ~ v13_lattices(sK0)
    | ~ r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1935,f246])).

fof(f1935,plain,
    ( ~ v13_lattices(sK0)
    | ~ r1_lattices(sK0,k5_lattices(sK0),sK4(sK0,k1_xboole_0,k5_lattices(sK0)))
    | ~ r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(equality_resolution,[],[f274])).

fof(f274,plain,(
    ! [X2] :
      ( k5_lattices(sK0) != X2
      | ~ v13_lattices(sK0)
      | ~ r1_lattices(sK0,X2,sK4(sK0,k1_xboole_0,X2))
      | ~ r4_lattice3(sK0,X2,k1_xboole_0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f273,f76])).

fof(f273,plain,(
    ! [X2] :
      ( k5_lattices(sK0) != X2
      | ~ v13_lattices(sK0)
      | ~ r1_lattices(sK0,X2,sK4(sK0,k1_xboole_0,X2))
      | ~ r4_lattice3(sK0,X2,k1_xboole_0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f272,f77])).

fof(f272,plain,(
    ! [X2] :
      ( k5_lattices(sK0) != X2
      | ~ v13_lattices(sK0)
      | ~ r1_lattices(sK0,X2,sK4(sK0,k1_xboole_0,X2))
      | ~ r4_lattice3(sK0,X2,k1_xboole_0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f271,f78])).

fof(f271,plain,(
    ! [X2] :
      ( k5_lattices(sK0) != X2
      | ~ v13_lattices(sK0)
      | ~ r1_lattices(sK0,X2,sK4(sK0,k1_xboole_0,X2))
      | ~ r4_lattice3(sK0,X2,k1_xboole_0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f262,f79])).

fof(f262,plain,(
    ! [X2] :
      ( k5_lattices(sK0) != X2
      | ~ v13_lattices(sK0)
      | ~ r1_lattices(sK0,X2,sK4(sK0,k1_xboole_0,X2))
      | ~ r4_lattice3(sK0,X2,k1_xboole_0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f232,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f3519,plain,(
    ! [X2] :
      ( r1_lattices(sK0,k5_lattices(sK0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v13_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f3493,f246])).

fof(f3493,plain,(
    ! [X2] :
      ( r1_lattices(sK0,k5_lattices(sK0),X2)
      | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v13_lattices(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3477])).

fof(f3477,plain,(
    ! [X2] :
      ( r1_lattices(sK0,k5_lattices(sK0),X2)
      | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v13_lattices(sK0) ) ),
    inference(superposition,[],[f1396,f1746])).

fof(f1746,plain,(
    ! [X4] :
      ( k5_lattices(sK0) = k4_lattices(sK0,X4,k5_lattices(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ v13_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f1745,f76])).

fof(f1745,plain,(
    ! [X4] :
      ( k5_lattices(sK0) = k4_lattices(sK0,X4,k5_lattices(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ v13_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1744,f187])).

fof(f1744,plain,(
    ! [X4] :
      ( k5_lattices(sK0) = k4_lattices(sK0,X4,k5_lattices(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ v13_lattices(sK0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1739,f246])).

fof(f1739,plain,(
    ! [X4] :
      ( k5_lattices(sK0) = k4_lattices(sK0,X4,k5_lattices(sK0))
      | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ v13_lattices(sK0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1712])).

fof(f1712,plain,(
    ! [X4] :
      ( k5_lattices(sK0) = k4_lattices(sK0,X4,k5_lattices(sK0))
      | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
      | ~ v13_lattices(sK0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f1709,f117])).

fof(f117,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f57,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f1709,plain,(
    ! [X23,X22] :
      ( k4_lattices(sK0,X22,X23) = k2_lattices(sK0,X22,X23)
      | ~ m1_subset_1(X23,u1_struct_0(sK0))
      | ~ m1_subset_1(X22,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1708,f206])).

fof(f1708,plain,(
    ! [X23,X22] :
      ( k4_lattices(sK0,X22,X23) = k2_lattices(sK0,X22,X23)
      | ~ m1_subset_1(X23,u1_struct_0(sK0))
      | ~ m1_subset_1(X22,u1_struct_0(sK0))
      | ~ v6_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f147,f187])).

fof(f147,plain,(
    ! [X23,X22] :
      ( k4_lattices(sK0,X22,X23) = k2_lattices(sK0,X22,X23)
      | ~ m1_subset_1(X23,u1_struct_0(sK0))
      | ~ m1_subset_1(X22,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0) ) ),
    inference(resolution,[],[f76,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f2644,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X26,u1_struct_0(sK0))
      | v13_lattices(sK0)
      | m1_subset_1(sK2(sK0,k4_lattices(sK0,X26,k15_lattice3(sK0,X27))),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f2643,f76])).

fof(f2643,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X26,u1_struct_0(sK0))
      | v13_lattices(sK0)
      | m1_subset_1(sK2(sK0,k4_lattices(sK0,X26,k15_lattice3(sK0,X27))),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2591,f187])).

fof(f2591,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X26,u1_struct_0(sK0))
      | v13_lattices(sK0)
      | m1_subset_1(sK2(sK0,k4_lattices(sK0,X26,k15_lattice3(sK0,X27))),u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f484,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f61,f63,f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
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

fof(f61,plain,(
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
    inference(rectify,[],[f60])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f484,plain,(
    ! [X31,X32] :
      ( m1_subset_1(k4_lattices(sK0,X31,k15_lattice3(sK0,X32)),u1_struct_0(sK0))
      | ~ m1_subset_1(X31,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f483,f76])).

fof(f483,plain,(
    ! [X31,X32] :
      ( m1_subset_1(k4_lattices(sK0,X31,k15_lattice3(sK0,X32)),u1_struct_0(sK0))
      | ~ m1_subset_1(X31,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f482,f206])).

fof(f482,plain,(
    ! [X31,X32] :
      ( m1_subset_1(k4_lattices(sK0,X31,k15_lattice3(sK0,X32)),u1_struct_0(sK0))
      | ~ m1_subset_1(X31,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f421,f187])).

fof(f421,plain,(
    ! [X31,X32] :
      ( m1_subset_1(k4_lattices(sK0,X31,k15_lattice3(sK0,X32)),u1_struct_0(sK0))
      | ~ m1_subset_1(X31,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f214,f113])).

fof(f47164,plain,(
    ! [X437] :
      ( ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,X437)),u1_struct_0(sK0))
      | ~ sP7(X437) ) ),
    inference(subsumption_resolution,[],[f47010,f214])).

fof(f47010,plain,(
    ! [X437] :
      ( ~ m1_subset_1(k15_lattice3(sK0,X437),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,X437)),u1_struct_0(sK0))
      | ~ sP7(X437) ) ),
    inference(trivial_inequality_removal,[],[f46937])).

fof(f46937,plain,(
    ! [X437] :
      ( k15_lattice3(sK0,X437) != k15_lattice3(sK0,X437)
      | ~ m1_subset_1(k15_lattice3(sK0,X437),u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,X437)),u1_struct_0(sK0))
      | ~ sP7(X437) ) ),
    inference(superposition,[],[f16470,f36984])).

fof(f36984,plain,(
    ! [X0,X1] :
      ( k15_lattice3(sK0,X0) = k4_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ sP7(X0) ) ),
    inference(duplicate_literal_removal,[],[f36905])).

fof(f36905,plain,(
    ! [X0,X1] :
      ( ~ sP7(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k15_lattice3(sK0,X0) = k4_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f12156,f3654])).

fof(f3654,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,k15_lattice3(sK0,X1),k4_lattices(sK0,k15_lattice3(sK0,X1),X0))
      | k15_lattice3(sK0,X1) = k4_lattices(sK0,k15_lattice3(sK0,X1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3653,f481])).

fof(f481,plain,(
    ! [X30,X29] :
      ( m1_subset_1(k4_lattices(sK0,k15_lattice3(sK0,X29),X30),u1_struct_0(sK0))
      | ~ m1_subset_1(X30,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f480,f76])).

fof(f480,plain,(
    ! [X30,X29] :
      ( m1_subset_1(k4_lattices(sK0,k15_lattice3(sK0,X29),X30),u1_struct_0(sK0))
      | ~ m1_subset_1(X30,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f479,f206])).

fof(f479,plain,(
    ! [X30,X29] :
      ( m1_subset_1(k4_lattices(sK0,k15_lattice3(sK0,X29),X30),u1_struct_0(sK0))
      | ~ m1_subset_1(X30,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f420,f187])).

fof(f420,plain,(
    ! [X30,X29] :
      ( m1_subset_1(k4_lattices(sK0,k15_lattice3(sK0,X29),X30),u1_struct_0(sK0))
      | ~ m1_subset_1(X30,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f214,f113])).

fof(f3653,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k15_lattice3(sK0,X1) = k4_lattices(sK0,k15_lattice3(sK0,X1),X0)
      | ~ r1_lattices(sK0,k15_lattice3(sK0,X1),k4_lattices(sK0,k15_lattice3(sK0,X1),X0))
      | ~ m1_subset_1(k4_lattices(sK0,k15_lattice3(sK0,X1),X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3637,f214])).

fof(f3637,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k15_lattice3(sK0,X1) = k4_lattices(sK0,k15_lattice3(sK0,X1),X0)
      | ~ r1_lattices(sK0,k15_lattice3(sK0,X1),k4_lattices(sK0,k15_lattice3(sK0,X1),X0))
      | ~ m1_subset_1(k4_lattices(sK0,k15_lattice3(sK0,X1),X0),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f452,f2018])).

fof(f452,plain,(
    ! [X8,X7] :
      ( r1_lattices(sK0,k4_lattices(sK0,k15_lattice3(sK0,X7),X8),k15_lattice3(sK0,X7))
      | ~ m1_subset_1(X8,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f451,f76])).

fof(f451,plain,(
    ! [X8,X7] :
      ( r1_lattices(sK0,k4_lattices(sK0,k15_lattice3(sK0,X7),X8),k15_lattice3(sK0,X7))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f450,f206])).

fof(f450,plain,(
    ! [X8,X7] :
      ( r1_lattices(sK0,k4_lattices(sK0,k15_lattice3(sK0,X7),X8),k15_lattice3(sK0,X7))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f449,f208])).

fof(f449,plain,(
    ! [X8,X7] :
      ( r1_lattices(sK0,k4_lattices(sK0,k15_lattice3(sK0,X7),X8),k15_lattice3(sK0,X7))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f407,f79])).

fof(f407,plain,(
    ! [X8,X7] :
      ( r1_lattices(sK0,k4_lattices(sK0,k15_lattice3(sK0,X7),X8),k15_lattice3(sK0,X7))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f214,f90])).

fof(f12156,plain,(
    ! [X14,X12,X13] :
      ( r1_lattices(sK0,k15_lattice3(sK0,X13),k4_lattices(sK0,k15_lattice3(sK0,X14),X12))
      | ~ sP7(X13)
      | ~ m1_subset_1(X12,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f12155,f481])).

fof(f12155,plain,(
    ! [X14,X12,X13] :
      ( ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ sP7(X13)
      | r1_lattices(sK0,k15_lattice3(sK0,X13),k4_lattices(sK0,k15_lattice3(sK0,X14),X12))
      | ~ m1_subset_1(k4_lattices(sK0,k15_lattice3(sK0,X14),X12),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f12154,f76])).

fof(f12154,plain,(
    ! [X14,X12,X13] :
      ( ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ sP7(X13)
      | r1_lattices(sK0,k15_lattice3(sK0,X13),k4_lattices(sK0,k15_lattice3(sK0,X14),X12))
      | ~ m1_subset_1(k4_lattices(sK0,k15_lattice3(sK0,X14),X12),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f12153,f77])).

fof(f12153,plain,(
    ! [X14,X12,X13] :
      ( ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ sP7(X13)
      | r1_lattices(sK0,k15_lattice3(sK0,X13),k4_lattices(sK0,k15_lattice3(sK0,X14),X12))
      | ~ m1_subset_1(k4_lattices(sK0,k15_lattice3(sK0,X14),X12),u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f12152,f78])).

fof(f12152,plain,(
    ! [X14,X12,X13] :
      ( ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ sP7(X13)
      | r1_lattices(sK0,k15_lattice3(sK0,X13),k4_lattices(sK0,k15_lattice3(sK0,X14),X12))
      | ~ m1_subset_1(k4_lattices(sK0,k15_lattice3(sK0,X14),X12),u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f12151,f79])).

fof(f12151,plain,(
    ! [X14,X12,X13] :
      ( ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ sP7(X13)
      | r1_lattices(sK0,k15_lattice3(sK0,X13),k4_lattices(sK0,k15_lattice3(sK0,X14),X12))
      | ~ m1_subset_1(k4_lattices(sK0,k15_lattice3(sK0,X14),X12),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f12124,f214])).

fof(f12124,plain,(
    ! [X14,X12,X13] :
      ( ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ sP7(X13)
      | r1_lattices(sK0,k15_lattice3(sK0,X13),k4_lattices(sK0,k15_lattice3(sK0,X14),X12))
      | ~ m1_subset_1(k4_lattices(sK0,k15_lattice3(sK0,X14),X12),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,X13),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2464,f126])).

fof(f2464,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(sK0,k4_lattices(sK0,k15_lattice3(sK0,X1),X0),X2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ sP7(X2) ) ),
    inference(resolution,[],[f481,f773])).

fof(f16470,plain,(
    ! [X0] :
      ( k4_lattices(sK0,X0,sK2(sK0,X0)) != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f16443])).

fof(f16443,plain,(
    ! [X0] :
      ( k4_lattices(sK0,X0,sK2(sK0,X0)) != X0
      | k4_lattices(sK0,X0,sK2(sK0,X0)) != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f7122,f7146])).

fof(f7146,plain,(
    ! [X35,X34] :
      ( k4_lattices(sK0,sK2(sK0,X34),X35) = k4_lattices(sK0,X35,sK2(sK0,X34))
      | ~ m1_subset_1(X34,u1_struct_0(sK0))
      | ~ m1_subset_1(X35,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f731,f6188])).

fof(f731,plain,(
    ! [X35,X34] :
      ( v13_lattices(sK0)
      | ~ m1_subset_1(X34,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2(sK0,X34),X35) = k4_lattices(sK0,X35,sK2(sK0,X34))
      | ~ m1_subset_1(X35,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f730,f76])).

fof(f730,plain,(
    ! [X35,X34] :
      ( v13_lattices(sK0)
      | ~ m1_subset_1(X34,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2(sK0,X34),X35) = k4_lattices(sK0,X35,sK2(sK0,X34))
      | ~ m1_subset_1(X35,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f729,f206])).

fof(f729,plain,(
    ! [X35,X34] :
      ( v13_lattices(sK0)
      | ~ m1_subset_1(X34,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2(sK0,X34),X35) = k4_lattices(sK0,X35,sK2(sK0,X34))
      | ~ m1_subset_1(X35,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f679,f187])).

fof(f679,plain,(
    ! [X35,X34] :
      ( v13_lattices(sK0)
      | ~ m1_subset_1(X34,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2(sK0,X34),X35) = k4_lattices(sK0,X35,sK2(sK0,X34))
      | ~ m1_subset_1(X35,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f659,f115])).

fof(f659,plain,(
    ! [X8] :
      ( m1_subset_1(sK2(sK0,X8),u1_struct_0(sK0))
      | v13_lattices(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f139,f187])).

fof(f139,plain,(
    ! [X8] :
      ( v13_lattices(sK0)
      | m1_subset_1(sK2(sK0,X8),u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ l1_lattices(sK0) ) ),
    inference(resolution,[],[f76,f99])).

fof(f7122,plain,(
    ! [X0] :
      ( k4_lattices(sK0,sK2(sK0,X0),X0) != X0
      | k4_lattices(sK0,X0,sK2(sK0,X0)) != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f7109])).

fof(f7109,plain,(
    ! [X0] :
      ( k4_lattices(sK0,sK2(sK0,X0),X0) != X0
      | k4_lattices(sK0,X0,sK2(sK0,X0)) != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f6877,f7104])).

fof(f7104,plain,(
    ! [X30,X31] :
      ( k4_lattices(sK0,sK2(sK0,X30),X31) = k2_lattices(sK0,sK2(sK0,X30),X31)
      | ~ m1_subset_1(X30,u1_struct_0(sK0))
      | ~ m1_subset_1(X31,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f725,f6188])).

fof(f725,plain,(
    ! [X30,X31] :
      ( v13_lattices(sK0)
      | ~ m1_subset_1(X30,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2(sK0,X30),X31) = k2_lattices(sK0,sK2(sK0,X30),X31)
      | ~ m1_subset_1(X31,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f724,f76])).

fof(f724,plain,(
    ! [X30,X31] :
      ( v13_lattices(sK0)
      | ~ m1_subset_1(X30,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2(sK0,X30),X31) = k2_lattices(sK0,sK2(sK0,X30),X31)
      | ~ m1_subset_1(X31,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f723,f206])).

fof(f723,plain,(
    ! [X30,X31] :
      ( v13_lattices(sK0)
      | ~ m1_subset_1(X30,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2(sK0,X30),X31) = k2_lattices(sK0,sK2(sK0,X30),X31)
      | ~ m1_subset_1(X31,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f677,f187])).

fof(f677,plain,(
    ! [X30,X31] :
      ( v13_lattices(sK0)
      | ~ m1_subset_1(X30,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2(sK0,X30),X31) = k2_lattices(sK0,sK2(sK0,X30),X31)
      | ~ m1_subset_1(X31,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f659,f114])).

fof(f6877,plain,(
    ! [X6] :
      ( k2_lattices(sK0,sK2(sK0,X6),X6) != X6
      | k4_lattices(sK0,X6,sK2(sK0,X6)) != X6
      | ~ m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1766,f6188])).

fof(f1766,plain,(
    ! [X6] :
      ( k4_lattices(sK0,X6,sK2(sK0,X6)) != X6
      | v13_lattices(sK0)
      | k2_lattices(sK0,sK2(sK0,X6),X6) != X6
      | ~ m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1765,f659])).

fof(f1765,plain,(
    ! [X6] :
      ( k4_lattices(sK0,X6,sK2(sK0,X6)) != X6
      | v13_lattices(sK0)
      | k2_lattices(sK0,sK2(sK0,X6),X6) != X6
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(sK0,X6),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1764,f76])).

fof(f1764,plain,(
    ! [X6] :
      ( k4_lattices(sK0,X6,sK2(sK0,X6)) != X6
      | v13_lattices(sK0)
      | k2_lattices(sK0,sK2(sK0,X6),X6) != X6
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2(sK0,X6),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1731,f187])).

fof(f1731,plain,(
    ! [X6] :
      ( k4_lattices(sK0,X6,sK2(sK0,X6)) != X6
      | v13_lattices(sK0)
      | k2_lattices(sK0,sK2(sK0,X6),X6) != X6
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2(sK0,X6),u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f1720])).

fof(f1720,plain,(
    ! [X6] :
      ( k4_lattices(sK0,X6,sK2(sK0,X6)) != X6
      | v13_lattices(sK0)
      | k2_lattices(sK0,sK2(sK0,X6),X6) != X6
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2(sK0,X6),u1_struct_0(sK0))
      | ~ m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f100,f1709])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | k2_lattices(X0,sK2(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

%------------------------------------------------------------------------------
