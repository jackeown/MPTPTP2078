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
% DateTime   : Thu Dec  3 13:15:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  163 (2578 expanded)
%              Number of leaves         :   19 ( 623 expanded)
%              Depth                    :   50
%              Number of atoms          :  799 (19515 expanded)
%              Number of equality atoms :  137 (2133 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (30672)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f1363,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1352,f991])).

fof(f991,plain,(
    ! [X0] : m1_subset_1(sK2(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f952,f373])).

fof(f373,plain,(
    ! [X14] :
      ( v13_lattices(sK0)
      | m1_subset_1(sK2(sK0,k15_lattice3(sK0,X14)),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f372,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f38])).

fof(f38,plain,
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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f372,plain,(
    ! [X14] :
      ( v13_lattices(sK0)
      | m1_subset_1(sK2(sK0,k15_lattice3(sK0,X14)),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f329,f181])).

fof(f181,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f59,f62])).

fof(f62,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f59,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f329,plain,(
    ! [X14] :
      ( v13_lattices(sK0)
      | m1_subset_1(sK2(sK0,k15_lattice3(sK0,X14)),u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f156,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f46,f48,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).

fof(f156,plain,(
    ! [X18] : m1_subset_1(k15_lattice3(sK0,X18),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f120,f59])).

fof(f120,plain,(
    ! [X18] :
      ( m1_subset_1(k15_lattice3(sK0,X18),u1_struct_0(sK0))
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f56,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f952,plain,(
    ~ v13_lattices(sK0) ),
    inference(subsumption_resolution,[],[f951,f200])).

fof(f200,plain,
    ( ~ v13_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f199,f56])).

fof(f199,plain,
    ( ~ v13_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f198,f59])).

fof(f198,plain,
    ( ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f60,f57])).

fof(f57,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f951,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0) ),
    inference(subsumption_resolution,[],[f950,f56])).

fof(f950,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f949,f181])).

fof(f949,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f948,f226])).

fof(f226,plain,(
    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f212,f56])).

fof(f212,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f181,f77])).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f948,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f940,f156])).

fof(f940,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f535,f94])).

fof(f94,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f535,plain,(
    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f534,f56])).

fof(f534,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f533,f134])).

fof(f134,plain,(
    v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f133,f59])).

fof(f133,plain,
    ( v8_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f100,f57])).

fof(f100,plain,
    ( v8_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f56,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f2])).

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

fof(f533,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f532,f136])).

fof(f136,plain,(
    v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f135,f59])).

fof(f135,plain,
    ( v9_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f101,f57])).

fof(f101,plain,
    ( v9_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f56,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f532,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f531,f59])).

fof(f531,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f530,f156])).

fof(f530,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f527,f226])).

fof(f527,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f507,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

fof(f507,plain,(
    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f506,f56])).

fof(f506,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f505,f130])).

fof(f130,plain,(
    v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f129,f59])).

fof(f129,plain,
    ( v6_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f98,f57])).

fof(f98,plain,
    ( v6_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f56,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f505,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f504,f134])).

fof(f504,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f503,f136])).

fof(f503,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f502,f59])).

fof(f502,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f501,f156])).

fof(f501,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f498,f226])).

fof(f498,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f465,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f465,plain,(
    r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    inference(superposition,[],[f459,f283])).

fof(f283,plain,(
    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) ),
    inference(subsumption_resolution,[],[f282,f56])).

fof(f282,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f281,f57])).

fof(f281,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f280,f58])).

fof(f58,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f280,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f246,f59])).

fof(f246,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f226,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f459,plain,(
    ! [X0] : r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) ),
    inference(resolution,[],[f151,f61])).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f151,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | r3_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7)) ) ),
    inference(subsumption_resolution,[],[f150,f57])).

fof(f150,plain,(
    ! [X6,X7] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7))
      | ~ r1_tarski(X6,X7)
      | ~ v10_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f149,f58])).

fof(f149,plain,(
    ! [X6,X7] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7))
      | ~ r1_tarski(X6,X7)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f106,f59])).

fof(f106,plain,(
    ! [X6,X7] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7))
      | ~ r1_tarski(X6,X7)
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0) ) ),
    inference(resolution,[],[f56,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f1352,plain,(
    ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f1214,f589])).

fof(f589,plain,(
    ! [X0] :
      ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f473,f145])).

fof(f145,plain,(
    ! [X4] :
      ( k15_lattice3(sK0,a_2_3_lattice3(sK0,X4)) = X4
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f144,f57])).

fof(f144,plain,(
    ! [X4] :
      ( k15_lattice3(sK0,a_2_3_lattice3(sK0,X4)) = X4
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ v10_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f143,f58])).

fof(f143,plain,(
    ! [X4] :
      ( k15_lattice3(sK0,a_2_3_lattice3(sK0,X4)) = X4
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f104,f59])).

fof(f104,plain,(
    ! [X4] :
      ( k15_lattice3(sK0,a_2_3_lattice3(sK0,X4)) = X4
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0) ) ),
    inference(resolution,[],[f56,f73])).

fof(f473,plain,(
    ! [X0] : r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) ),
    inference(subsumption_resolution,[],[f472,f56])).

fof(f472,plain,(
    ! [X0] :
      ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f471,f130])).

fof(f471,plain,(
    ! [X0] :
      ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f470,f134])).

fof(f470,plain,(
    ! [X0] :
      ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f469,f136])).

fof(f469,plain,(
    ! [X0] :
      ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f468,f59])).

fof(f468,plain,(
    ! [X0] :
      ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f467,f156])).

fof(f467,plain,(
    ! [X0] :
      ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
      | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f463,f156])).

fof(f463,plain,(
    ! [X0] :
      ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
      | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f459,f92])).

fof(f1214,plain,(
    ! [X2] : ~ r1_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0,k15_lattice3(sK0,X2))) ),
    inference(subsumption_resolution,[],[f1213,f56])).

fof(f1213,plain,(
    ! [X2] :
      ( ~ r1_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0,k15_lattice3(sK0,X2)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1212,f134])).

fof(f1212,plain,(
    ! [X2] :
      ( ~ r1_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0,k15_lattice3(sK0,X2)))
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1211,f136])).

fof(f1211,plain,(
    ! [X2] :
      ( ~ r1_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0,k15_lattice3(sK0,X2)))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1210,f59])).

fof(f1210,plain,(
    ! [X2] :
      ( ~ r1_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0,k15_lattice3(sK0,X2)))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1209,f156])).

fof(f1209,plain,(
    ! [X2] :
      ( ~ r1_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0,k15_lattice3(sK0,X2)))
      | ~ m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1208,f991])).

fof(f1208,plain,(
    ! [X2] :
      ( ~ r1_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0,k15_lattice3(sK0,X2)))
      | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,X2)),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(trivial_inequality_removal,[],[f1207])).

fof(f1207,plain,(
    ! [X2] :
      ( k15_lattice3(sK0,X2) != k15_lattice3(sK0,X2)
      | ~ r1_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0,k15_lattice3(sK0,X2)))
      | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,X2)),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f1158,f71])).

fof(f1158,plain,(
    ! [X15] : k15_lattice3(sK0,X15) != k2_lattices(sK0,k15_lattice3(sK0,X15),sK2(sK0,k15_lattice3(sK0,X15))) ),
    inference(subsumption_resolution,[],[f1157,f952])).

fof(f1157,plain,(
    ! [X15] :
      ( k15_lattice3(sK0,X15) != k2_lattices(sK0,k15_lattice3(sK0,X15),sK2(sK0,k15_lattice3(sK0,X15)))
      | v13_lattices(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1156])).

fof(f1156,plain,(
    ! [X15] :
      ( k15_lattice3(sK0,X15) != k2_lattices(sK0,k15_lattice3(sK0,X15),sK2(sK0,k15_lattice3(sK0,X15)))
      | v13_lattices(sK0)
      | k15_lattice3(sK0,X15) != k2_lattices(sK0,k15_lattice3(sK0,X15),sK2(sK0,k15_lattice3(sK0,X15))) ) ),
    inference(backward_demodulation,[],[f375,f1123])).

fof(f1123,plain,(
    ! [X8,X9] : k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X8)),k15_lattice3(sK0,X9)) = k2_lattices(sK0,k15_lattice3(sK0,X9),sK2(sK0,k15_lattice3(sK0,X8))) ),
    inference(resolution,[],[f991,f378])).

fof(f378,plain,(
    ! [X17,X16] :
      ( ~ m1_subset_1(X16,u1_struct_0(sK0))
      | k2_lattices(sK0,X16,k15_lattice3(sK0,X17)) = k2_lattices(sK0,k15_lattice3(sK0,X17),X16) ) ),
    inference(subsumption_resolution,[],[f377,f56])).

fof(f377,plain,(
    ! [X17,X16] :
      ( k2_lattices(sK0,X16,k15_lattice3(sK0,X17)) = k2_lattices(sK0,k15_lattice3(sK0,X17),X16)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f376,f181])).

fof(f376,plain,(
    ! [X17,X16] :
      ( k2_lattices(sK0,X16,k15_lattice3(sK0,X17)) = k2_lattices(sK0,k15_lattice3(sK0,X17),X16)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f331,f130])).

fof(f331,plain,(
    ! [X17,X16] :
      ( k2_lattices(sK0,X16,k15_lattice3(sK0,X17)) = k2_lattices(sK0,k15_lattice3(sK0,X17),X16)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f156,f87])).

fof(f87,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f51,f53,f52])).

fof(f52,plain,(
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

fof(f53,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f375,plain,(
    ! [X15] :
      ( v13_lattices(sK0)
      | k15_lattice3(sK0,X15) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X15)),k15_lattice3(sK0,X15))
      | k15_lattice3(sK0,X15) != k2_lattices(sK0,k15_lattice3(sK0,X15),sK2(sK0,k15_lattice3(sK0,X15))) ) ),
    inference(subsumption_resolution,[],[f374,f56])).

fof(f374,plain,(
    ! [X15] :
      ( v13_lattices(sK0)
      | k15_lattice3(sK0,X15) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X15)),k15_lattice3(sK0,X15))
      | k15_lattice3(sK0,X15) != k2_lattices(sK0,k15_lattice3(sK0,X15),sK2(sK0,k15_lattice3(sK0,X15)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f330,f181])).

fof(f330,plain,(
    ! [X15] :
      ( v13_lattices(sK0)
      | k15_lattice3(sK0,X15) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X15)),k15_lattice3(sK0,X15))
      | k15_lattice3(sK0,X15) != k2_lattices(sK0,k15_lattice3(sK0,X15),sK2(sK0,k15_lattice3(sK0,X15)))
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f156,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | k2_lattices(X0,sK2(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:53:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.44  % (30677)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.45  % (30668)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.46  % (30675)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.47  % (30684)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (30669)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (30665)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (30665)Refutation not found, incomplete strategy% (30665)------------------------------
% 0.21/0.49  % (30665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (30665)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (30665)Memory used [KB]: 10618
% 0.21/0.49  % (30665)Time elapsed: 0.080 s
% 0.21/0.49  % (30665)------------------------------
% 0.21/0.49  % (30665)------------------------------
% 0.21/0.49  % (30681)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (30676)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (30684)Refutation not found, incomplete strategy% (30684)------------------------------
% 0.21/0.49  % (30684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (30684)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (30684)Memory used [KB]: 10618
% 0.21/0.49  % (30684)Time elapsed: 0.092 s
% 0.21/0.49  % (30684)------------------------------
% 0.21/0.49  % (30684)------------------------------
% 0.21/0.49  % (30666)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (30679)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (30667)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (30673)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (30664)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (30670)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (30664)Refutation not found, incomplete strategy% (30664)------------------------------
% 0.21/0.50  % (30664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30664)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (30664)Memory used [KB]: 6140
% 0.21/0.50  % (30664)Time elapsed: 0.089 s
% 0.21/0.50  % (30664)------------------------------
% 0.21/0.50  % (30664)------------------------------
% 0.21/0.50  % (30668)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  % (30672)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  fof(f1363,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f1352,f991])).
% 0.21/0.50  fof(f991,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(sK2(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))) )),
% 0.21/0.50    inference(resolution,[],[f952,f373])).
% 0.21/0.50  fof(f373,plain,(
% 0.21/0.50    ( ! [X14] : (v13_lattices(sK0) | m1_subset_1(sK2(sK0,k15_lattice3(sK0,X14)),u1_struct_0(sK0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f372,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(negated_conjecture,[],[f13])).
% 0.21/0.50  fof(f13,conjecture,(
% 0.21/0.50    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).
% 0.21/0.50  fof(f372,plain,(
% 0.21/0.50    ( ! [X14] : (v13_lattices(sK0) | m1_subset_1(sK2(sK0,k15_lattice3(sK0,X14)),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f329,f181])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    l1_lattices(sK0)),
% 0.21/0.50    inference(resolution,[],[f59,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    l3_lattices(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f329,plain,(
% 0.21/0.50    ( ! [X14] : (v13_lattices(sK0) | m1_subset_1(sK2(sK0,k15_lattice3(sK0,X14)),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f156,f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v13_lattices(X0) | m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f46,f48,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(rectify,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    ( ! [X18] : (m1_subset_1(k15_lattice3(sK0,X18),u1_struct_0(sK0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f120,f59])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    ( ! [X18] : (m1_subset_1(k15_lattice3(sK0,X18),u1_struct_0(sK0)) | ~l3_lattices(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f56,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 0.21/0.50  fof(f952,plain,(
% 0.21/0.50    ~v13_lattices(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f951,f200])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    ~v13_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f199,f56])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    ~v13_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f198,f59])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    ~l3_lattices(sK0) | ~v13_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f60,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    v10_lattices(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ~v10_lattices(sK0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f951,plain,(
% 0.21/0.50    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f950,f56])).
% 0.21/0.50  fof(f950,plain,(
% 0.21/0.50    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f949,f181])).
% 0.21/0.50  fof(f949,plain,(
% 0.21/0.50    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f948,f226])).
% 0.21/0.50  fof(f226,plain,(
% 0.21/0.50    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f212,f56])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f181,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).
% 0.21/0.50  fof(f948,plain,(
% 0.21/0.50    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f940,f156])).
% 0.21/0.50  fof(f940,plain,(
% 0.21/0.50    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(superposition,[],[f535,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (k2_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(rectify,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).
% 0.21/0.50  fof(f535,plain,(
% 0.21/0.50    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f534,f56])).
% 0.21/0.50  fof(f534,plain,(
% 0.21/0.50    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f533,f134])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    v8_lattices(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f133,f59])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    v8_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f100,f57])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    v8_lattices(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.50    inference(resolution,[],[f56,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.50  fof(f533,plain,(
% 0.21/0.50    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~v8_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f532,f136])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    v9_lattices(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f135,f59])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    v9_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f101,f57])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    v9_lattices(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.50    inference(resolution,[],[f56,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f532,plain,(
% 0.21/0.50    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f531,f59])).
% 0.21/0.50  fof(f531,plain,(
% 0.21/0.50    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f530,f156])).
% 0.21/0.50  fof(f530,plain,(
% 0.21/0.50    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f527,f226])).
% 0.21/0.50  fof(f527,plain,(
% 0.21/0.50    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f507,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 0.21/0.50  fof(f507,plain,(
% 0.21/0.50    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f506,f56])).
% 0.21/0.50  fof(f506,plain,(
% 0.21/0.50    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f505,f130])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    v6_lattices(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f129,f59])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    v6_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f98,f57])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    v6_lattices(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.50    inference(resolution,[],[f56,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f505,plain,(
% 0.21/0.50    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f504,f134])).
% 0.21/0.50  fof(f504,plain,(
% 0.21/0.50    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f503,f136])).
% 0.21/0.50  fof(f503,plain,(
% 0.21/0.50    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f502,f59])).
% 0.21/0.50  fof(f502,plain,(
% 0.21/0.50    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f501,f156])).
% 0.21/0.50  fof(f501,plain,(
% 0.21/0.50    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f498,f226])).
% 0.21/0.50  fof(f498,plain,(
% 0.21/0.50    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f465,f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.21/0.50  fof(f465,plain,(
% 0.21/0.50    r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 0.21/0.50    inference(superposition,[],[f459,f283])).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f282,f56])).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f281,f57])).
% 0.21/0.50  fof(f281,plain,(
% 0.21/0.50    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f280,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    v4_lattice3(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f280,plain,(
% 0.21/0.50    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f246,f59])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f226,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).
% 0.21/0.50  fof(f459,plain,(
% 0.21/0.50    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) )),
% 0.21/0.50    inference(resolution,[],[f151,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ( ! [X6,X7] : (~r1_tarski(X6,X7) | r3_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f150,f57])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ( ! [X6,X7] : (r3_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7)) | ~r1_tarski(X6,X7) | ~v10_lattices(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f149,f58])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    ( ! [X6,X7] : (r3_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7)) | ~r1_tarski(X6,X7) | ~v4_lattice3(sK0) | ~v10_lattices(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f106,f59])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ( ! [X6,X7] : (r3_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7)) | ~r1_tarski(X6,X7) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f56,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ~r1_tarski(X1,X2) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) | ~r1_tarski(X1,X2)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) | ~r1_tarski(X1,X2)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_lattice3)).
% 0.21/0.50  fof(f1352,plain,(
% 0.21/0.50    ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))),
% 0.21/0.50    inference(resolution,[],[f1214,f589])).
% 0.21/0.50  fof(f589,plain,(
% 0.21/0.50    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.21/0.50    inference(superposition,[],[f473,f145])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    ( ! [X4] : (k15_lattice3(sK0,a_2_3_lattice3(sK0,X4)) = X4 | ~m1_subset_1(X4,u1_struct_0(sK0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f144,f57])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    ( ! [X4] : (k15_lattice3(sK0,a_2_3_lattice3(sK0,X4)) = X4 | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~v10_lattices(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f143,f58])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ( ! [X4] : (k15_lattice3(sK0,a_2_3_lattice3(sK0,X4)) = X4 | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f104,f59])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ( ! [X4] : (k15_lattice3(sK0,a_2_3_lattice3(sK0,X4)) = X4 | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f56,f73])).
% 0.21/0.50  fof(f473,plain,(
% 0.21/0.50    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f472,f56])).
% 0.21/0.50  fof(f472,plain,(
% 0.21/0.50    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f471,f130])).
% 0.21/0.50  fof(f471,plain,(
% 0.21/0.50    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f470,f134])).
% 0.21/0.50  fof(f470,plain,(
% 0.21/0.50    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f469,f136])).
% 0.21/0.50  fof(f469,plain,(
% 0.21/0.50    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f468,f59])).
% 0.21/0.50  fof(f468,plain,(
% 0.21/0.50    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f467,f156])).
% 0.21/0.50  fof(f467,plain,(
% 0.21/0.50    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f463,f156])).
% 0.21/0.50  fof(f463,plain,(
% 0.21/0.50    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f459,f92])).
% 0.21/0.50  fof(f1214,plain,(
% 0.21/0.50    ( ! [X2] : (~r1_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0,k15_lattice3(sK0,X2)))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f1213,f56])).
% 0.21/0.50  fof(f1213,plain,(
% 0.21/0.50    ( ! [X2] : (~r1_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0,k15_lattice3(sK0,X2))) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f1212,f134])).
% 0.21/0.50  fof(f1212,plain,(
% 0.21/0.50    ( ! [X2] : (~r1_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0,k15_lattice3(sK0,X2))) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f1211,f136])).
% 0.21/0.50  fof(f1211,plain,(
% 0.21/0.50    ( ! [X2] : (~r1_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0,k15_lattice3(sK0,X2))) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f1210,f59])).
% 0.21/0.50  fof(f1210,plain,(
% 0.21/0.50    ( ! [X2] : (~r1_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0,k15_lattice3(sK0,X2))) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f1209,f156])).
% 0.21/0.50  fof(f1209,plain,(
% 0.21/0.50    ( ! [X2] : (~r1_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0,k15_lattice3(sK0,X2))) | ~m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f1208,f991])).
% 0.21/0.50  fof(f1208,plain,(
% 0.21/0.50    ( ! [X2] : (~r1_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0,k15_lattice3(sK0,X2))) | ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,X2)),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f1207])).
% 0.21/0.50  fof(f1207,plain,(
% 0.21/0.50    ( ! [X2] : (k15_lattice3(sK0,X2) != k15_lattice3(sK0,X2) | ~r1_lattices(sK0,k15_lattice3(sK0,X2),sK2(sK0,k15_lattice3(sK0,X2))) | ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,X2)),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(superposition,[],[f1158,f71])).
% 0.21/0.50  fof(f1158,plain,(
% 0.21/0.50    ( ! [X15] : (k15_lattice3(sK0,X15) != k2_lattices(sK0,k15_lattice3(sK0,X15),sK2(sK0,k15_lattice3(sK0,X15)))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f1157,f952])).
% 0.21/0.50  fof(f1157,plain,(
% 0.21/0.50    ( ! [X15] : (k15_lattice3(sK0,X15) != k2_lattices(sK0,k15_lattice3(sK0,X15),sK2(sK0,k15_lattice3(sK0,X15))) | v13_lattices(sK0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f1156])).
% 0.21/0.50  fof(f1156,plain,(
% 0.21/0.50    ( ! [X15] : (k15_lattice3(sK0,X15) != k2_lattices(sK0,k15_lattice3(sK0,X15),sK2(sK0,k15_lattice3(sK0,X15))) | v13_lattices(sK0) | k15_lattice3(sK0,X15) != k2_lattices(sK0,k15_lattice3(sK0,X15),sK2(sK0,k15_lattice3(sK0,X15)))) )),
% 0.21/0.50    inference(backward_demodulation,[],[f375,f1123])).
% 0.21/0.50  fof(f1123,plain,(
% 0.21/0.50    ( ! [X8,X9] : (k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X8)),k15_lattice3(sK0,X9)) = k2_lattices(sK0,k15_lattice3(sK0,X9),sK2(sK0,k15_lattice3(sK0,X8)))) )),
% 0.21/0.50    inference(resolution,[],[f991,f378])).
% 0.21/0.50  fof(f378,plain,(
% 0.21/0.50    ( ! [X17,X16] : (~m1_subset_1(X16,u1_struct_0(sK0)) | k2_lattices(sK0,X16,k15_lattice3(sK0,X17)) = k2_lattices(sK0,k15_lattice3(sK0,X17),X16)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f377,f56])).
% 0.21/0.50  fof(f377,plain,(
% 0.21/0.50    ( ! [X17,X16] : (k2_lattices(sK0,X16,k15_lattice3(sK0,X17)) = k2_lattices(sK0,k15_lattice3(sK0,X17),X16) | ~m1_subset_1(X16,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f376,f181])).
% 0.21/0.50  fof(f376,plain,(
% 0.21/0.50    ( ! [X17,X16] : (k2_lattices(sK0,X16,k15_lattice3(sK0,X17)) = k2_lattices(sK0,k15_lattice3(sK0,X17),X16) | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f331,f130])).
% 0.21/0.50  fof(f331,plain,(
% 0.21/0.50    ( ! [X17,X16] : (k2_lattices(sK0,X16,k15_lattice3(sK0,X17)) = k2_lattices(sK0,k15_lattice3(sK0,X17),X16) | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f156,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X4,X0,X3] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f51,f53,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ! [X0] : (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(rectify,[],[f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).
% 0.21/0.50  fof(f375,plain,(
% 0.21/0.50    ( ! [X15] : (v13_lattices(sK0) | k15_lattice3(sK0,X15) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X15)),k15_lattice3(sK0,X15)) | k15_lattice3(sK0,X15) != k2_lattices(sK0,k15_lattice3(sK0,X15),sK2(sK0,k15_lattice3(sK0,X15)))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f374,f56])).
% 0.21/0.50  fof(f374,plain,(
% 0.21/0.50    ( ! [X15] : (v13_lattices(sK0) | k15_lattice3(sK0,X15) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X15)),k15_lattice3(sK0,X15)) | k15_lattice3(sK0,X15) != k2_lattices(sK0,k15_lattice3(sK0,X15),sK2(sK0,k15_lattice3(sK0,X15))) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f330,f181])).
% 0.21/0.50  fof(f330,plain,(
% 0.21/0.50    ( ! [X15] : (v13_lattices(sK0) | k15_lattice3(sK0,X15) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X15)),k15_lattice3(sK0,X15)) | k15_lattice3(sK0,X15) != k2_lattices(sK0,k15_lattice3(sK0,X15),sK2(sK0,k15_lattice3(sK0,X15))) | ~l1_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f156,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v13_lattices(X0) | k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f49])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (30668)------------------------------
% 0.21/0.50  % (30668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30668)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (30668)Memory used [KB]: 2174
% 0.21/0.50  % (30668)Time elapsed: 0.087 s
% 0.21/0.50  % (30668)------------------------------
% 0.21/0.50  % (30668)------------------------------
% 0.21/0.50  % (30663)Success in time 0.154 s
%------------------------------------------------------------------------------
