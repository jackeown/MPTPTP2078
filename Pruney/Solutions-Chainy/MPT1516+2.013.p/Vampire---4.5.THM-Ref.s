%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:50 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 762 expanded)
%              Number of leaves         :   31 ( 192 expanded)
%              Depth                    :   35
%              Number of atoms          : 1208 (5781 expanded)
%              Number of equality atoms :  141 ( 650 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1009,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f145,f149,f965,f967,f983,f997,f1006,f1008])).

fof(f1008,plain,(
    ~ spl11_1 ),
    inference(avatar_contradiction_clause,[],[f1007])).

fof(f1007,plain,
    ( $false
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f132,f74])).

fof(f74,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f40])).

fof(f40,plain,
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f132,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f131])).

% (19194)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f131,plain,
    ( spl11_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f1006,plain,(
    spl11_6 ),
    inference(avatar_contradiction_clause,[],[f1005])).

fof(f1005,plain,
    ( $false
    | spl11_6 ),
    inference(subsumption_resolution,[],[f1004,f74])).

fof(f1004,plain,
    ( v2_struct_0(sK0)
    | spl11_6 ),
    inference(subsumption_resolution,[],[f999,f150])).

fof(f150,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f79,f77])).

fof(f77,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f79,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f999,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl11_6 ),
    inference(resolution,[],[f979,f86])).

fof(f86,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f979,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl11_6 ),
    inference(avatar_component_clause,[],[f978])).

fof(f978,plain,
    ( spl11_6
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f997,plain,(
    spl11_7 ),
    inference(avatar_contradiction_clause,[],[f996])).

fof(f996,plain,
    ( $false
    | spl11_7 ),
    inference(subsumption_resolution,[],[f995,f74])).

fof(f995,plain,
    ( v2_struct_0(sK0)
    | spl11_7 ),
    inference(subsumption_resolution,[],[f994,f77])).

fof(f994,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl11_7 ),
    inference(resolution,[],[f982,f177])).

fof(f177,plain,(
    ! [X0] :
      ( r4_lattice3(X0,k5_lattices(X0),k1_xboole_0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f176,f79])).

fof(f176,plain,(
    ! [X0] :
      ( r4_lattice3(X0,k5_lattices(X0),k1_xboole_0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ l1_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,(
    ! [X0] :
      ( r4_lattice3(X0,k5_lattices(X0),k1_xboole_0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f164,f86])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r4_lattice3(X0,X1,k1_xboole_0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f113,f151])).

fof(f151,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f115,f123])).

fof(f123,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f115,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X2),X2)
      | r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK10(X0,X1,X2),X1)
                  & r2_hidden(sK10(X0,X1,X2),X2)
                  & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f69,f70])).

fof(f70,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK10(X0,X1,X2),X1)
        & r2_hidden(sK10(X0,X1,X2),X2)
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
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
    inference(rectify,[],[f68])).

fof(f68,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f982,plain,
    ( ~ r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0)
    | spl11_7 ),
    inference(avatar_component_clause,[],[f981])).

fof(f981,plain,
    ( spl11_7
  <=> r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f983,plain,
    ( ~ spl11_6
    | ~ spl11_7
    | spl11_5 ),
    inference(avatar_split_clause,[],[f976,f143,f981,f978])).

fof(f143,plain,
    ( spl11_5
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f976,plain,
    ( ~ r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl11_5 ),
    inference(subsumption_resolution,[],[f975,f75])).

fof(f75,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f975,plain,
    ( ~ r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f974,f76])).

fof(f76,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f974,plain,
    ( ~ r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f973,f77])).

fof(f973,plain,
    ( ~ l3_lattices(sK0)
    | ~ r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f972,f963])).

fof(f963,plain,(
    v13_lattices(sK0) ),
    inference(subsumption_resolution,[],[f962,f74])).

fof(f962,plain,
    ( v2_struct_0(sK0)
    | v13_lattices(sK0) ),
    inference(subsumption_resolution,[],[f961,f158])).

fof(f158,plain,(
    v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f157,f77])).

fof(f157,plain,
    ( v8_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f156,f74])).

fof(f156,plain,
    ( v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f82,f75])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f961,plain,
    ( ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | v13_lattices(sK0) ),
    inference(subsumption_resolution,[],[f960,f161])).

fof(f161,plain,(
    v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f160,f77])).

fof(f160,plain,
    ( v9_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f159,f74])).

fof(f159,plain,
    ( v9_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f83,f75])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f960,plain,
    ( ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | v13_lattices(sK0) ),
    inference(subsumption_resolution,[],[f959,f77])).

fof(f959,plain,
    ( ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | v13_lattices(sK0) ),
    inference(subsumption_resolution,[],[f958,f155])).

fof(f155,plain,(
    v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f154,f77])).

fof(f154,plain,
    ( v6_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f153,f74])).

fof(f153,plain,
    ( v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f81,f75])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f958,plain,
    ( ~ v6_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | v13_lattices(sK0) ),
    inference(resolution,[],[f940,f76])).

fof(f940,plain,(
    ! [X0] :
      ( ~ v4_lattice3(X0)
      | ~ v6_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | v13_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f939,f105])).

fof(f105,plain,(
    ! [X4,X0] :
      ( m1_subset_1(sK9(X0,X4),u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ! [X2] :
              ( ( ~ r1_lattices(X0,X2,sK8(X0,X2))
                & r4_lattice3(X0,sK8(X0,X2),sK7(X0))
                & m1_subset_1(sK8(X0,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,sK7(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X6] :
                  ( r1_lattices(X0,sK9(X0,X4),X6)
                  | ~ r4_lattice3(X0,X6,X4)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r4_lattice3(X0,sK9(X0,X4),X4)
              & m1_subset_1(sK9(X0,X4),u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f63,f66,f65,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(X0,X2,X3)
              & r4_lattice3(X0,X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r4_lattice3(X0,X2,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
     => ! [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(X0,X2,X3)
              & r4_lattice3(X0,X3,sK7(X0))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r4_lattice3(X0,X2,sK7(X0))
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,sK7(X0))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK8(X0,X2))
        & r4_lattice3(X0,sK8(X0,X2),sK7(X0))
        & m1_subset_1(sK8(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_lattices(X0,X5,X6)
              | ~ r4_lattice3(X0,X6,X4)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r4_lattice3(X0,X5,X4)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r1_lattices(X0,sK9(X0,X4),X6)
            | ~ r4_lattice3(X0,X6,X4)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r4_lattice3(X0,sK9(X0,X4),X4)
        & m1_subset_1(sK9(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
            ? [X5] :
              ( ! [X6] :
                  ( r1_lattices(X0,X5,X6)
                  | ~ r4_lattice3(X0,X6,X4)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r4_lattice3(X0,X5,X4)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X1] :
            ? [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_lattices(X0,X2,X3)
                | ~ r4_lattice3(X0,X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_lattices(X0,X2,X3)
                | ~ r4_lattice3(X0,X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r4_lattice3(X0,X3,X1)
                 => r1_lattices(X0,X2,X3) ) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_lattice3)).

fof(f939,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v4_lattice3(X0)
      | ~ m1_subset_1(sK9(X0,k1_xboole_0),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f938,f79])).

fof(f938,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v4_lattice3(X0)
      | ~ m1_subset_1(sK9(X0,k1_xboole_0),u1_struct_0(X0))
      | ~ l1_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f931])).

fof(f931,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v4_lattice3(X0)
      | v13_lattices(X0)
      | ~ m1_subset_1(sK9(X0,k1_xboole_0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f790,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f48,f50,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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

fof(f790,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2(X0,sK9(X0,k1_xboole_0)),u1_struct_0(X0))
      | v13_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v4_lattice3(X0) ) ),
    inference(subsumption_resolution,[],[f789,f105])).

fof(f789,plain,(
    ! [X0] :
      ( ~ v6_lattices(X0)
      | v13_lattices(X0)
      | ~ m1_subset_1(sK2(X0,sK9(X0,k1_xboole_0)),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v4_lattice3(X0)
      | ~ m1_subset_1(sK9(X0,k1_xboole_0),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f782])).

fof(f782,plain,(
    ! [X0] :
      ( ~ v6_lattices(X0)
      | v13_lattices(X0)
      | ~ m1_subset_1(sK2(X0,sK9(X0,k1_xboole_0)),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | v13_lattices(X0)
      | ~ m1_subset_1(sK9(X0,k1_xboole_0),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f641,f178])).

fof(f178,plain,(
    ! [X2,X1] :
      ( r4_lattice3(X1,sK2(X1,X2),k1_xboole_0)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | v13_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f175,f79])).

fof(f175,plain,(
    ! [X2,X1] :
      ( r4_lattice3(X1,sK2(X1,X2),k1_xboole_0)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | v13_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X2,X1] :
      ( r4_lattice3(X1,sK2(X1,X2),k1_xboole_0)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | v13_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f164,f94])).

fof(f641,plain,(
    ! [X4,X5] :
      ( ~ r4_lattice3(X4,sK2(X4,sK9(X4,X5)),X5)
      | ~ v6_lattices(X4)
      | v13_lattices(X4)
      | ~ m1_subset_1(sK2(X4,sK9(X4,X5)),u1_struct_0(X4))
      | ~ l3_lattices(X4)
      | ~ v9_lattices(X4)
      | ~ v8_lattices(X4)
      | v2_struct_0(X4)
      | ~ v4_lattice3(X4) ) ),
    inference(subsumption_resolution,[],[f636,f105])).

fof(f636,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(sK9(X4,X5),u1_struct_0(X4))
      | v2_struct_0(X4)
      | ~ v6_lattices(X4)
      | v13_lattices(X4)
      | ~ m1_subset_1(sK2(X4,sK9(X4,X5)),u1_struct_0(X4))
      | ~ l3_lattices(X4)
      | ~ v9_lattices(X4)
      | ~ v8_lattices(X4)
      | ~ r4_lattice3(X4,sK2(X4,sK9(X4,X5)),X5)
      | ~ v4_lattice3(X4) ) ),
    inference(duplicate_literal_removal,[],[f635])).

fof(f635,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(sK9(X4,X5),u1_struct_0(X4))
      | v2_struct_0(X4)
      | ~ v6_lattices(X4)
      | v13_lattices(X4)
      | ~ m1_subset_1(sK2(X4,sK9(X4,X5)),u1_struct_0(X4))
      | ~ l3_lattices(X4)
      | ~ v9_lattices(X4)
      | ~ v8_lattices(X4)
      | ~ r4_lattice3(X4,sK2(X4,sK9(X4,X5)),X5)
      | ~ m1_subset_1(sK2(X4,sK9(X4,X5)),u1_struct_0(X4))
      | ~ v4_lattice3(X4)
      | ~ l3_lattices(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f380,f107])).

fof(f107,plain,(
    ! [X6,X4,X0] :
      ( r1_lattices(X0,sK9(X0,X4),X6)
      | ~ r4_lattice3(X0,X6,X4)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f380,plain,(
    ! [X2,X1] :
      ( ~ r1_lattices(X1,X2,sK2(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ v6_lattices(X1)
      | v13_lattices(X1)
      | ~ m1_subset_1(sK2(X1,X2),u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f378,f79])).

fof(f378,plain,(
    ! [X2,X1] :
      ( v13_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_lattices(X1)
      | v2_struct_0(X1)
      | ~ v6_lattices(X1)
      | ~ r1_lattices(X1,X2,sK2(X1,X2))
      | ~ m1_subset_1(sK2(X1,X2),u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1) ) ),
    inference(trivial_inequality_removal,[],[f377])).

fof(f377,plain,(
    ! [X2,X1] :
      ( X2 != X2
      | v13_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_lattices(X1)
      | v2_struct_0(X1)
      | ~ v6_lattices(X1)
      | ~ r1_lattices(X1,X2,sK2(X1,X2))
      | ~ m1_subset_1(sK2(X1,X2),u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f374])).

fof(f374,plain,(
    ! [X2,X1] :
      ( X2 != X2
      | v13_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_lattices(X1)
      | v2_struct_0(X1)
      | ~ v6_lattices(X1)
      | ~ r1_lattices(X1,X2,sK2(X1,X2))
      | ~ m1_subset_1(sK2(X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(superposition,[],[f326,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f326,plain,(
    ! [X4,X5] :
      ( k2_lattices(X4,X5,sK2(X4,X5)) != X5
      | v13_lattices(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_lattices(X4)
      | v2_struct_0(X4)
      | ~ v6_lattices(X4) ) ),
    inference(subsumption_resolution,[],[f318,f94])).

fof(f318,plain,(
    ! [X4,X5] :
      ( k2_lattices(X4,X5,sK2(X4,X5)) != X5
      | v13_lattices(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_lattices(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(sK2(X4,X5),u1_struct_0(X4))
      | ~ v6_lattices(X4) ) ),
    inference(duplicate_literal_removal,[],[f315])).

fof(f315,plain,(
    ! [X4,X5] :
      ( k2_lattices(X4,X5,sK2(X4,X5)) != X5
      | v13_lattices(X4)
      | k2_lattices(X4,X5,sK2(X4,X5)) != X5
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_lattices(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(sK2(X4,X5),u1_struct_0(X4))
      | ~ v6_lattices(X4)
      | ~ l1_lattices(X4)
      | v2_struct_0(X4) ) ),
    inference(superposition,[],[f95,f96])).

fof(f96,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f53,f55,f54])).

fof(f54,plain,(
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

fof(f55,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f95,plain,(
    ! [X0,X1] :
      ( k2_lattices(X0,sK2(X0,X1),X1) != X1
      | v13_lattices(X0)
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f972,plain,
    ( ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f971,f74])).

fof(f971,plain,
    ( v2_struct_0(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | spl11_5 ),
    inference(trivial_inequality_removal,[],[f968])).

fof(f968,plain,
    ( k5_lattices(sK0) != k5_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | spl11_5 ),
    inference(superposition,[],[f144,f357])).

fof(f357,plain,(
    ! [X2,X1] :
      ( k5_lattices(X1) = k15_lattice3(X1,X2)
      | v2_struct_0(X1)
      | ~ v13_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ r4_lattice3(X1,k5_lattices(X1),X2)
      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f356,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | k15_lattice3(X0,X1) = X2
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f59,f60])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK6(X0,X1,X2))
        & r4_lattice3(X0,sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
    inference(rectify,[],[f58])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f356,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK6(X1,X2,k5_lattices(X1)),u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ v13_lattices(X1)
      | k5_lattices(X1) = k15_lattice3(X1,X2)
      | ~ r4_lattice3(X1,k5_lattices(X1),X2)
      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f355,f82])).

fof(f355,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK6(X1,X2,k5_lattices(X1)),u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v8_lattices(X1)
      | v2_struct_0(X1)
      | ~ v13_lattices(X1)
      | k5_lattices(X1) = k15_lattice3(X1,X2)
      | ~ r4_lattice3(X1,k5_lattices(X1),X2)
      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f352,f83])).

fof(f352,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK6(X1,X2,k5_lattices(X1)),u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | v2_struct_0(X1)
      | ~ v13_lattices(X1)
      | k5_lattices(X1) = k15_lattice3(X1,X2)
      | ~ r4_lattice3(X1,k5_lattices(X1),X2)
      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f351])).

fof(f351,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK6(X1,X2,k5_lattices(X1)),u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | v2_struct_0(X1)
      | ~ v13_lattices(X1)
      | k5_lattices(X1) = k15_lattice3(X1,X2)
      | ~ r4_lattice3(X1,k5_lattices(X1),X2)
      | ~ m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f311,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X2,sK6(X0,X1,X2))
      | k15_lattice3(X0,X1) = X2
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | ~ r1_lattices(X0,X2,sK6(X0,X1,X2))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f311,plain,(
    ! [X15,X16] :
      ( r1_lattices(X15,k5_lattices(X15),X16)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ l3_lattices(X15)
      | ~ v9_lattices(X15)
      | ~ v8_lattices(X15)
      | v2_struct_0(X15)
      | ~ v13_lattices(X15) ) ),
    inference(global_subsumption,[],[f79,f86,f310])).

fof(f310,plain,(
    ! [X15,X16] :
      ( r1_lattices(X15,k5_lattices(X15),X16)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(k5_lattices(X15),u1_struct_0(X15))
      | ~ l3_lattices(X15)
      | ~ v9_lattices(X15)
      | ~ v8_lattices(X15)
      | v2_struct_0(X15)
      | ~ v13_lattices(X15) ) ),
    inference(subsumption_resolution,[],[f295,f79])).

fof(f295,plain,(
    ! [X15,X16] :
      ( r1_lattices(X15,k5_lattices(X15),X16)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(k5_lattices(X15),u1_struct_0(X15))
      | ~ l3_lattices(X15)
      | ~ v9_lattices(X15)
      | ~ v8_lattices(X15)
      | v2_struct_0(X15)
      | ~ v13_lattices(X15)
      | ~ l1_lattices(X15) ) ),
    inference(trivial_inequality_removal,[],[f294])).

fof(f294,plain,(
    ! [X15,X16] :
      ( k5_lattices(X15) != k5_lattices(X15)
      | r1_lattices(X15,k5_lattices(X15),X16)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(k5_lattices(X15),u1_struct_0(X15))
      | ~ l3_lattices(X15)
      | ~ v9_lattices(X15)
      | ~ v8_lattices(X15)
      | v2_struct_0(X15)
      | ~ v13_lattices(X15)
      | ~ l1_lattices(X15) ) ),
    inference(duplicate_literal_removal,[],[f293])).

fof(f293,plain,(
    ! [X15,X16] :
      ( k5_lattices(X15) != k5_lattices(X15)
      | r1_lattices(X15,k5_lattices(X15),X16)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(k5_lattices(X15),u1_struct_0(X15))
      | ~ l3_lattices(X15)
      | ~ v9_lattices(X15)
      | ~ v8_lattices(X15)
      | v2_struct_0(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ v13_lattices(X15)
      | ~ l1_lattices(X15)
      | v2_struct_0(X15) ) ),
    inference(superposition,[],[f85,f147])).

fof(f147,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f120,f86])).

fof(f120,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f4])).

% (19193)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) != X1
      | r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f144,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl11_5 ),
    inference(avatar_component_clause,[],[f143])).

fof(f967,plain,(
    spl11_4 ),
    inference(avatar_contradiction_clause,[],[f966])).

fof(f966,plain,
    ( $false
    | spl11_4 ),
    inference(subsumption_resolution,[],[f141,f77])).

fof(f141,plain,
    ( ~ l3_lattices(sK0)
    | spl11_4 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl11_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f965,plain,(
    spl11_3 ),
    inference(avatar_contradiction_clause,[],[f964])).

fof(f964,plain,
    ( $false
    | spl11_3 ),
    inference(subsumption_resolution,[],[f963,f138])).

fof(f138,plain,
    ( ~ v13_lattices(sK0)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl11_3
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f149,plain,(
    spl11_2 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl11_2 ),
    inference(subsumption_resolution,[],[f135,f75])).

fof(f135,plain,
    ( ~ v10_lattices(sK0)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl11_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f145,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f78,f143,f140,f137,f134,f131])).

fof(f78,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:46:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (19185)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (19195)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (19184)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.52  % (19187)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (19201)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.54  % (19186)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.54  % (19192)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.37/0.55  % (19188)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.37/0.56  % (19202)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.37/0.56  % (19197)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.37/0.56  % (19202)Refutation not found, incomplete strategy% (19202)------------------------------
% 1.37/0.56  % (19202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (19202)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (19202)Memory used [KB]: 10618
% 1.37/0.56  % (19202)Time elapsed: 0.128 s
% 1.37/0.56  % (19202)------------------------------
% 1.37/0.56  % (19202)------------------------------
% 1.37/0.56  % (19182)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.37/0.56  % (19183)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.63/0.56  % (19198)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.63/0.57  % (19200)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.63/0.57  % (19196)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 1.63/0.58  % (19190)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.63/0.58  % (19191)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.63/0.58  % (19184)Refutation found. Thanks to Tanya!
% 1.63/0.58  % SZS status Theorem for theBenchmark
% 1.63/0.58  % (19189)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.63/0.58  % (19183)Refutation not found, incomplete strategy% (19183)------------------------------
% 1.63/0.58  % (19183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (19183)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (19183)Memory used [KB]: 10618
% 1.63/0.58  % (19183)Time elapsed: 0.140 s
% 1.63/0.58  % (19183)------------------------------
% 1.63/0.58  % (19183)------------------------------
% 1.63/0.58  % (19199)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.63/0.58  % SZS output start Proof for theBenchmark
% 1.63/0.58  fof(f1009,plain,(
% 1.63/0.58    $false),
% 1.63/0.58    inference(avatar_sat_refutation,[],[f145,f149,f965,f967,f983,f997,f1006,f1008])).
% 1.63/0.58  fof(f1008,plain,(
% 1.63/0.58    ~spl11_1),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f1007])).
% 1.63/0.58  fof(f1007,plain,(
% 1.63/0.58    $false | ~spl11_1),
% 1.63/0.58    inference(subsumption_resolution,[],[f132,f74])).
% 1.63/0.58  fof(f74,plain,(
% 1.63/0.58    ~v2_struct_0(sK0)),
% 1.63/0.58    inference(cnf_transformation,[],[f41])).
% 1.63/0.58  fof(f41,plain,(
% 1.63/0.58    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 1.63/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f40])).
% 1.63/0.58  fof(f40,plain,(
% 1.63/0.58    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 1.63/0.58    introduced(choice_axiom,[])).
% 1.63/0.58  fof(f20,plain,(
% 1.63/0.58    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.63/0.58    inference(flattening,[],[f19])).
% 1.63/0.58  fof(f19,plain,(
% 1.63/0.58    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.63/0.58    inference(ennf_transformation,[],[f14])).
% 1.63/0.58  fof(f14,negated_conjecture,(
% 1.63/0.58    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.63/0.58    inference(negated_conjecture,[],[f13])).
% 1.63/0.58  fof(f13,conjecture,(
% 1.63/0.58    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).
% 1.63/0.58  fof(f132,plain,(
% 1.63/0.58    v2_struct_0(sK0) | ~spl11_1),
% 1.63/0.58    inference(avatar_component_clause,[],[f131])).
% 1.63/0.58  % (19194)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.63/0.58  fof(f131,plain,(
% 1.63/0.58    spl11_1 <=> v2_struct_0(sK0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.63/0.58  fof(f1006,plain,(
% 1.63/0.58    spl11_6),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f1005])).
% 1.63/0.58  fof(f1005,plain,(
% 1.63/0.58    $false | spl11_6),
% 1.63/0.58    inference(subsumption_resolution,[],[f1004,f74])).
% 1.63/0.58  fof(f1004,plain,(
% 1.63/0.58    v2_struct_0(sK0) | spl11_6),
% 1.63/0.58    inference(subsumption_resolution,[],[f999,f150])).
% 1.63/0.58  fof(f150,plain,(
% 1.63/0.58    l1_lattices(sK0)),
% 1.63/0.58    inference(resolution,[],[f79,f77])).
% 1.63/0.58  fof(f77,plain,(
% 1.63/0.58    l3_lattices(sK0)),
% 1.63/0.58    inference(cnf_transformation,[],[f41])).
% 1.63/0.58  fof(f79,plain,(
% 1.63/0.58    ( ! [X0] : (~l3_lattices(X0) | l1_lattices(X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f21])).
% 1.63/0.58  fof(f21,plain,(
% 1.63/0.58    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 1.63/0.58    inference(ennf_transformation,[],[f15])).
% 1.63/0.58  fof(f15,plain,(
% 1.63/0.58    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 1.63/0.58    inference(pure_predicate_removal,[],[f6])).
% 1.63/0.58  fof(f6,axiom,(
% 1.63/0.58    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 1.63/0.58  fof(f999,plain,(
% 1.63/0.58    ~l1_lattices(sK0) | v2_struct_0(sK0) | spl11_6),
% 1.63/0.58    inference(resolution,[],[f979,f86])).
% 1.63/0.58  fof(f86,plain,(
% 1.63/0.58    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f27])).
% 1.63/0.58  fof(f27,plain,(
% 1.63/0.58    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.58    inference(flattening,[],[f26])).
% 1.63/0.58  fof(f26,plain,(
% 1.63/0.58    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.63/0.58    inference(ennf_transformation,[],[f5])).
% 1.63/0.58  fof(f5,axiom,(
% 1.63/0.58    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).
% 1.63/0.58  fof(f979,plain,(
% 1.63/0.58    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | spl11_6),
% 1.63/0.58    inference(avatar_component_clause,[],[f978])).
% 1.63/0.58  fof(f978,plain,(
% 1.63/0.58    spl11_6 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 1.63/0.58  fof(f997,plain,(
% 1.63/0.58    spl11_7),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f996])).
% 1.63/0.58  fof(f996,plain,(
% 1.63/0.58    $false | spl11_7),
% 1.63/0.58    inference(subsumption_resolution,[],[f995,f74])).
% 1.63/0.58  fof(f995,plain,(
% 1.63/0.58    v2_struct_0(sK0) | spl11_7),
% 1.63/0.58    inference(subsumption_resolution,[],[f994,f77])).
% 1.63/0.58  fof(f994,plain,(
% 1.63/0.58    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl11_7),
% 1.63/0.58    inference(resolution,[],[f982,f177])).
% 1.63/0.58  fof(f177,plain,(
% 1.63/0.58    ( ! [X0] : (r4_lattice3(X0,k5_lattices(X0),k1_xboole_0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f176,f79])).
% 1.63/0.58  fof(f176,plain,(
% 1.63/0.58    ( ! [X0] : (r4_lattice3(X0,k5_lattices(X0),k1_xboole_0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~l1_lattices(X0)) )),
% 1.63/0.58    inference(duplicate_literal_removal,[],[f165])).
% 1.63/0.58  fof(f165,plain,(
% 1.63/0.58    ( ! [X0] : (r4_lattice3(X0,k5_lattices(X0),k1_xboole_0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.58    inference(resolution,[],[f164,f86])).
% 1.63/0.58  fof(f164,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | r4_lattice3(X0,X1,k1_xboole_0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.58    inference(resolution,[],[f113,f151])).
% 1.63/0.58  fof(f151,plain,(
% 1.63/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.63/0.58    inference(superposition,[],[f115,f123])).
% 1.63/0.58  fof(f123,plain,(
% 1.63/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.63/0.58    inference(equality_resolution,[],[f118])).
% 1.63/0.58  fof(f118,plain,(
% 1.63/0.58    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.63/0.58    inference(cnf_transformation,[],[f73])).
% 1.63/0.58  fof(f73,plain,(
% 1.63/0.58    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.63/0.58    inference(flattening,[],[f72])).
% 1.63/0.58  fof(f72,plain,(
% 1.63/0.58    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.63/0.58    inference(nnf_transformation,[],[f1])).
% 1.63/0.58  fof(f1,axiom,(
% 1.63/0.58    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.63/0.58  fof(f115,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f2])).
% 1.63/0.58  fof(f2,axiom,(
% 1.63/0.58    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.63/0.58  fof(f113,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK10(X0,X1,X2),X2) | r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f71])).
% 1.63/0.58  fof(f71,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK10(X0,X1,X2),X1) & r2_hidden(sK10(X0,X1,X2),X2) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f69,f70])).
% 1.63/0.58  fof(f70,plain,(
% 1.63/0.58    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK10(X0,X1,X2),X1) & r2_hidden(sK10(X0,X1,X2),X2) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0))))),
% 1.63/0.58    introduced(choice_axiom,[])).
% 1.63/0.58  fof(f69,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.58    inference(rectify,[],[f68])).
% 1.63/0.58  fof(f68,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.58    inference(nnf_transformation,[],[f39])).
% 1.63/0.58  fof(f39,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.58    inference(flattening,[],[f38])).
% 1.63/0.58  fof(f38,plain,(
% 1.63/0.58    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.63/0.58    inference(ennf_transformation,[],[f9])).
% 1.63/0.58  fof(f9,axiom,(
% 1.63/0.58    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 1.63/0.58  fof(f982,plain,(
% 1.63/0.58    ~r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0) | spl11_7),
% 1.63/0.58    inference(avatar_component_clause,[],[f981])).
% 1.63/0.58  fof(f981,plain,(
% 1.63/0.58    spl11_7 <=> r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 1.63/0.58  fof(f983,plain,(
% 1.63/0.58    ~spl11_6 | ~spl11_7 | spl11_5),
% 1.63/0.58    inference(avatar_split_clause,[],[f976,f143,f981,f978])).
% 1.63/0.58  fof(f143,plain,(
% 1.63/0.58    spl11_5 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.63/0.59  fof(f976,plain,(
% 1.63/0.59    ~r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | spl11_5),
% 1.63/0.59    inference(subsumption_resolution,[],[f975,f75])).
% 1.63/0.59  fof(f75,plain,(
% 1.63/0.59    v10_lattices(sK0)),
% 1.63/0.59    inference(cnf_transformation,[],[f41])).
% 1.63/0.59  fof(f975,plain,(
% 1.63/0.59    ~r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v10_lattices(sK0) | spl11_5),
% 1.63/0.59    inference(subsumption_resolution,[],[f974,f76])).
% 1.63/0.59  fof(f76,plain,(
% 1.63/0.59    v4_lattice3(sK0)),
% 1.63/0.59    inference(cnf_transformation,[],[f41])).
% 1.63/0.59  fof(f974,plain,(
% 1.63/0.59    ~r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | spl11_5),
% 1.63/0.59    inference(subsumption_resolution,[],[f973,f77])).
% 1.63/0.59  fof(f973,plain,(
% 1.63/0.59    ~l3_lattices(sK0) | ~r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | spl11_5),
% 1.63/0.59    inference(subsumption_resolution,[],[f972,f963])).
% 1.63/0.59  fof(f963,plain,(
% 1.63/0.59    v13_lattices(sK0)),
% 1.63/0.59    inference(subsumption_resolution,[],[f962,f74])).
% 1.63/0.59  fof(f962,plain,(
% 1.63/0.59    v2_struct_0(sK0) | v13_lattices(sK0)),
% 1.63/0.59    inference(subsumption_resolution,[],[f961,f158])).
% 1.63/0.59  fof(f158,plain,(
% 1.63/0.59    v8_lattices(sK0)),
% 1.63/0.59    inference(subsumption_resolution,[],[f157,f77])).
% 1.63/0.59  fof(f157,plain,(
% 1.63/0.59    v8_lattices(sK0) | ~l3_lattices(sK0)),
% 1.63/0.59    inference(subsumption_resolution,[],[f156,f74])).
% 1.63/0.59  fof(f156,plain,(
% 1.63/0.59    v8_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.63/0.59    inference(resolution,[],[f82,f75])).
% 1.63/0.59  fof(f82,plain,(
% 1.63/0.59    ( ! [X0] : (~v10_lattices(X0) | v8_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f23])).
% 1.63/0.59  fof(f23,plain,(
% 1.63/0.59    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.63/0.59    inference(flattening,[],[f22])).
% 1.63/0.59  fof(f22,plain,(
% 1.63/0.59    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.63/0.59    inference(ennf_transformation,[],[f18])).
% 1.63/0.59  fof(f18,plain,(
% 1.63/0.59    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 1.63/0.59    inference(pure_predicate_removal,[],[f17])).
% 1.63/0.59  fof(f17,plain,(
% 1.63/0.59    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.63/0.59    inference(pure_predicate_removal,[],[f16])).
% 1.63/0.59  fof(f16,plain,(
% 1.63/0.59    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.63/0.59    inference(pure_predicate_removal,[],[f3])).
% 1.63/0.59  fof(f3,axiom,(
% 1.63/0.59    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 1.63/0.59  fof(f961,plain,(
% 1.63/0.59    ~v8_lattices(sK0) | v2_struct_0(sK0) | v13_lattices(sK0)),
% 1.63/0.59    inference(subsumption_resolution,[],[f960,f161])).
% 1.63/0.59  fof(f161,plain,(
% 1.63/0.59    v9_lattices(sK0)),
% 1.63/0.59    inference(subsumption_resolution,[],[f160,f77])).
% 1.63/0.59  fof(f160,plain,(
% 1.63/0.59    v9_lattices(sK0) | ~l3_lattices(sK0)),
% 1.63/0.59    inference(subsumption_resolution,[],[f159,f74])).
% 1.63/0.59  fof(f159,plain,(
% 1.63/0.59    v9_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.63/0.59    inference(resolution,[],[f83,f75])).
% 1.63/0.59  fof(f83,plain,(
% 1.63/0.59    ( ! [X0] : (~v10_lattices(X0) | v9_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f23])).
% 1.63/0.59  fof(f960,plain,(
% 1.63/0.59    ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | v13_lattices(sK0)),
% 1.63/0.59    inference(subsumption_resolution,[],[f959,f77])).
% 1.63/0.59  fof(f959,plain,(
% 1.63/0.59    ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | v13_lattices(sK0)),
% 1.63/0.59    inference(subsumption_resolution,[],[f958,f155])).
% 1.63/0.59  fof(f155,plain,(
% 1.63/0.59    v6_lattices(sK0)),
% 1.63/0.59    inference(subsumption_resolution,[],[f154,f77])).
% 1.63/0.59  fof(f154,plain,(
% 1.63/0.59    v6_lattices(sK0) | ~l3_lattices(sK0)),
% 1.63/0.59    inference(subsumption_resolution,[],[f153,f74])).
% 1.63/0.59  fof(f153,plain,(
% 1.63/0.59    v6_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.63/0.59    inference(resolution,[],[f81,f75])).
% 1.63/0.59  fof(f81,plain,(
% 1.63/0.59    ( ! [X0] : (~v10_lattices(X0) | v6_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f23])).
% 1.63/0.59  fof(f958,plain,(
% 1.63/0.59    ~v6_lattices(sK0) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | v13_lattices(sK0)),
% 1.63/0.59    inference(resolution,[],[f940,f76])).
% 1.63/0.59  fof(f940,plain,(
% 1.63/0.59    ( ! [X0] : (~v4_lattice3(X0) | ~v6_lattices(X0) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0) | v13_lattices(X0)) )),
% 1.63/0.59    inference(subsumption_resolution,[],[f939,f105])).
% 1.63/0.59  fof(f105,plain,(
% 1.63/0.59    ( ! [X4,X0] : (m1_subset_1(sK9(X0,X4),u1_struct_0(X0)) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f67])).
% 1.63/0.59  fof(f67,plain,(
% 1.63/0.59    ! [X0] : (((v4_lattice3(X0) | ! [X2] : ((~r1_lattices(X0,X2,sK8(X0,X2)) & r4_lattice3(X0,sK8(X0,X2),sK7(X0)) & m1_subset_1(sK8(X0,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,sK7(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X6] : (r1_lattices(X0,sK9(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,sK9(X0,X4),X4) & m1_subset_1(sK9(X0,X4),u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f63,f66,f65,f64])).
% 1.63/0.59  fof(f64,plain,(
% 1.63/0.59    ! [X0] : (? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) => ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,sK7(X0)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,sK7(X0)) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f65,plain,(
% 1.63/0.59    ! [X2,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,sK7(X0)) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK8(X0,X2)) & r4_lattice3(X0,sK8(X0,X2),sK7(X0)) & m1_subset_1(sK8(X0,X2),u1_struct_0(X0))))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f66,plain,(
% 1.63/0.59    ! [X4,X0] : (? [X5] : (! [X6] : (r1_lattices(X0,X5,X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,X5,X4) & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r1_lattices(X0,sK9(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,sK9(X0,X4),X4) & m1_subset_1(sK9(X0,X4),u1_struct_0(X0))))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f63,plain,(
% 1.63/0.59    ! [X0] : (((v4_lattice3(X0) | ? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : ? [X5] : (! [X6] : (r1_lattices(X0,X5,X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,X5,X4) & m1_subset_1(X5,u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(rectify,[],[f62])).
% 1.63/0.59  fof(f62,plain,(
% 1.63/0.59    ! [X0] : (((v4_lattice3(X0) | ? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X1] : ? [X2] : (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(nnf_transformation,[],[f37])).
% 1.63/0.59  fof(f37,plain,(
% 1.63/0.59    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(flattening,[],[f36])).
% 1.63/0.59  fof(f36,plain,(
% 1.63/0.59    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.63/0.59    inference(ennf_transformation,[],[f10])).
% 1.63/0.59  fof(f10,axiom,(
% 1.63/0.59    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_lattice3)).
% 1.63/0.59  fof(f939,plain,(
% 1.63/0.59    ( ! [X0] : (v13_lattices(X0) | ~v6_lattices(X0) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0) | ~v4_lattice3(X0) | ~m1_subset_1(sK9(X0,k1_xboole_0),u1_struct_0(X0))) )),
% 1.63/0.59    inference(subsumption_resolution,[],[f938,f79])).
% 1.63/0.59  fof(f938,plain,(
% 1.63/0.59    ( ! [X0] : (v13_lattices(X0) | ~v6_lattices(X0) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0) | ~v4_lattice3(X0) | ~m1_subset_1(sK9(X0,k1_xboole_0),u1_struct_0(X0)) | ~l1_lattices(X0)) )),
% 1.63/0.59    inference(duplicate_literal_removal,[],[f931])).
% 1.63/0.59  fof(f931,plain,(
% 1.63/0.59    ( ! [X0] : (v13_lattices(X0) | ~v6_lattices(X0) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0) | ~v4_lattice3(X0) | v13_lattices(X0) | ~m1_subset_1(sK9(X0,k1_xboole_0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(resolution,[],[f790,f94])).
% 1.63/0.59  fof(f94,plain,(
% 1.63/0.59    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f51])).
% 1.63/0.59  fof(f51,plain,(
% 1.63/0.59    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f48,f50,f49])).
% 1.63/0.59  fof(f49,plain,(
% 1.63/0.59    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f50,plain,(
% 1.63/0.59    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f48,plain,(
% 1.63/0.59    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(rectify,[],[f47])).
% 1.63/0.59  fof(f47,plain,(
% 1.63/0.59    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(nnf_transformation,[],[f31])).
% 1.63/0.59  fof(f31,plain,(
% 1.63/0.59    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(flattening,[],[f30])).
% 1.63/0.59  fof(f30,plain,(
% 1.63/0.59    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.63/0.59    inference(ennf_transformation,[],[f8])).
% 1.63/0.59  fof(f8,axiom,(
% 1.63/0.59    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).
% 1.63/0.59  fof(f790,plain,(
% 1.63/0.59    ( ! [X0] : (~m1_subset_1(sK2(X0,sK9(X0,k1_xboole_0)),u1_struct_0(X0)) | v13_lattices(X0) | ~v6_lattices(X0) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0) | ~v4_lattice3(X0)) )),
% 1.63/0.59    inference(subsumption_resolution,[],[f789,f105])).
% 1.63/0.59  fof(f789,plain,(
% 1.63/0.59    ( ! [X0] : (~v6_lattices(X0) | v13_lattices(X0) | ~m1_subset_1(sK2(X0,sK9(X0,k1_xboole_0)),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0) | ~v4_lattice3(X0) | ~m1_subset_1(sK9(X0,k1_xboole_0),u1_struct_0(X0))) )),
% 1.63/0.59    inference(duplicate_literal_removal,[],[f782])).
% 1.63/0.59  fof(f782,plain,(
% 1.63/0.59    ( ! [X0] : (~v6_lattices(X0) | v13_lattices(X0) | ~m1_subset_1(sK2(X0,sK9(X0,k1_xboole_0)),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | v13_lattices(X0) | ~m1_subset_1(sK9(X0,k1_xboole_0),u1_struct_0(X0))) )),
% 1.63/0.59    inference(resolution,[],[f641,f178])).
% 1.63/0.59  fof(f178,plain,(
% 1.63/0.59    ( ! [X2,X1] : (r4_lattice3(X1,sK2(X1,X2),k1_xboole_0) | ~l3_lattices(X1) | v2_struct_0(X1) | v13_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1))) )),
% 1.63/0.59    inference(subsumption_resolution,[],[f175,f79])).
% 1.63/0.59  fof(f175,plain,(
% 1.63/0.59    ( ! [X2,X1] : (r4_lattice3(X1,sK2(X1,X2),k1_xboole_0) | ~l3_lattices(X1) | v2_struct_0(X1) | v13_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_lattices(X1)) )),
% 1.63/0.59    inference(duplicate_literal_removal,[],[f166])).
% 1.63/0.59  fof(f166,plain,(
% 1.63/0.59    ( ! [X2,X1] : (r4_lattice3(X1,sK2(X1,X2),k1_xboole_0) | ~l3_lattices(X1) | v2_struct_0(X1) | v13_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_lattices(X1) | v2_struct_0(X1)) )),
% 1.63/0.59    inference(resolution,[],[f164,f94])).
% 1.63/0.59  fof(f641,plain,(
% 1.63/0.59    ( ! [X4,X5] : (~r4_lattice3(X4,sK2(X4,sK9(X4,X5)),X5) | ~v6_lattices(X4) | v13_lattices(X4) | ~m1_subset_1(sK2(X4,sK9(X4,X5)),u1_struct_0(X4)) | ~l3_lattices(X4) | ~v9_lattices(X4) | ~v8_lattices(X4) | v2_struct_0(X4) | ~v4_lattice3(X4)) )),
% 1.63/0.59    inference(subsumption_resolution,[],[f636,f105])).
% 1.63/0.59  fof(f636,plain,(
% 1.63/0.59    ( ! [X4,X5] : (~m1_subset_1(sK9(X4,X5),u1_struct_0(X4)) | v2_struct_0(X4) | ~v6_lattices(X4) | v13_lattices(X4) | ~m1_subset_1(sK2(X4,sK9(X4,X5)),u1_struct_0(X4)) | ~l3_lattices(X4) | ~v9_lattices(X4) | ~v8_lattices(X4) | ~r4_lattice3(X4,sK2(X4,sK9(X4,X5)),X5) | ~v4_lattice3(X4)) )),
% 1.63/0.59    inference(duplicate_literal_removal,[],[f635])).
% 1.63/0.59  fof(f635,plain,(
% 1.63/0.59    ( ! [X4,X5] : (~m1_subset_1(sK9(X4,X5),u1_struct_0(X4)) | v2_struct_0(X4) | ~v6_lattices(X4) | v13_lattices(X4) | ~m1_subset_1(sK2(X4,sK9(X4,X5)),u1_struct_0(X4)) | ~l3_lattices(X4) | ~v9_lattices(X4) | ~v8_lattices(X4) | ~r4_lattice3(X4,sK2(X4,sK9(X4,X5)),X5) | ~m1_subset_1(sK2(X4,sK9(X4,X5)),u1_struct_0(X4)) | ~v4_lattice3(X4) | ~l3_lattices(X4) | v2_struct_0(X4)) )),
% 1.63/0.59    inference(resolution,[],[f380,f107])).
% 1.63/0.59  fof(f107,plain,(
% 1.63/0.59    ( ! [X6,X4,X0] : (r1_lattices(X0,sK9(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f67])).
% 1.63/0.59  fof(f380,plain,(
% 1.63/0.59    ( ! [X2,X1] : (~r1_lattices(X1,X2,sK2(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~v6_lattices(X1) | v13_lattices(X1) | ~m1_subset_1(sK2(X1,X2),u1_struct_0(X1)) | ~l3_lattices(X1) | ~v9_lattices(X1) | ~v8_lattices(X1)) )),
% 1.63/0.59    inference(subsumption_resolution,[],[f378,f79])).
% 1.63/0.59  fof(f378,plain,(
% 1.63/0.59    ( ! [X2,X1] : (v13_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_lattices(X1) | v2_struct_0(X1) | ~v6_lattices(X1) | ~r1_lattices(X1,X2,sK2(X1,X2)) | ~m1_subset_1(sK2(X1,X2),u1_struct_0(X1)) | ~l3_lattices(X1) | ~v9_lattices(X1) | ~v8_lattices(X1)) )),
% 1.63/0.59    inference(trivial_inequality_removal,[],[f377])).
% 1.63/0.59  fof(f377,plain,(
% 1.63/0.59    ( ! [X2,X1] : (X2 != X2 | v13_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_lattices(X1) | v2_struct_0(X1) | ~v6_lattices(X1) | ~r1_lattices(X1,X2,sK2(X1,X2)) | ~m1_subset_1(sK2(X1,X2),u1_struct_0(X1)) | ~l3_lattices(X1) | ~v9_lattices(X1) | ~v8_lattices(X1)) )),
% 1.63/0.59    inference(duplicate_literal_removal,[],[f374])).
% 1.63/0.59  fof(f374,plain,(
% 1.63/0.59    ( ! [X2,X1] : (X2 != X2 | v13_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_lattices(X1) | v2_struct_0(X1) | ~v6_lattices(X1) | ~r1_lattices(X1,X2,sK2(X1,X2)) | ~m1_subset_1(sK2(X1,X2),u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v9_lattices(X1) | ~v8_lattices(X1) | v2_struct_0(X1)) )),
% 1.63/0.59    inference(superposition,[],[f326,f84])).
% 1.63/0.59  fof(f84,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f42])).
% 1.63/0.59  fof(f42,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(nnf_transformation,[],[f25])).
% 1.63/0.59  fof(f25,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(flattening,[],[f24])).
% 1.63/0.59  fof(f24,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 1.63/0.59    inference(ennf_transformation,[],[f7])).
% 1.63/0.59  fof(f7,axiom,(
% 1.63/0.59    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 1.63/0.59  fof(f326,plain,(
% 1.63/0.59    ( ! [X4,X5] : (k2_lattices(X4,X5,sK2(X4,X5)) != X5 | v13_lattices(X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_lattices(X4) | v2_struct_0(X4) | ~v6_lattices(X4)) )),
% 1.63/0.59    inference(subsumption_resolution,[],[f318,f94])).
% 1.63/0.59  fof(f318,plain,(
% 1.63/0.59    ( ! [X4,X5] : (k2_lattices(X4,X5,sK2(X4,X5)) != X5 | v13_lattices(X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_lattices(X4) | v2_struct_0(X4) | ~m1_subset_1(sK2(X4,X5),u1_struct_0(X4)) | ~v6_lattices(X4)) )),
% 1.63/0.59    inference(duplicate_literal_removal,[],[f315])).
% 1.63/0.59  fof(f315,plain,(
% 1.63/0.59    ( ! [X4,X5] : (k2_lattices(X4,X5,sK2(X4,X5)) != X5 | v13_lattices(X4) | k2_lattices(X4,X5,sK2(X4,X5)) != X5 | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_lattices(X4) | v2_struct_0(X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~m1_subset_1(sK2(X4,X5),u1_struct_0(X4)) | ~v6_lattices(X4) | ~l1_lattices(X4) | v2_struct_0(X4)) )),
% 1.63/0.59    inference(superposition,[],[f95,f96])).
% 1.63/0.59  fof(f96,plain,(
% 1.63/0.59    ( ! [X4,X0,X3] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f56])).
% 1.63/0.59  fof(f56,plain,(
% 1.63/0.59    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f53,f55,f54])).
% 1.63/0.59  fof(f54,plain,(
% 1.63/0.59    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f55,plain,(
% 1.63/0.59    ! [X0] : (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f53,plain,(
% 1.63/0.59    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(rectify,[],[f52])).
% 1.63/0.59  fof(f52,plain,(
% 1.63/0.59    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(nnf_transformation,[],[f33])).
% 1.63/0.59  fof(f33,plain,(
% 1.63/0.59    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(flattening,[],[f32])).
% 1.63/0.59  fof(f32,plain,(
% 1.63/0.59    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.63/0.59    inference(ennf_transformation,[],[f12])).
% 1.63/0.59  fof(f12,axiom,(
% 1.63/0.59    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).
% 1.63/0.59  fof(f95,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k2_lattices(X0,sK2(X0,X1),X1) != X1 | v13_lattices(X0) | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f51])).
% 1.63/0.59  fof(f972,plain,(
% 1.63/0.59    ~v13_lattices(sK0) | ~l3_lattices(sK0) | ~r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | spl11_5),
% 1.63/0.59    inference(subsumption_resolution,[],[f971,f74])).
% 1.63/0.59  fof(f971,plain,(
% 1.63/0.59    v2_struct_0(sK0) | ~v13_lattices(sK0) | ~l3_lattices(sK0) | ~r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | spl11_5),
% 1.63/0.59    inference(trivial_inequality_removal,[],[f968])).
% 1.63/0.59  fof(f968,plain,(
% 1.63/0.59    k5_lattices(sK0) != k5_lattices(sK0) | v2_struct_0(sK0) | ~v13_lattices(sK0) | ~l3_lattices(sK0) | ~r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | spl11_5),
% 1.63/0.59    inference(superposition,[],[f144,f357])).
% 1.63/0.59  fof(f357,plain,(
% 1.63/0.59    ( ! [X2,X1] : (k5_lattices(X1) = k15_lattice3(X1,X2) | v2_struct_0(X1) | ~v13_lattices(X1) | ~l3_lattices(X1) | ~r4_lattice3(X1,k5_lattices(X1),X2) | ~m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) | ~v4_lattice3(X1) | ~v10_lattices(X1)) )),
% 1.63/0.59    inference(subsumption_resolution,[],[f356,f127])).
% 1.63/0.59  fof(f127,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | k15_lattice3(X0,X1) = X2 | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(duplicate_literal_removal,[],[f102])).
% 1.63/0.59  fof(f102,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f61])).
% 1.63/0.59  fof(f61,plain,(
% 1.63/0.59    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK6(X0,X1,X2)) & r4_lattice3(X0,sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f59,f60])).
% 1.63/0.59  fof(f60,plain,(
% 1.63/0.59    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK6(X0,X1,X2)) & r4_lattice3(X0,sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f59,plain,(
% 1.63/0.59    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(rectify,[],[f58])).
% 1.63/0.59  fof(f58,plain,(
% 1.63/0.59    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(flattening,[],[f57])).
% 1.63/0.59  fof(f57,plain,(
% 1.63/0.59    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(nnf_transformation,[],[f35])).
% 1.63/0.59  fof(f35,plain,(
% 1.63/0.59    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(flattening,[],[f34])).
% 1.63/0.59  fof(f34,plain,(
% 1.63/0.59    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.63/0.59    inference(ennf_transformation,[],[f11])).
% 1.63/0.59  fof(f11,axiom,(
% 1.63/0.59    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 1.63/0.59  fof(f356,plain,(
% 1.63/0.59    ( ! [X2,X1] : (~m1_subset_1(sK6(X1,X2,k5_lattices(X1)),u1_struct_0(X1)) | ~l3_lattices(X1) | v2_struct_0(X1) | ~v13_lattices(X1) | k5_lattices(X1) = k15_lattice3(X1,X2) | ~r4_lattice3(X1,k5_lattices(X1),X2) | ~m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) | ~v4_lattice3(X1) | ~v10_lattices(X1)) )),
% 1.63/0.59    inference(subsumption_resolution,[],[f355,f82])).
% 1.63/0.59  fof(f355,plain,(
% 1.63/0.59    ( ! [X2,X1] : (~m1_subset_1(sK6(X1,X2,k5_lattices(X1)),u1_struct_0(X1)) | ~l3_lattices(X1) | ~v8_lattices(X1) | v2_struct_0(X1) | ~v13_lattices(X1) | k5_lattices(X1) = k15_lattice3(X1,X2) | ~r4_lattice3(X1,k5_lattices(X1),X2) | ~m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) | ~v4_lattice3(X1) | ~v10_lattices(X1)) )),
% 1.63/0.59    inference(subsumption_resolution,[],[f352,f83])).
% 1.63/0.59  fof(f352,plain,(
% 1.63/0.59    ( ! [X2,X1] : (~m1_subset_1(sK6(X1,X2,k5_lattices(X1)),u1_struct_0(X1)) | ~l3_lattices(X1) | ~v9_lattices(X1) | ~v8_lattices(X1) | v2_struct_0(X1) | ~v13_lattices(X1) | k5_lattices(X1) = k15_lattice3(X1,X2) | ~r4_lattice3(X1,k5_lattices(X1),X2) | ~m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) | ~v4_lattice3(X1) | ~v10_lattices(X1)) )),
% 1.63/0.59    inference(duplicate_literal_removal,[],[f351])).
% 1.63/0.59  fof(f351,plain,(
% 1.63/0.59    ( ! [X2,X1] : (~m1_subset_1(sK6(X1,X2,k5_lattices(X1)),u1_struct_0(X1)) | ~l3_lattices(X1) | ~v9_lattices(X1) | ~v8_lattices(X1) | v2_struct_0(X1) | ~v13_lattices(X1) | k5_lattices(X1) = k15_lattice3(X1,X2) | ~r4_lattice3(X1,k5_lattices(X1),X2) | ~m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.63/0.59    inference(resolution,[],[f311,f129])).
% 1.63/0.59  fof(f129,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (~r1_lattices(X0,X2,sK6(X0,X1,X2)) | k15_lattice3(X0,X1) = X2 | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(duplicate_literal_removal,[],[f104])).
% 1.63/0.59  fof(f104,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | ~r1_lattices(X0,X2,sK6(X0,X1,X2)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f61])).
% 1.63/0.59  fof(f311,plain,(
% 1.63/0.59    ( ! [X15,X16] : (r1_lattices(X15,k5_lattices(X15),X16) | ~m1_subset_1(X16,u1_struct_0(X15)) | ~l3_lattices(X15) | ~v9_lattices(X15) | ~v8_lattices(X15) | v2_struct_0(X15) | ~v13_lattices(X15)) )),
% 1.63/0.59    inference(global_subsumption,[],[f79,f86,f310])).
% 1.63/0.59  fof(f310,plain,(
% 1.63/0.59    ( ! [X15,X16] : (r1_lattices(X15,k5_lattices(X15),X16) | ~m1_subset_1(X16,u1_struct_0(X15)) | ~m1_subset_1(k5_lattices(X15),u1_struct_0(X15)) | ~l3_lattices(X15) | ~v9_lattices(X15) | ~v8_lattices(X15) | v2_struct_0(X15) | ~v13_lattices(X15)) )),
% 1.63/0.59    inference(subsumption_resolution,[],[f295,f79])).
% 1.63/0.59  fof(f295,plain,(
% 1.63/0.59    ( ! [X15,X16] : (r1_lattices(X15,k5_lattices(X15),X16) | ~m1_subset_1(X16,u1_struct_0(X15)) | ~m1_subset_1(k5_lattices(X15),u1_struct_0(X15)) | ~l3_lattices(X15) | ~v9_lattices(X15) | ~v8_lattices(X15) | v2_struct_0(X15) | ~v13_lattices(X15) | ~l1_lattices(X15)) )),
% 1.63/0.59    inference(trivial_inequality_removal,[],[f294])).
% 1.63/0.59  fof(f294,plain,(
% 1.63/0.59    ( ! [X15,X16] : (k5_lattices(X15) != k5_lattices(X15) | r1_lattices(X15,k5_lattices(X15),X16) | ~m1_subset_1(X16,u1_struct_0(X15)) | ~m1_subset_1(k5_lattices(X15),u1_struct_0(X15)) | ~l3_lattices(X15) | ~v9_lattices(X15) | ~v8_lattices(X15) | v2_struct_0(X15) | ~v13_lattices(X15) | ~l1_lattices(X15)) )),
% 1.63/0.59    inference(duplicate_literal_removal,[],[f293])).
% 1.63/0.59  fof(f293,plain,(
% 1.63/0.59    ( ! [X15,X16] : (k5_lattices(X15) != k5_lattices(X15) | r1_lattices(X15,k5_lattices(X15),X16) | ~m1_subset_1(X16,u1_struct_0(X15)) | ~m1_subset_1(k5_lattices(X15),u1_struct_0(X15)) | ~l3_lattices(X15) | ~v9_lattices(X15) | ~v8_lattices(X15) | v2_struct_0(X15) | ~m1_subset_1(X16,u1_struct_0(X15)) | ~v13_lattices(X15) | ~l1_lattices(X15) | v2_struct_0(X15)) )),
% 1.63/0.59    inference(superposition,[],[f85,f147])).
% 1.63/0.59  fof(f147,plain,(
% 1.63/0.59    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(subsumption_resolution,[],[f120,f86])).
% 1.63/0.59  fof(f120,plain,(
% 1.63/0.59    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(equality_resolution,[],[f87])).
% 1.63/0.59  fof(f87,plain,(
% 1.63/0.59    ( ! [X0,X3,X1] : (k2_lattices(X0,X1,X3) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f46])).
% 1.63/0.59  fof(f46,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).
% 1.63/0.59  fof(f45,plain,(
% 1.63/0.59    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f44,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(rectify,[],[f43])).
% 1.63/0.59  fof(f43,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(nnf_transformation,[],[f29])).
% 1.63/0.59  fof(f29,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(flattening,[],[f28])).
% 1.63/0.59  fof(f28,plain,(
% 1.63/0.59    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.63/0.59    inference(ennf_transformation,[],[f4])).
% 1.63/0.59  % (19193)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.63/0.59  fof(f4,axiom,(
% 1.63/0.59    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 1.63/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).
% 1.63/0.59  fof(f85,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) != X1 | r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f42])).
% 1.63/0.59  fof(f144,plain,(
% 1.63/0.59    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl11_5),
% 1.63/0.59    inference(avatar_component_clause,[],[f143])).
% 1.63/0.59  fof(f967,plain,(
% 1.63/0.59    spl11_4),
% 1.63/0.59    inference(avatar_contradiction_clause,[],[f966])).
% 1.63/0.59  fof(f966,plain,(
% 1.63/0.59    $false | spl11_4),
% 1.63/0.59    inference(subsumption_resolution,[],[f141,f77])).
% 1.63/0.59  fof(f141,plain,(
% 1.63/0.59    ~l3_lattices(sK0) | spl11_4),
% 1.63/0.59    inference(avatar_component_clause,[],[f140])).
% 1.63/0.59  fof(f140,plain,(
% 1.63/0.59    spl11_4 <=> l3_lattices(sK0)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.63/0.59  fof(f965,plain,(
% 1.63/0.59    spl11_3),
% 1.63/0.59    inference(avatar_contradiction_clause,[],[f964])).
% 1.63/0.59  fof(f964,plain,(
% 1.63/0.59    $false | spl11_3),
% 1.63/0.59    inference(subsumption_resolution,[],[f963,f138])).
% 1.63/0.59  fof(f138,plain,(
% 1.63/0.59    ~v13_lattices(sK0) | spl11_3),
% 1.63/0.59    inference(avatar_component_clause,[],[f137])).
% 1.63/0.59  fof(f137,plain,(
% 1.63/0.59    spl11_3 <=> v13_lattices(sK0)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.63/0.59  fof(f149,plain,(
% 1.63/0.59    spl11_2),
% 1.63/0.59    inference(avatar_contradiction_clause,[],[f148])).
% 1.63/0.59  fof(f148,plain,(
% 1.63/0.59    $false | spl11_2),
% 1.63/0.59    inference(subsumption_resolution,[],[f135,f75])).
% 1.63/0.59  fof(f135,plain,(
% 1.63/0.59    ~v10_lattices(sK0) | spl11_2),
% 1.63/0.59    inference(avatar_component_clause,[],[f134])).
% 1.63/0.59  fof(f134,plain,(
% 1.63/0.59    spl11_2 <=> v10_lattices(sK0)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.63/0.59  fof(f145,plain,(
% 1.63/0.59    spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_5),
% 1.63/0.59    inference(avatar_split_clause,[],[f78,f143,f140,f137,f134,f131])).
% 1.63/0.59  fof(f78,plain,(
% 1.63/0.59    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 1.63/0.59    inference(cnf_transformation,[],[f41])).
% 1.63/0.59  % SZS output end Proof for theBenchmark
% 1.63/0.59  % (19184)------------------------------
% 1.63/0.59  % (19184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.59  % (19184)Termination reason: Refutation
% 1.63/0.59  
% 1.63/0.59  % (19184)Memory used [KB]: 11001
% 1.63/0.59  % (19184)Time elapsed: 0.140 s
% 1.63/0.59  % (19184)------------------------------
% 1.63/0.59  % (19184)------------------------------
% 1.63/0.59  % (19181)Success in time 0.232 s
%------------------------------------------------------------------------------
