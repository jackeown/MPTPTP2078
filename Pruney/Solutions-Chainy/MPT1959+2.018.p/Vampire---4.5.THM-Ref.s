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
% DateTime   : Thu Dec  3 13:22:52 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 482 expanded)
%              Number of leaves         :   41 ( 163 expanded)
%              Depth                    :   20
%              Number of atoms          :  901 (2537 expanded)
%              Number of equality atoms :   46 ( 117 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1065,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f125,f130,f135,f140,f145,f150,f155,f165,f167,f201,f248,f253,f296,f315,f335,f368,f612,f622,f1060])).

fof(f1060,plain,
    ( ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | spl9_14
    | ~ spl9_18
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(avatar_contradiction_clause,[],[f1059])).

fof(f1059,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | spl9_14
    | ~ spl9_18
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(subsumption_resolution,[],[f1050,f630])).

fof(f630,plain,
    ( ~ r2_hidden(sK8(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)
    | ~ spl9_8
    | spl9_14
    | ~ spl9_30 ),
    inference(unit_resulting_resolution,[],[f251,f154,f362,f621,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1,X2),X2)
      | X1 = X2
      | ~ r2_hidden(sK8(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK8(X0,X1,X2),X2)
              | ~ r2_hidden(sK8(X0,X1,X2),X1) )
            & ( r2_hidden(sK8(X0,X1,X2),X2)
              | r2_hidden(sK8(X0,X1,X2),X1) )
            & m1_subset_1(sK8(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f68,f69])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK8(X0,X1,X2),X2)
          | ~ r2_hidden(sK8(X0,X1,X2),X1) )
        & ( r2_hidden(sK8(X0,X1,X2),X2)
          | r2_hidden(sK8(X0,X1,X2),X1) )
        & m1_subset_1(sK8(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

fof(f621,plain,
    ( r2_hidden(sK8(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f619])).

fof(f619,plain,
    ( spl9_30
  <=> r2_hidden(sK8(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f362,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f100,f185])).

fof(f185,plain,(
    ! [X0] : sK7(X0) = X0 ),
    inference(unit_resulting_resolution,[],[f101,f100,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f101,plain,(
    ! [X0] : ~ v1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK7(X0),X0)
      & m1_subset_1(sK7(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f5,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK7(X0),X0)
        & m1_subset_1(sK7(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f100,plain,(
    ! [X0] : m1_subset_1(sK7(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

fof(f154,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl9_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f251,plain,
    ( u1_struct_0(sK0) != sK1
    | spl9_14 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl9_14
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f1050,plain,
    ( r2_hidden(sK8(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_18
    | ~ spl9_28 ),
    inference(resolution,[],[f697,f611])).

fof(f611,plain,
    ( m1_subset_1(sK8(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f609])).

fof(f609,plain,
    ( spl9_28
  <=> m1_subset_1(sK8(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f697,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f696,f404])).

fof(f404,plain,
    ( ! [X8] :
        ( r2_lattice3(sK0,k1_xboole_0,X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(resolution,[],[f204,f156])).

fof(f156,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl9_7 ),
    inference(unit_resulting_resolution,[],[f149,f98])).

fof(f98,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f61,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f149,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl9_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f204,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl9_4 ),
    inference(resolution,[],[f95,f134])).

fof(f134,plain,
    ( l1_orders_2(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl9_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f57,f58])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f696,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ r2_lattice3(sK0,k1_xboole_0,X0) )
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f695,f163])).

fof(f163,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl9_10
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f695,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | r2_hidden(X0,sK1)
        | ~ r2_lattice3(sK0,k1_xboole_0,X0) )
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_18 ),
    inference(duplicate_literal_removal,[],[f691])).

fof(f691,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | r2_hidden(X0,sK1)
        | ~ r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_18 ),
    inference(resolution,[],[f446,f330])).

fof(f330,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_4
    | ~ spl9_12
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f329,f134])).

fof(f329,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_12
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f323,f200])).

fof(f200,plain,
    ( r1_yellow_0(sK0,k1_xboole_0)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl9_12
  <=> r1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f323,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,k1_xboole_0)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_18 ),
    inference(superposition,[],[f115,f314])).

fof(f314,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl9_18
  <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f115,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f111,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
                & r2_lattice3(X0,X1,sK4(X0,X1,X2))
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f53,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_lattice3(X0,X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f446,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1) )
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f445,f154])).

fof(f445,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,sK1) )
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(resolution,[],[f232,f144])).

fof(f144,plain,
    ( v13_waybel_0(sK1,sK0)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl9_6
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f232,plain,
    ( ! [X2,X0,X1] :
        ( ~ v13_waybel_0(X2,sK0)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) )
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f231,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f231,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) )
    | ~ spl9_4 ),
    inference(resolution,[],[f82,f134])).

fof(f82,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f47,f49,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X2,X3)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,sK2(X0,X1),X3)
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,sK2(X0,X1),X3)
          & r2_hidden(sK2(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f622,plain,
    ( spl9_30
    | ~ spl9_8
    | spl9_14 ),
    inference(avatar_split_clause,[],[f434,f250,f152,f619])).

fof(f434,plain,
    ( r2_hidden(sK8(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl9_8
    | spl9_14 ),
    inference(unit_resulting_resolution,[],[f251,f154,f227])).

fof(f227,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | r2_hidden(sK8(X1,X1,X2),X1)
      | X1 = X2 ) ),
    inference(forward_demodulation,[],[f226,f185])).

fof(f226,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK8(X1,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | sK7(X1) = X2 ) ),
    inference(subsumption_resolution,[],[f225,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f225,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK8(X1,X1,X2),X1)
      | r2_hidden(sK8(X1,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | sK7(X1) = X2 ) ),
    inference(forward_demodulation,[],[f224,f185])).

fof(f224,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK8(X1,X1,X2),X2)
      | r2_hidden(sK8(X1,sK7(X1),X2),sK7(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | sK7(X1) = X2 ) ),
    inference(forward_demodulation,[],[f219,f185])).

fof(f219,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK8(X1,sK7(X1),X2),X2)
      | r2_hidden(sK8(X1,sK7(X1),X2),sK7(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | sK7(X1) = X2 ) ),
    inference(resolution,[],[f108,f100])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(sK8(X0,X1,X2),X2)
      | r2_hidden(sK8(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f612,plain,
    ( spl9_28
    | ~ spl9_8
    | spl9_14 ),
    inference(avatar_split_clause,[],[f431,f250,f152,f609])).

fof(f431,plain,
    ( m1_subset_1(sK8(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl9_8
    | spl9_14 ),
    inference(unit_resulting_resolution,[],[f251,f154,f212])).

fof(f212,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | m1_subset_1(sK8(X1,X1,X2),X1)
      | X1 = X2 ) ),
    inference(forward_demodulation,[],[f211,f185])).

fof(f211,plain,(
    ! [X2,X1] :
      ( m1_subset_1(sK8(X1,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | sK7(X1) = X2 ) ),
    inference(forward_demodulation,[],[f208,f185])).

fof(f208,plain,(
    ! [X2,X1] :
      ( m1_subset_1(sK8(X1,sK7(X1),X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | sK7(X1) = X2 ) ),
    inference(resolution,[],[f107,f100])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK8(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f368,plain,(
    ~ spl9_17 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f295,f364])).

fof(f364,plain,(
    ! [X1] : ~ v1_subset_1(X1,X1) ),
    inference(subsumption_resolution,[],[f113,f362])).

fof(f113,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f295,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl9_17
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f335,plain,
    ( ~ spl9_4
    | spl9_13
    | ~ spl9_14
    | ~ spl9_18 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | ~ spl9_4
    | spl9_13
    | ~ spl9_14
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f333,f247])).

fof(f247,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),sK1)
    | spl9_13 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl9_13
  <=> m1_subset_1(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f333,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ spl9_4
    | ~ spl9_14
    | ~ spl9_18 ),
    inference(forward_demodulation,[],[f332,f252])).

fof(f252,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f250])).

fof(f332,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl9_4
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f325,f134])).

fof(f325,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_18 ),
    inference(superposition,[],[f102,f314])).

fof(f315,plain,
    ( spl9_18
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f172,f132,f312])).

fof(f172,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f134,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f296,plain,
    ( spl9_17
    | ~ spl9_9
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f280,f250,f158,f293])).

fof(f158,plain,
    ( spl9_9
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f280,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl9_9
    | ~ spl9_14 ),
    inference(superposition,[],[f160,f252])).

fof(f160,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f158])).

fof(f253,plain,
    ( spl9_14
    | ~ spl9_8
    | spl9_9 ),
    inference(avatar_split_clause,[],[f184,f158,f152,f250])).

fof(f184,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl9_8
    | spl9_9 ),
    inference(unit_resulting_resolution,[],[f159,f154,f105])).

fof(f159,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl9_9 ),
    inference(avatar_component_clause,[],[f158])).

fof(f248,plain,
    ( ~ spl9_13
    | spl9_5
    | spl9_10 ),
    inference(avatar_split_clause,[],[f180,f162,f137,f245])).

fof(f137,plain,
    ( spl9_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f180,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),sK1)
    | spl9_5
    | spl9_10 ),
    inference(unit_resulting_resolution,[],[f164,f139,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f139,plain,
    ( ~ v1_xboole_0(sK1)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f137])).

fof(f164,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | spl9_10 ),
    inference(avatar_component_clause,[],[f162])).

fof(f201,plain,
    ( spl9_12
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f194,f132,f127,f122,f117,f198])).

fof(f117,plain,
    ( spl9_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f122,plain,
    ( spl9_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f127,plain,
    ( spl9_3
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f194,plain,
    ( r1_yellow_0(sK0,k1_xboole_0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f119,f124,f129,f134,f97])).

fof(f97,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f129,plain,
    ( v1_yellow_0(sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f124,plain,
    ( v5_orders_2(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f119,plain,
    ( ~ v2_struct_0(sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f167,plain,
    ( ~ spl9_9
    | spl9_10 ),
    inference(avatar_split_clause,[],[f166,f162,f158])).

fof(f166,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl9_10 ),
    inference(subsumption_resolution,[],[f79,f164])).

fof(f79,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
    & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | v1_subset_1(sK1,u1_struct_0(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v13_waybel_0(sK1,sK0)
    & ~ v1_xboole_0(sK1)
    & l1_orders_2(sK0)
    & v1_yellow_0(sK0)
    & v5_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
          & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
            | v1_subset_1(X1,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v13_waybel_0(X1,sK0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK0)
      & v1_yellow_0(sK0)
      & v5_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( ( r2_hidden(k3_yellow_0(sK0),X1)
          | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
        & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
          | v1_subset_1(X1,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v13_waybel_0(X1,sK0)
        & ~ v1_xboole_0(X1) )
   => ( ( r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
      & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | v1_subset_1(sK1,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v13_waybel_0(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f165,plain,
    ( spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f78,f162,f158])).

fof(f78,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f155,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f77,f152])).

fof(f77,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f150,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f80,f147])).

fof(f80,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f145,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f76,f142])).

fof(f76,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f140,plain,(
    ~ spl9_5 ),
    inference(avatar_split_clause,[],[f75,f137])).

fof(f75,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f135,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f74,f132])).

fof(f74,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f130,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f73,f127])).

fof(f73,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f125,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f72,f122])).

fof(f72,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f120,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f71,f117])).

fof(f71,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (2071)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.47  % (2063)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.47  % (2079)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.48  % (2056)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.48  % (2063)Refutation not found, incomplete strategy% (2063)------------------------------
% 0.20/0.48  % (2063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (2063)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (2063)Memory used [KB]: 1791
% 0.20/0.48  % (2063)Time elapsed: 0.073 s
% 0.20/0.48  % (2063)------------------------------
% 0.20/0.48  % (2063)------------------------------
% 0.20/0.48  % (2066)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.48  % (2067)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.49  % (2058)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (2059)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (2064)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.49  % (2056)Refutation not found, incomplete strategy% (2056)------------------------------
% 0.20/0.49  % (2056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (2056)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (2056)Memory used [KB]: 10746
% 0.20/0.49  % (2056)Time elapsed: 0.081 s
% 0.20/0.49  % (2056)------------------------------
% 0.20/0.49  % (2056)------------------------------
% 0.20/0.49  % (2076)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % (2061)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (2075)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (2074)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (2062)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (2081)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.50  % (2070)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (2069)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (2057)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (2068)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (2073)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (2060)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (2077)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (2080)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (2072)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (2062)Refutation not found, incomplete strategy% (2062)------------------------------
% 0.20/0.52  % (2062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2062)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (2062)Memory used [KB]: 10618
% 0.20/0.52  % (2062)Time elapsed: 0.129 s
% 0.20/0.52  % (2062)------------------------------
% 0.20/0.52  % (2062)------------------------------
% 1.36/0.53  % (2065)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.36/0.53  % (2078)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.36/0.54  % (2079)Refutation found. Thanks to Tanya!
% 1.36/0.54  % SZS status Theorem for theBenchmark
% 1.36/0.54  % SZS output start Proof for theBenchmark
% 1.36/0.54  fof(f1065,plain,(
% 1.36/0.54    $false),
% 1.36/0.54    inference(avatar_sat_refutation,[],[f120,f125,f130,f135,f140,f145,f150,f155,f165,f167,f201,f248,f253,f296,f315,f335,f368,f612,f622,f1060])).
% 1.36/0.54  fof(f1060,plain,(
% 1.36/0.54    ~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_10 | ~spl9_12 | spl9_14 | ~spl9_18 | ~spl9_28 | ~spl9_30),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f1059])).
% 1.36/0.54  fof(f1059,plain,(
% 1.36/0.54    $false | (~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_10 | ~spl9_12 | spl9_14 | ~spl9_18 | ~spl9_28 | ~spl9_30)),
% 1.36/0.54    inference(subsumption_resolution,[],[f1050,f630])).
% 1.36/0.54  fof(f630,plain,(
% 1.36/0.54    ~r2_hidden(sK8(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) | (~spl9_8 | spl9_14 | ~spl9_30)),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f251,f154,f362,f621,f109])).
% 1.36/0.54  fof(f109,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK8(X0,X1,X2),X2) | X1 = X2 | ~r2_hidden(sK8(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f70])).
% 1.36/0.54  fof(f70,plain,(
% 1.36/0.54    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK8(X0,X1,X2),X2) | ~r2_hidden(sK8(X0,X1,X2),X1)) & (r2_hidden(sK8(X0,X1,X2),X2) | r2_hidden(sK8(X0,X1,X2),X1)) & m1_subset_1(sK8(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f68,f69])).
% 1.36/0.54  fof(f69,plain,(
% 1.36/0.54    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK8(X0,X1,X2),X2) | ~r2_hidden(sK8(X0,X1,X2),X1)) & (r2_hidden(sK8(X0,X1,X2),X2) | r2_hidden(sK8(X0,X1,X2),X1)) & m1_subset_1(sK8(X0,X1,X2),X0)))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f68,plain,(
% 1.36/0.54    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.54    inference(flattening,[],[f67])).
% 1.36/0.54  fof(f67,plain,(
% 1.36/0.54    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.54    inference(nnf_transformation,[],[f38])).
% 1.36/0.54  fof(f38,plain,(
% 1.36/0.54    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.54    inference(flattening,[],[f37])).
% 1.36/0.54  fof(f37,plain,(
% 1.36/0.54    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.54    inference(ennf_transformation,[],[f4])).
% 1.36/0.54  fof(f4,axiom,(
% 1.36/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).
% 1.36/0.54  fof(f621,plain,(
% 1.36/0.54    r2_hidden(sK8(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl9_30),
% 1.36/0.54    inference(avatar_component_clause,[],[f619])).
% 1.36/0.54  fof(f619,plain,(
% 1.36/0.54    spl9_30 <=> r2_hidden(sK8(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 1.36/0.54  fof(f362,plain,(
% 1.36/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.36/0.54    inference(superposition,[],[f100,f185])).
% 1.36/0.54  fof(f185,plain,(
% 1.36/0.54    ( ! [X0] : (sK7(X0) = X0) )),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f101,f100,f105])).
% 1.36/0.54  fof(f105,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f66])).
% 1.36/0.54  fof(f66,plain,(
% 1.36/0.54    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.54    inference(nnf_transformation,[],[f35])).
% 1.36/0.54  fof(f35,plain,(
% 1.36/0.54    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.54    inference(ennf_transformation,[],[f14])).
% 1.36/0.54  fof(f14,axiom,(
% 1.36/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 1.36/0.54  fof(f101,plain,(
% 1.36/0.54    ( ! [X0] : (~v1_subset_1(sK7(X0),X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f65])).
% 1.36/0.54  fof(f65,plain,(
% 1.36/0.54    ! [X0] : (~v1_subset_1(sK7(X0),X0) & m1_subset_1(sK7(X0),k1_zfmisc_1(X0)))),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f5,f64])).
% 1.36/0.54  fof(f64,plain,(
% 1.36/0.54    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK7(X0),X0) & m1_subset_1(sK7(X0),k1_zfmisc_1(X0))))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f5,axiom,(
% 1.36/0.54    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).
% 1.36/0.54  fof(f100,plain,(
% 1.36/0.54    ( ! [X0] : (m1_subset_1(sK7(X0),k1_zfmisc_1(X0))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f65])).
% 1.36/0.54  fof(f154,plain,(
% 1.36/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl9_8),
% 1.36/0.54    inference(avatar_component_clause,[],[f152])).
% 1.36/0.54  fof(f152,plain,(
% 1.36/0.54    spl9_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 1.36/0.54  fof(f251,plain,(
% 1.36/0.54    u1_struct_0(sK0) != sK1 | spl9_14),
% 1.36/0.54    inference(avatar_component_clause,[],[f250])).
% 1.36/0.54  fof(f250,plain,(
% 1.36/0.54    spl9_14 <=> u1_struct_0(sK0) = sK1),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 1.36/0.54  fof(f1050,plain,(
% 1.36/0.54    r2_hidden(sK8(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) | (~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_10 | ~spl9_12 | ~spl9_18 | ~spl9_28)),
% 1.36/0.54    inference(resolution,[],[f697,f611])).
% 1.36/0.54  fof(f611,plain,(
% 1.36/0.54    m1_subset_1(sK8(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl9_28),
% 1.36/0.54    inference(avatar_component_clause,[],[f609])).
% 1.36/0.54  fof(f609,plain,(
% 1.36/0.54    spl9_28 <=> m1_subset_1(sK8(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 1.36/0.54  fof(f697,plain,(
% 1.36/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1)) ) | (~spl9_4 | ~spl9_6 | ~spl9_7 | ~spl9_8 | ~spl9_10 | ~spl9_12 | ~spl9_18)),
% 1.36/0.54    inference(subsumption_resolution,[],[f696,f404])).
% 1.36/0.54  fof(f404,plain,(
% 1.36/0.54    ( ! [X8] : (r2_lattice3(sK0,k1_xboole_0,X8) | ~m1_subset_1(X8,u1_struct_0(sK0))) ) | (~spl9_4 | ~spl9_7)),
% 1.36/0.54    inference(resolution,[],[f204,f156])).
% 1.36/0.54  fof(f156,plain,(
% 1.36/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl9_7),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f149,f98])).
% 1.36/0.54  fof(f98,plain,(
% 1.36/0.54    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f63])).
% 1.36/0.54  fof(f63,plain,(
% 1.36/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f61,f62])).
% 1.36/0.54  fof(f62,plain,(
% 1.36/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f61,plain,(
% 1.36/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.36/0.54    inference(rectify,[],[f60])).
% 1.36/0.54  fof(f60,plain,(
% 1.36/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.36/0.54    inference(nnf_transformation,[],[f1])).
% 1.36/0.54  fof(f1,axiom,(
% 1.36/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.36/0.54  fof(f149,plain,(
% 1.36/0.54    v1_xboole_0(k1_xboole_0) | ~spl9_7),
% 1.36/0.54    inference(avatar_component_clause,[],[f147])).
% 1.36/0.54  fof(f147,plain,(
% 1.36/0.54    spl9_7 <=> v1_xboole_0(k1_xboole_0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 1.36/0.54  fof(f204,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r2_hidden(sK5(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)) ) | ~spl9_4),
% 1.36/0.54    inference(resolution,[],[f95,f134])).
% 1.36/0.54  fof(f134,plain,(
% 1.36/0.54    l1_orders_2(sK0) | ~spl9_4),
% 1.36/0.54    inference(avatar_component_clause,[],[f132])).
% 1.36/0.54  fof(f132,plain,(
% 1.36/0.54    spl9_4 <=> l1_orders_2(sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.36/0.54  fof(f95,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f59])).
% 1.36/0.54  fof(f59,plain,(
% 1.36/0.54    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f57,f58])).
% 1.36/0.54  fof(f58,plain,(
% 1.36/0.54    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f57,plain,(
% 1.36/0.54    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.36/0.54    inference(rectify,[],[f56])).
% 1.36/0.54  fof(f56,plain,(
% 1.36/0.54    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.36/0.54    inference(nnf_transformation,[],[f29])).
% 1.36/0.54  fof(f29,plain,(
% 1.36/0.54    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.36/0.54    inference(flattening,[],[f28])).
% 1.36/0.54  fof(f28,plain,(
% 1.36/0.54    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f8])).
% 1.36/0.54  fof(f8,axiom,(
% 1.36/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 1.36/0.54  fof(f696,plain,(
% 1.36/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1) | ~r2_lattice3(sK0,k1_xboole_0,X0)) ) | (~spl9_4 | ~spl9_6 | ~spl9_8 | ~spl9_10 | ~spl9_12 | ~spl9_18)),
% 1.36/0.54    inference(subsumption_resolution,[],[f695,f163])).
% 1.36/0.54  fof(f163,plain,(
% 1.36/0.54    r2_hidden(k3_yellow_0(sK0),sK1) | ~spl9_10),
% 1.36/0.54    inference(avatar_component_clause,[],[f162])).
% 1.36/0.54  fof(f162,plain,(
% 1.36/0.54    spl9_10 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.36/0.54  fof(f695,plain,(
% 1.36/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(X0,sK1) | ~r2_lattice3(sK0,k1_xboole_0,X0)) ) | (~spl9_4 | ~spl9_6 | ~spl9_8 | ~spl9_12 | ~spl9_18)),
% 1.36/0.54    inference(duplicate_literal_removal,[],[f691])).
% 1.36/0.54  fof(f691,plain,(
% 1.36/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(X0,sK1) | ~r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_4 | ~spl9_6 | ~spl9_8 | ~spl9_12 | ~spl9_18)),
% 1.36/0.54    inference(resolution,[],[f446,f330])).
% 1.36/0.54  fof(f330,plain,(
% 1.36/0.54    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_4 | ~spl9_12 | ~spl9_18)),
% 1.36/0.54    inference(subsumption_resolution,[],[f329,f134])).
% 1.36/0.54  fof(f329,plain,(
% 1.36/0.54    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | (~spl9_12 | ~spl9_18)),
% 1.36/0.54    inference(subsumption_resolution,[],[f323,f200])).
% 1.36/0.54  fof(f200,plain,(
% 1.36/0.54    r1_yellow_0(sK0,k1_xboole_0) | ~spl9_12),
% 1.36/0.54    inference(avatar_component_clause,[],[f198])).
% 1.36/0.54  fof(f198,plain,(
% 1.36/0.54    spl9_12 <=> r1_yellow_0(sK0,k1_xboole_0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 1.36/0.54  fof(f323,plain,(
% 1.36/0.54    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_yellow_0(sK0,k1_xboole_0) | ~l1_orders_2(sK0)) ) | ~spl9_18),
% 1.36/0.54    inference(superposition,[],[f115,f314])).
% 1.36/0.54  fof(f314,plain,(
% 1.36/0.54    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) | ~spl9_18),
% 1.36/0.54    inference(avatar_component_clause,[],[f312])).
% 1.36/0.54  fof(f312,plain,(
% 1.36/0.54    spl9_18 <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 1.36/0.54  fof(f115,plain,(
% 1.36/0.54    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0)) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f111,f102])).
% 1.36/0.54  fof(f102,plain,(
% 1.36/0.54    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f32])).
% 1.36/0.54  fof(f32,plain,(
% 1.36/0.54    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f11])).
% 1.36/0.54  fof(f11,axiom,(
% 1.36/0.54    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 1.36/0.54  fof(f111,plain,(
% 1.36/0.54    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.36/0.54    inference(equality_resolution,[],[f89])).
% 1.36/0.54  fof(f89,plain,(
% 1.36/0.54    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f55])).
% 1.36/0.54  fof(f55,plain,(
% 1.36/0.54    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_lattice3(X0,X1,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f53,f54])).
% 1.36/0.54  fof(f54,plain,(
% 1.36/0.54    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_lattice3(X0,X1,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f53,plain,(
% 1.36/0.54    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.36/0.54    inference(rectify,[],[f52])).
% 1.36/0.54  fof(f52,plain,(
% 1.36/0.54    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.36/0.54    inference(flattening,[],[f51])).
% 1.36/0.54  fof(f51,plain,(
% 1.36/0.54    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.36/0.54    inference(nnf_transformation,[],[f27])).
% 1.36/0.54  fof(f27,plain,(
% 1.36/0.54    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.36/0.54    inference(flattening,[],[f26])).
% 1.36/0.54  fof(f26,plain,(
% 1.36/0.54    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f10])).
% 1.36/0.54  fof(f10,axiom,(
% 1.36/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).
% 1.36/0.54  fof(f446,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | r2_hidden(X1,sK1)) ) | (~spl9_4 | ~spl9_6 | ~spl9_8)),
% 1.36/0.54    inference(subsumption_resolution,[],[f445,f154])).
% 1.36/0.54  fof(f445,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,sK1)) ) | (~spl9_4 | ~spl9_6)),
% 1.36/0.54    inference(resolution,[],[f232,f144])).
% 1.36/0.54  fof(f144,plain,(
% 1.36/0.54    v13_waybel_0(sK1,sK0) | ~spl9_6),
% 1.36/0.54    inference(avatar_component_clause,[],[f142])).
% 1.36/0.54  fof(f142,plain,(
% 1.36/0.54    spl9_6 <=> v13_waybel_0(sK1,sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.36/0.54  fof(f232,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~v13_waybel_0(X2,sK0) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2)) ) | ~spl9_4),
% 1.36/0.54    inference(subsumption_resolution,[],[f231,f110])).
% 1.36/0.54  fof(f110,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f40])).
% 1.36/0.54  fof(f40,plain,(
% 1.36/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.36/0.54    inference(flattening,[],[f39])).
% 1.36/0.54  fof(f39,plain,(
% 1.36/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.36/0.54    inference(ennf_transformation,[],[f7])).
% 1.36/0.54  fof(f7,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.36/0.54  fof(f231,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v13_waybel_0(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2)) ) | ~spl9_4),
% 1.36/0.54    inference(resolution,[],[f82,f134])).
% 1.36/0.54  fof(f82,plain,(
% 1.36/0.54    ( ! [X4,X0,X5,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X5,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f50])).
% 1.36/0.54  fof(f50,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f47,f49,f48])).
% 1.36/0.54  fof(f48,plain,(
% 1.36/0.54    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f49,plain,(
% 1.36/0.54    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f47,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.36/0.54    inference(rectify,[],[f46])).
% 1.36/0.54  fof(f46,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.36/0.54    inference(nnf_transformation,[],[f25])).
% 1.36/0.54  fof(f25,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.36/0.54    inference(flattening,[],[f24])).
% 1.36/0.54  fof(f24,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f13])).
% 1.36/0.54  fof(f13,axiom,(
% 1.36/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).
% 1.36/0.54  fof(f622,plain,(
% 1.36/0.54    spl9_30 | ~spl9_8 | spl9_14),
% 1.36/0.54    inference(avatar_split_clause,[],[f434,f250,f152,f619])).
% 1.36/0.54  fof(f434,plain,(
% 1.36/0.54    r2_hidden(sK8(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl9_8 | spl9_14)),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f251,f154,f227])).
% 1.36/0.54  fof(f227,plain,(
% 1.36/0.54    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | r2_hidden(sK8(X1,X1,X2),X1) | X1 = X2) )),
% 1.36/0.54    inference(forward_demodulation,[],[f226,f185])).
% 1.36/0.54  fof(f226,plain,(
% 1.36/0.54    ( ! [X2,X1] : (r2_hidden(sK8(X1,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | sK7(X1) = X2) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f225,f106])).
% 1.36/0.54  fof(f106,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f36])).
% 1.36/0.54  fof(f36,plain,(
% 1.36/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.36/0.54    inference(ennf_transformation,[],[f3])).
% 1.36/0.54  fof(f3,axiom,(
% 1.36/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.36/0.54  fof(f225,plain,(
% 1.36/0.54    ( ! [X2,X1] : (r2_hidden(sK8(X1,X1,X2),X1) | r2_hidden(sK8(X1,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | sK7(X1) = X2) )),
% 1.36/0.54    inference(forward_demodulation,[],[f224,f185])).
% 1.36/0.54  fof(f224,plain,(
% 1.36/0.54    ( ! [X2,X1] : (r2_hidden(sK8(X1,X1,X2),X2) | r2_hidden(sK8(X1,sK7(X1),X2),sK7(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | sK7(X1) = X2) )),
% 1.36/0.54    inference(forward_demodulation,[],[f219,f185])).
% 1.36/0.54  fof(f219,plain,(
% 1.36/0.54    ( ! [X2,X1] : (r2_hidden(sK8(X1,sK7(X1),X2),X2) | r2_hidden(sK8(X1,sK7(X1),X2),sK7(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | sK7(X1) = X2) )),
% 1.36/0.54    inference(resolution,[],[f108,f100])).
% 1.36/0.54  fof(f108,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(sK8(X0,X1,X2),X2) | r2_hidden(sK8(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | X1 = X2) )),
% 1.36/0.54    inference(cnf_transformation,[],[f70])).
% 1.36/0.54  fof(f612,plain,(
% 1.36/0.54    spl9_28 | ~spl9_8 | spl9_14),
% 1.36/0.54    inference(avatar_split_clause,[],[f431,f250,f152,f609])).
% 1.36/0.54  fof(f431,plain,(
% 1.36/0.54    m1_subset_1(sK8(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl9_8 | spl9_14)),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f251,f154,f212])).
% 1.56/0.54  fof(f212,plain,(
% 1.56/0.54    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | m1_subset_1(sK8(X1,X1,X2),X1) | X1 = X2) )),
% 1.56/0.54    inference(forward_demodulation,[],[f211,f185])).
% 1.56/0.54  fof(f211,plain,(
% 1.56/0.54    ( ! [X2,X1] : (m1_subset_1(sK8(X1,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | sK7(X1) = X2) )),
% 1.56/0.54    inference(forward_demodulation,[],[f208,f185])).
% 1.56/0.54  fof(f208,plain,(
% 1.56/0.54    ( ! [X2,X1] : (m1_subset_1(sK8(X1,sK7(X1),X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | sK7(X1) = X2) )),
% 1.56/0.54    inference(resolution,[],[f107,f100])).
% 1.56/0.54  fof(f107,plain,(
% 1.56/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK8(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | X1 = X2) )),
% 1.56/0.54    inference(cnf_transformation,[],[f70])).
% 1.56/0.54  fof(f368,plain,(
% 1.56/0.54    ~spl9_17),
% 1.56/0.54    inference(avatar_contradiction_clause,[],[f367])).
% 1.56/0.54  fof(f367,plain,(
% 1.56/0.54    $false | ~spl9_17),
% 1.56/0.54    inference(subsumption_resolution,[],[f295,f364])).
% 1.56/0.54  fof(f364,plain,(
% 1.56/0.54    ( ! [X1] : (~v1_subset_1(X1,X1)) )),
% 1.56/0.54    inference(subsumption_resolution,[],[f113,f362])).
% 1.56/0.54  fof(f113,plain,(
% 1.56/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 1.56/0.54    inference(equality_resolution,[],[f104])).
% 1.56/0.54  fof(f104,plain,(
% 1.56/0.54    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.56/0.54    inference(cnf_transformation,[],[f66])).
% 1.56/0.54  fof(f295,plain,(
% 1.56/0.54    v1_subset_1(sK1,sK1) | ~spl9_17),
% 1.56/0.54    inference(avatar_component_clause,[],[f293])).
% 1.56/0.54  fof(f293,plain,(
% 1.56/0.54    spl9_17 <=> v1_subset_1(sK1,sK1)),
% 1.56/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 1.56/0.54  fof(f335,plain,(
% 1.56/0.54    ~spl9_4 | spl9_13 | ~spl9_14 | ~spl9_18),
% 1.56/0.54    inference(avatar_contradiction_clause,[],[f334])).
% 1.56/0.54  fof(f334,plain,(
% 1.56/0.54    $false | (~spl9_4 | spl9_13 | ~spl9_14 | ~spl9_18)),
% 1.56/0.54    inference(subsumption_resolution,[],[f333,f247])).
% 1.56/0.54  fof(f247,plain,(
% 1.56/0.54    ~m1_subset_1(k3_yellow_0(sK0),sK1) | spl9_13),
% 1.56/0.54    inference(avatar_component_clause,[],[f245])).
% 1.56/0.54  fof(f245,plain,(
% 1.56/0.54    spl9_13 <=> m1_subset_1(k3_yellow_0(sK0),sK1)),
% 1.56/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 1.56/0.54  fof(f333,plain,(
% 1.56/0.54    m1_subset_1(k3_yellow_0(sK0),sK1) | (~spl9_4 | ~spl9_14 | ~spl9_18)),
% 1.56/0.54    inference(forward_demodulation,[],[f332,f252])).
% 1.56/0.54  fof(f252,plain,(
% 1.56/0.54    u1_struct_0(sK0) = sK1 | ~spl9_14),
% 1.56/0.54    inference(avatar_component_clause,[],[f250])).
% 1.56/0.54  fof(f332,plain,(
% 1.56/0.54    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | (~spl9_4 | ~spl9_18)),
% 1.56/0.54    inference(subsumption_resolution,[],[f325,f134])).
% 1.56/0.54  fof(f325,plain,(
% 1.56/0.54    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~spl9_18),
% 1.56/0.54    inference(superposition,[],[f102,f314])).
% 1.56/0.54  fof(f315,plain,(
% 1.56/0.54    spl9_18 | ~spl9_4),
% 1.56/0.54    inference(avatar_split_clause,[],[f172,f132,f312])).
% 1.56/0.54  fof(f172,plain,(
% 1.56/0.54    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) | ~spl9_4),
% 1.56/0.54    inference(unit_resulting_resolution,[],[f134,f81])).
% 1.56/0.54  fof(f81,plain,(
% 1.56/0.54    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 1.56/0.54    inference(cnf_transformation,[],[f23])).
% 1.56/0.54  fof(f23,plain,(
% 1.56/0.54    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 1.56/0.54    inference(ennf_transformation,[],[f9])).
% 1.56/0.54  fof(f9,axiom,(
% 1.56/0.54    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 1.56/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).
% 1.56/0.54  fof(f296,plain,(
% 1.56/0.54    spl9_17 | ~spl9_9 | ~spl9_14),
% 1.56/0.54    inference(avatar_split_clause,[],[f280,f250,f158,f293])).
% 1.56/0.54  fof(f158,plain,(
% 1.56/0.54    spl9_9 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.56/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 1.56/0.54  fof(f280,plain,(
% 1.56/0.54    v1_subset_1(sK1,sK1) | (~spl9_9 | ~spl9_14)),
% 1.56/0.54    inference(superposition,[],[f160,f252])).
% 1.56/0.54  fof(f160,plain,(
% 1.56/0.54    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl9_9),
% 1.56/0.54    inference(avatar_component_clause,[],[f158])).
% 1.56/0.54  fof(f253,plain,(
% 1.56/0.54    spl9_14 | ~spl9_8 | spl9_9),
% 1.56/0.54    inference(avatar_split_clause,[],[f184,f158,f152,f250])).
% 1.56/0.54  fof(f184,plain,(
% 1.56/0.54    u1_struct_0(sK0) = sK1 | (~spl9_8 | spl9_9)),
% 1.56/0.54    inference(unit_resulting_resolution,[],[f159,f154,f105])).
% 1.56/0.54  fof(f159,plain,(
% 1.56/0.54    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl9_9),
% 1.56/0.54    inference(avatar_component_clause,[],[f158])).
% 1.56/0.54  fof(f248,plain,(
% 1.56/0.54    ~spl9_13 | spl9_5 | spl9_10),
% 1.56/0.54    inference(avatar_split_clause,[],[f180,f162,f137,f245])).
% 1.56/0.54  fof(f137,plain,(
% 1.56/0.54    spl9_5 <=> v1_xboole_0(sK1)),
% 1.56/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.56/0.54  fof(f180,plain,(
% 1.56/0.54    ~m1_subset_1(k3_yellow_0(sK0),sK1) | (spl9_5 | spl9_10)),
% 1.56/0.54    inference(unit_resulting_resolution,[],[f164,f139,f103])).
% 1.56/0.54  fof(f103,plain,(
% 1.56/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.56/0.54    inference(cnf_transformation,[],[f34])).
% 1.56/0.54  fof(f34,plain,(
% 1.56/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.56/0.54    inference(flattening,[],[f33])).
% 1.56/0.54  fof(f33,plain,(
% 1.56/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.56/0.54    inference(ennf_transformation,[],[f6])).
% 1.56/0.54  fof(f6,axiom,(
% 1.56/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.56/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.56/0.54  fof(f139,plain,(
% 1.56/0.54    ~v1_xboole_0(sK1) | spl9_5),
% 1.56/0.54    inference(avatar_component_clause,[],[f137])).
% 1.56/0.54  fof(f164,plain,(
% 1.56/0.54    ~r2_hidden(k3_yellow_0(sK0),sK1) | spl9_10),
% 1.56/0.54    inference(avatar_component_clause,[],[f162])).
% 1.56/0.54  fof(f201,plain,(
% 1.56/0.54    spl9_12 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4),
% 1.56/0.54    inference(avatar_split_clause,[],[f194,f132,f127,f122,f117,f198])).
% 1.56/0.54  fof(f117,plain,(
% 1.56/0.54    spl9_1 <=> v2_struct_0(sK0)),
% 1.56/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.56/0.54  fof(f122,plain,(
% 1.56/0.54    spl9_2 <=> v5_orders_2(sK0)),
% 1.56/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.56/0.54  fof(f127,plain,(
% 1.56/0.54    spl9_3 <=> v1_yellow_0(sK0)),
% 1.56/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.56/0.54  fof(f194,plain,(
% 1.56/0.54    r1_yellow_0(sK0,k1_xboole_0) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 1.56/0.54    inference(unit_resulting_resolution,[],[f119,f124,f129,f134,f97])).
% 1.56/0.54  fof(f97,plain,(
% 1.56/0.54    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.56/0.54    inference(cnf_transformation,[],[f31])).
% 1.56/0.54  fof(f31,plain,(
% 1.56/0.54    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.56/0.54    inference(flattening,[],[f30])).
% 1.56/0.54  fof(f30,plain,(
% 1.56/0.54    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.56/0.54    inference(ennf_transformation,[],[f20])).
% 1.56/0.54  fof(f20,plain,(
% 1.56/0.54    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 1.56/0.54    inference(pure_predicate_removal,[],[f12])).
% 1.56/0.54  fof(f12,axiom,(
% 1.56/0.54    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 1.56/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).
% 1.56/0.54  fof(f129,plain,(
% 1.56/0.54    v1_yellow_0(sK0) | ~spl9_3),
% 1.56/0.54    inference(avatar_component_clause,[],[f127])).
% 1.56/0.54  fof(f124,plain,(
% 1.56/0.54    v5_orders_2(sK0) | ~spl9_2),
% 1.56/0.54    inference(avatar_component_clause,[],[f122])).
% 1.56/0.54  fof(f119,plain,(
% 1.56/0.54    ~v2_struct_0(sK0) | spl9_1),
% 1.56/0.54    inference(avatar_component_clause,[],[f117])).
% 1.56/0.54  fof(f167,plain,(
% 1.56/0.54    ~spl9_9 | spl9_10),
% 1.56/0.54    inference(avatar_split_clause,[],[f166,f162,f158])).
% 1.56/0.54  fof(f166,plain,(
% 1.56/0.54    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl9_10),
% 1.56/0.54    inference(subsumption_resolution,[],[f79,f164])).
% 1.56/0.54  fof(f79,plain,(
% 1.56/0.54    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.56/0.54    inference(cnf_transformation,[],[f45])).
% 1.56/0.54  fof(f45,plain,(
% 1.56/0.54    ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.56/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).
% 1.56/0.54  fof(f43,plain,(
% 1.56/0.54    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.56/0.54    introduced(choice_axiom,[])).
% 1.56/0.54  fof(f44,plain,(
% 1.56/0.54    ? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1))),
% 1.56/0.55    introduced(choice_axiom,[])).
% 1.56/0.55  fof(f42,plain,(
% 1.56/0.55    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 1.56/0.55    inference(flattening,[],[f41])).
% 1.56/0.55  fof(f41,plain,(
% 1.56/0.55    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 1.56/0.55    inference(nnf_transformation,[],[f22])).
% 1.56/0.55  fof(f22,plain,(
% 1.56/0.55    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 1.56/0.55    inference(flattening,[],[f21])).
% 1.56/0.55  fof(f21,plain,(
% 1.56/0.55    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.56/0.55    inference(ennf_transformation,[],[f19])).
% 1.56/0.55  fof(f19,plain,(
% 1.56/0.55    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.56/0.55    inference(pure_predicate_removal,[],[f18])).
% 1.56/0.55  fof(f18,plain,(
% 1.56/0.55    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.56/0.55    inference(pure_predicate_removal,[],[f17])).
% 1.56/0.55  fof(f17,plain,(
% 1.56/0.55    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.56/0.55    inference(pure_predicate_removal,[],[f16])).
% 1.56/0.55  fof(f16,negated_conjecture,(
% 1.56/0.55    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.56/0.55    inference(negated_conjecture,[],[f15])).
% 1.56/0.55  fof(f15,conjecture,(
% 1.56/0.55    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.56/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).
% 1.56/0.55  fof(f165,plain,(
% 1.56/0.55    spl9_9 | ~spl9_10),
% 1.56/0.55    inference(avatar_split_clause,[],[f78,f162,f158])).
% 1.56/0.55  fof(f78,plain,(
% 1.56/0.55    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.56/0.55    inference(cnf_transformation,[],[f45])).
% 1.56/0.55  fof(f155,plain,(
% 1.56/0.55    spl9_8),
% 1.56/0.55    inference(avatar_split_clause,[],[f77,f152])).
% 1.56/0.55  fof(f77,plain,(
% 1.56/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.55    inference(cnf_transformation,[],[f45])).
% 1.56/0.55  fof(f150,plain,(
% 1.56/0.55    spl9_7),
% 1.56/0.55    inference(avatar_split_clause,[],[f80,f147])).
% 1.56/0.55  fof(f80,plain,(
% 1.56/0.55    v1_xboole_0(k1_xboole_0)),
% 1.56/0.55    inference(cnf_transformation,[],[f2])).
% 1.56/0.55  fof(f2,axiom,(
% 1.56/0.55    v1_xboole_0(k1_xboole_0)),
% 1.56/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.56/0.55  fof(f145,plain,(
% 1.56/0.55    spl9_6),
% 1.56/0.55    inference(avatar_split_clause,[],[f76,f142])).
% 1.56/0.55  fof(f76,plain,(
% 1.56/0.55    v13_waybel_0(sK1,sK0)),
% 1.56/0.55    inference(cnf_transformation,[],[f45])).
% 1.56/0.55  fof(f140,plain,(
% 1.56/0.55    ~spl9_5),
% 1.56/0.55    inference(avatar_split_clause,[],[f75,f137])).
% 1.56/0.55  fof(f75,plain,(
% 1.56/0.55    ~v1_xboole_0(sK1)),
% 1.56/0.55    inference(cnf_transformation,[],[f45])).
% 1.56/0.55  fof(f135,plain,(
% 1.56/0.55    spl9_4),
% 1.56/0.55    inference(avatar_split_clause,[],[f74,f132])).
% 1.56/0.55  fof(f74,plain,(
% 1.56/0.55    l1_orders_2(sK0)),
% 1.56/0.55    inference(cnf_transformation,[],[f45])).
% 1.56/0.55  fof(f130,plain,(
% 1.56/0.55    spl9_3),
% 1.56/0.55    inference(avatar_split_clause,[],[f73,f127])).
% 1.56/0.55  fof(f73,plain,(
% 1.56/0.55    v1_yellow_0(sK0)),
% 1.56/0.55    inference(cnf_transformation,[],[f45])).
% 1.56/0.55  fof(f125,plain,(
% 1.56/0.55    spl9_2),
% 1.56/0.55    inference(avatar_split_clause,[],[f72,f122])).
% 1.56/0.55  fof(f72,plain,(
% 1.56/0.55    v5_orders_2(sK0)),
% 1.56/0.55    inference(cnf_transformation,[],[f45])).
% 1.56/0.55  fof(f120,plain,(
% 1.56/0.55    ~spl9_1),
% 1.56/0.55    inference(avatar_split_clause,[],[f71,f117])).
% 1.56/0.55  fof(f71,plain,(
% 1.56/0.55    ~v2_struct_0(sK0)),
% 1.56/0.55    inference(cnf_transformation,[],[f45])).
% 1.56/0.55  % SZS output end Proof for theBenchmark
% 1.56/0.55  % (2079)------------------------------
% 1.56/0.55  % (2079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.55  % (2079)Termination reason: Refutation
% 1.56/0.55  
% 1.56/0.55  % (2079)Memory used [KB]: 11385
% 1.56/0.55  % (2079)Time elapsed: 0.147 s
% 1.56/0.55  % (2079)------------------------------
% 1.56/0.55  % (2079)------------------------------
% 1.56/0.55  % (2055)Success in time 0.201 s
%------------------------------------------------------------------------------
