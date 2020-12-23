%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t33_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:40 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 335 expanded)
%              Number of leaves         :   15 ( 105 expanded)
%              Depth                    :   17
%              Number of atoms          :  530 (1706 expanded)
%              Number of equality atoms :   42 ( 150 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f314,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f71,f75,f79,f88,f96,f149,f276,f284,f292,f313])).

fof(f313,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_26 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f311,f294])).

fof(f294,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f293,f92])).

fof(f92,plain,
    ( k2_yellow_0(sK0,sK2) = sK1
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl7_10
  <=> k2_yellow_0(sK0,sK2) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f293,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | k2_yellow_0(sK0,sK2) != sK1
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f38,f190])).

fof(f190,plain,
    ( r1_lattice3(sK0,sK2,sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(superposition,[],[f134,f92])).

fof(f134,plain,
    ( ! [X2] : r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f133,f84])).

fof(f84,plain,
    ( ! [X0] : r2_yellow_0(sK0,X0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f83,f66])).

fof(f66,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl7_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f83,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | r2_yellow_0(sK0,X0) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f82,f74])).

fof(f74,plain,
    ( v3_lattice3(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl7_4
  <=> v3_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f82,plain,
    ( ! [X0] :
        ( ~ v3_lattice3(sK0)
        | v2_struct_0(sK0)
        | r2_yellow_0(sK0,X0) )
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f80,f70])).

fof(f70,plain,
    ( v5_orders_2(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl7_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | ~ v3_lattice3(sK0)
        | v2_struct_0(sK0)
        | r2_yellow_0(sK0,X0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f78,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_lattice3(X0)
      | v2_struct_0(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] : r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] : r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : r2_yellow_0(X0,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t33_yellow_0.p',t17_yellow_0)).

fof(f78,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl7_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f133,plain,
    ( ! [X2] :
        ( ~ r2_yellow_0(sK0,X2)
        | r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2)) )
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f132,f70])).

fof(f132,plain,
    ( ! [X2] :
        ( ~ v5_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X2)
        | r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2)) )
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f127,f78])).

fof(f127,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X2)
        | r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f81,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_yellow_0(X0,X2)
      | r1_lattice3(X0,X2,k2_yellow_0(X0,X2)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k2_yellow_0(X0,X2) != X1
      | ~ r2_yellow_0(X0,X2)
      | r1_lattice3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X4,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t33_yellow_0.p',t31_yellow_0)).

fof(f81,plain,
    ( ! [X1] : m1_subset_1(k2_yellow_0(sK0,X1),u1_struct_0(sK0))
    | ~ spl7_6 ),
    inference(resolution,[],[f78,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t33_yellow_0.p',dt_k2_yellow_0)).

fof(f38,plain,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK3,sK1)
    | k2_yellow_0(sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) = X1
            <~> ( ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | ~ r1_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X2,X1) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_yellow_0(X0,X2) = X1
            <~> ( ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | ~ r1_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X2,X1) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( k2_yellow_0(X0,X2) = X1
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k2_yellow_0(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X2,X3)
                     => r1_orders_2(X0,X3,X1) ) )
                & r1_lattice3(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t33_yellow_0.p',t33_yellow_0)).

fof(f311,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f310,f92])).

fof(f310,plain,
    ( r1_orders_2(sK0,sK3,k2_yellow_0(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f305,f304])).

fof(f304,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f303,f92])).

fof(f303,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | k2_yellow_0(sK0,sK2) != sK1
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f36,f190])).

fof(f36,plain,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | m1_subset_1(sK3,u1_struct_0(sK0))
    | k2_yellow_0(sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f305,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3,k2_yellow_0(sK0,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_26 ),
    inference(resolution,[],[f164,f131])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f130,f84])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ r2_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0)) )
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f129,f70])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0)) )
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f126,f78])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f81,f63])).

fof(f63,plain,(
    ! [X4,X2,X0] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X4)
      | r1_orders_2(X0,X4,k2_yellow_0(X0,X2)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k2_yellow_0(X0,X2) != X1
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X4)
      | r1_orders_2(X0,X4,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f164,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl7_26
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f292,plain,
    ( spl7_26
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f291,f91,f77,f73,f69,f65,f163])).

fof(f291,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f290,f92])).

fof(f290,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | k2_yellow_0(sK0,sK2) != sK1
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f37,f190])).

fof(f37,plain,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | r1_lattice3(sK0,sK2,sK3)
    | k2_yellow_0(sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f284,plain,
    ( ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8
    | spl7_11
    | ~ spl7_12
    | ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f282,f112])).

fof(f112,plain,
    ( k2_yellow_0(sK0,sK2) != sK1
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl7_11
  <=> k2_yellow_0(sK0,sK2) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f282,plain,
    ( k2_yellow_0(sK0,sK2) = sK1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f281,f70])).

fof(f281,plain,
    ( ~ v5_orders_2(sK0)
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f280,f95])).

fof(f95,plain,
    ( r1_lattice3(sK0,sK2,sK1)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl7_12
  <=> r1_lattice3(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f280,plain,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | ~ v5_orders_2(sK0)
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f279,f87])).

fof(f87,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl7_8
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f279,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ v5_orders_2(sK0)
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl7_6
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f278,f78])).

fof(f278,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ v5_orders_2(sK0)
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl7_44 ),
    inference(resolution,[],[f275,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ v5_orders_2(X0)
      | k2_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f275,plain,
    ( r1_orders_2(sK0,sK4(sK0,sK1,sK2),sK1)
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl7_44
  <=> r1_orders_2(sK0,sK4(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f276,plain,
    ( spl7_44
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8
    | spl7_11
    | ~ spl7_12
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f250,f147,f94,f111,f86,f77,f69,f274])).

fof(f147,plain,
    ( spl7_22
  <=> r1_lattice3(sK0,sK2,sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f250,plain,
    ( r1_orders_2(sK0,sK4(sK0,sK1,sK2),sK1)
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f244,f229])).

fof(f229,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f106,f112])).

fof(f106,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f105,f70])).

fof(f105,plain,
    ( ~ v5_orders_2(sK0)
    | m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f104,f87])).

fof(f104,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f102,f78])).

fof(f102,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl7_12 ),
    inference(resolution,[],[f95,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X2,X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f244,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK4(sK0,sK1,sK2),sK1)
    | ~ spl7_11
    | ~ spl7_22 ),
    inference(resolution,[],[f148,f230])).

fof(f230,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK0,sK2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X3,sK1) )
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f35,f112])).

fof(f35,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK2,X3)
      | r1_orders_2(sK0,X3,sK1)
      | k2_yellow_0(sK0,sK2) = sK1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f148,plain,
    ( r1_lattice3(sK0,sK2,sK4(sK0,sK1,sK2))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f147])).

fof(f149,plain,
    ( spl7_22
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8
    | spl7_11
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f117,f94,f111,f86,f77,f69,f147])).

fof(f117,plain,
    ( r1_lattice3(sK0,sK2,sK4(sK0,sK1,sK2))
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f109,f112])).

fof(f109,plain,
    ( r1_lattice3(sK0,sK2,sK4(sK0,sK1,sK2))
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f108,f70])).

fof(f108,plain,
    ( ~ v5_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK4(sK0,sK1,sK2))
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f107,f87])).

fof(f107,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK4(sK0,sK1,sK2))
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f103,f78])).

fof(f103,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK4(sK0,sK1,sK2))
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl7_12 ),
    inference(resolution,[],[f95,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X2,X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r1_lattice3(X0,X2,sK4(X0,X1,X2))
      | k2_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f96,plain,
    ( spl7_10
    | spl7_12 ),
    inference(avatar_split_clause,[],[f39,f94,f91])).

fof(f39,plain,
    ( r1_lattice3(sK0,sK2,sK1)
    | k2_yellow_0(sK0,sK2) = sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f40,f86])).

fof(f40,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f44,f77])).

fof(f44,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f43,f73])).

fof(f43,plain,(
    v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f42,f69])).

fof(f42,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f41,f65])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
