%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t39_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:41 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 402 expanded)
%              Number of leaves         :   34 ( 165 expanded)
%              Depth                    :   12
%              Number of atoms          :  876 (1651 expanded)
%              Number of equality atoms :   76 ( 175 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f840,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f121,f125,f129,f136,f140,f151,f158,f168,f208,f215,f232,f237,f275,f302,f358,f395,f408,f586,f620,f664,f704,f766,f831])).

fof(f831,plain,
    ( ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_20
    | spl7_41
    | ~ spl7_62 ),
    inference(avatar_contradiction_clause,[],[f830])).

fof(f830,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_20
    | ~ spl7_41
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f829,f394])).

fof(f394,plain,
    ( k1_yellow_0(sK0,k1_tarski(sK1)) != sK1
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f393])).

fof(f393,plain,
    ( spl7_41
  <=> k1_yellow_0(sK0,k1_tarski(sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f829,plain,
    ( k1_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_20
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f828,f124])).

fof(f124,plain,
    ( v5_orders_2(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f828,plain,
    ( ~ v5_orders_2(sK0)
    | k1_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_20
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f827,f207])).

fof(f207,plain,
    ( r2_lattice3(sK0,k1_tarski(sK1),sK1)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl7_20
  <=> r2_lattice3(sK0,k1_tarski(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f827,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK1),sK1)
    | ~ v5_orders_2(sK0)
    | k1_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f826,f139])).

fof(f139,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl7_10
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f826,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k1_tarski(sK1),sK1)
    | ~ v5_orders_2(sK0)
    | k1_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_6
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f816,f128])).

fof(f128,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f816,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k1_tarski(sK1),sK1)
    | ~ v5_orders_2(sK0)
    | k1_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_62 ),
    inference(resolution,[],[f703,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,sK5(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ v5_orders_2(X0)
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t39_yellow_0.p',t30_yellow_0)).

fof(f703,plain,
    ( r1_orders_2(sK0,sK1,sK5(sK0,sK1,k1_tarski(sK1)))
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f702])).

fof(f702,plain,
    ( spl7_62
  <=> r1_orders_2(sK0,sK1,sK5(sK0,sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f766,plain,
    ( ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_32
    | spl7_35
    | ~ spl7_60 ),
    inference(avatar_contradiction_clause,[],[f765])).

fof(f765,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_32
    | ~ spl7_35
    | ~ spl7_60 ),
    inference(subsumption_resolution,[],[f764,f301])).

fof(f301,plain,
    ( k2_yellow_0(sK0,k1_tarski(sK1)) != sK1
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl7_35
  <=> k2_yellow_0(sK0,k1_tarski(sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f764,plain,
    ( k2_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_32
    | ~ spl7_60 ),
    inference(subsumption_resolution,[],[f763,f124])).

fof(f763,plain,
    ( ~ v5_orders_2(sK0)
    | k2_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_32
    | ~ spl7_60 ),
    inference(subsumption_resolution,[],[f762,f274])).

fof(f274,plain,
    ( r1_lattice3(sK0,k1_tarski(sK1),sK1)
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl7_32
  <=> r1_lattice3(sK0,k1_tarski(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f762,plain,
    ( ~ r1_lattice3(sK0,k1_tarski(sK1),sK1)
    | ~ v5_orders_2(sK0)
    | k2_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_60 ),
    inference(subsumption_resolution,[],[f761,f139])).

fof(f761,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k1_tarski(sK1),sK1)
    | ~ v5_orders_2(sK0)
    | k2_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_6
    | ~ spl7_60 ),
    inference(subsumption_resolution,[],[f751,f128])).

fof(f751,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k1_tarski(sK1),sK1)
    | ~ v5_orders_2(sK0)
    | k2_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_60 ),
    inference(resolution,[],[f663,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ v5_orders_2(X0)
      | k2_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t39_yellow_0.p',t31_yellow_0)).

fof(f663,plain,
    ( r1_orders_2(sK0,sK6(sK0,sK1,k1_tarski(sK1)),sK1)
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f662])).

fof(f662,plain,
    ( spl7_60
  <=> r1_orders_2(sK0,sK6(sK0,sK1,k1_tarski(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f704,plain,
    ( spl7_62
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_42
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f688,f618,f406,f138,f127,f702])).

fof(f406,plain,
    ( spl7_42
  <=> m1_subset_1(sK5(sK0,sK1,k1_tarski(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f618,plain,
    ( spl7_56
  <=> r2_lattice3(sK0,k1_tarski(sK1),sK5(sK0,sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f688,plain,
    ( r1_orders_2(sK0,sK1,sK5(sK0,sK1,k1_tarski(sK1)))
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_42
    | ~ spl7_56 ),
    inference(subsumption_resolution,[],[f687,f128])).

fof(f687,plain,
    ( ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK5(sK0,sK1,k1_tarski(sK1)))
    | ~ spl7_10
    | ~ spl7_42
    | ~ spl7_56 ),
    inference(subsumption_resolution,[],[f686,f139])).

fof(f686,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK5(sK0,sK1,k1_tarski(sK1)))
    | ~ spl7_42
    | ~ spl7_56 ),
    inference(subsumption_resolution,[],[f680,f407])).

fof(f407,plain,
    ( m1_subset_1(sK5(sK0,sK1,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f406])).

fof(f680,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK5(sK0,sK1,k1_tarski(sK1)))
    | ~ spl7_56 ),
    inference(resolution,[],[f619,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattice3(X0,k1_tarski(X2),X1)
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(X0,X1,X2)
                  | ~ r1_lattice3(X0,k1_tarski(X2),X1) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                 => r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r2_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X1,X2)
                 => r1_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t39_yellow_0.p',t7_yellow_0)).

fof(f619,plain,
    ( r2_lattice3(sK0,k1_tarski(sK1),sK5(sK0,sK1,k1_tarski(sK1)))
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f618])).

fof(f664,plain,
    ( spl7_60
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_36
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f648,f584,f356,f138,f127,f662])).

fof(f356,plain,
    ( spl7_36
  <=> m1_subset_1(sK6(sK0,sK1,k1_tarski(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f584,plain,
    ( spl7_54
  <=> r1_lattice3(sK0,k1_tarski(sK1),sK6(sK0,sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f648,plain,
    ( r1_orders_2(sK0,sK6(sK0,sK1,k1_tarski(sK1)),sK1)
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_36
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f647,f128])).

fof(f647,plain,
    ( ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK6(sK0,sK1,k1_tarski(sK1)),sK1)
    | ~ spl7_10
    | ~ spl7_36
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f646,f139])).

fof(f646,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK6(sK0,sK1,k1_tarski(sK1)),sK1)
    | ~ spl7_36
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f640,f357])).

fof(f357,plain,
    ( m1_subset_1(sK6(sK0,sK1,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f356])).

fof(f640,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK6(sK0,sK1,k1_tarski(sK1)),sK1)
    | ~ spl7_54 ),
    inference(resolution,[],[f585,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f585,plain,
    ( r1_lattice3(sK0,k1_tarski(sK1),sK6(sK0,sK1,k1_tarski(sK1)))
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f584])).

fof(f620,plain,
    ( spl7_56
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_20
    | spl7_41 ),
    inference(avatar_split_clause,[],[f587,f393,f206,f138,f127,f123,f618])).

fof(f587,plain,
    ( r2_lattice3(sK0,k1_tarski(sK1),sK5(sK0,sK1,k1_tarski(sK1)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_20
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f298,f394])).

fof(f298,plain,
    ( r2_lattice3(sK0,k1_tarski(sK1),sK5(sK0,sK1,k1_tarski(sK1)))
    | k1_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f297,f124])).

fof(f297,plain,
    ( ~ v5_orders_2(sK0)
    | r2_lattice3(sK0,k1_tarski(sK1),sK5(sK0,sK1,k1_tarski(sK1)))
    | k1_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f296,f139])).

fof(f296,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r2_lattice3(sK0,k1_tarski(sK1),sK5(sK0,sK1,k1_tarski(sK1)))
    | k1_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_6
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f285,f128])).

fof(f285,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r2_lattice3(sK0,k1_tarski(sK1),sK5(sK0,sK1,k1_tarski(sK1)))
    | k1_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_20 ),
    inference(resolution,[],[f207,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X2,X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r2_lattice3(X0,X2,sK5(X0,X1,X2))
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f586,plain,
    ( spl7_54
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_32
    | spl7_35 ),
    inference(avatar_split_clause,[],[f469,f300,f273,f138,f127,f123,f584])).

fof(f469,plain,
    ( r1_lattice3(sK0,k1_tarski(sK1),sK6(sK0,sK1,k1_tarski(sK1)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_32
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f321,f301])).

fof(f321,plain,
    ( r1_lattice3(sK0,k1_tarski(sK1),sK6(sK0,sK1,k1_tarski(sK1)))
    | k2_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f320,f124])).

fof(f320,plain,
    ( ~ v5_orders_2(sK0)
    | r1_lattice3(sK0,k1_tarski(sK1),sK6(sK0,sK1,k1_tarski(sK1)))
    | k2_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f319,f139])).

fof(f319,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_lattice3(sK0,k1_tarski(sK1),sK6(sK0,sK1,k1_tarski(sK1)))
    | k2_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_6
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f307,f128])).

fof(f307,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_lattice3(sK0,k1_tarski(sK1),sK6(sK0,sK1,k1_tarski(sK1)))
    | k2_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_32 ),
    inference(resolution,[],[f274,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X2,X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r1_lattice3(X0,X2,sK6(X0,X1,X2))
      | k2_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f408,plain,
    ( spl7_42
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | spl7_17
    | ~ spl7_20
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f391,f230,f206,f156,f138,f127,f123,f406])).

fof(f156,plain,
    ( spl7_17
  <=> k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f230,plain,
    ( spl7_26
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f391,plain,
    ( m1_subset_1(sK5(sK0,sK1,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f295,f389])).

fof(f389,plain,
    ( k1_yellow_0(sK0,k1_tarski(sK1)) != sK1
    | ~ spl7_17
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f157,f231])).

fof(f231,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f230])).

fof(f157,plain,
    ( k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != sK1
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f156])).

fof(f295,plain,
    ( m1_subset_1(sK5(sK0,sK1,k1_tarski(sK1)),u1_struct_0(sK0))
    | k1_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f294,f124])).

fof(f294,plain,
    ( ~ v5_orders_2(sK0)
    | m1_subset_1(sK5(sK0,sK1,k1_tarski(sK1)),u1_struct_0(sK0))
    | k1_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f293,f139])).

fof(f293,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | m1_subset_1(sK5(sK0,sK1,k1_tarski(sK1)),u1_struct_0(sK0))
    | k1_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_6
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f284,f128])).

fof(f284,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | m1_subset_1(sK5(sK0,sK1,k1_tarski(sK1)),u1_struct_0(sK0))
    | k1_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_20 ),
    inference(resolution,[],[f207,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X2,X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f395,plain,
    ( ~ spl7_41
    | spl7_17
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f389,f230,f156,f393])).

fof(f358,plain,
    ( spl7_36
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_32
    | spl7_35 ),
    inference(avatar_split_clause,[],[f318,f300,f273,f138,f127,f123,f356])).

fof(f318,plain,
    ( m1_subset_1(sK6(sK0,sK1,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_32
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f317,f301])).

fof(f317,plain,
    ( m1_subset_1(sK6(sK0,sK1,k1_tarski(sK1)),u1_struct_0(sK0))
    | k2_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f316,f124])).

fof(f316,plain,
    ( ~ v5_orders_2(sK0)
    | m1_subset_1(sK6(sK0,sK1,k1_tarski(sK1)),u1_struct_0(sK0))
    | k2_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f315,f139])).

fof(f315,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | m1_subset_1(sK6(sK0,sK1,k1_tarski(sK1)),u1_struct_0(sK0))
    | k2_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_6
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f306,f128])).

fof(f306,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | m1_subset_1(sK6(sK0,sK1,k1_tarski(sK1)),u1_struct_0(sK0))
    | k2_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl7_32 ),
    inference(resolution,[],[f274,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X2,X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f302,plain,
    ( ~ spl7_35
    | spl7_15
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f266,f230,f153,f300])).

fof(f153,plain,
    ( spl7_15
  <=> k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f266,plain,
    ( k2_yellow_0(sK0,k1_tarski(sK1)) != sK1
    | ~ spl7_15
    | ~ spl7_26 ),
    inference(superposition,[],[f154,f231])).

fof(f154,plain,
    ( k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != sK1
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f153])).

fof(f275,plain,
    ( spl7_32
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f191,f166,f138,f127,f273])).

fof(f166,plain,
    ( spl7_18
  <=> r1_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f191,plain,
    ( r1_lattice3(sK0,k1_tarski(sK1),sK1)
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f190,f128])).

fof(f190,plain,
    ( ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,k1_tarski(sK1),sK1)
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f186,f139])).

fof(f186,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,k1_tarski(sK1),sK1)
    | ~ spl7_18 ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,k1_tarski(sK1),sK1)
    | ~ spl7_18 ),
    inference(resolution,[],[f167,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,k1_tarski(X2),X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f167,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f166])).

fof(f237,plain,
    ( spl7_1
    | ~ spl7_8
    | ~ spl7_24 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_8
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f235,f116])).

fof(f116,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl7_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f235,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_8
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f233,f135])).

fof(f135,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl7_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f233,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_24 ),
    inference(resolution,[],[f214,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t39_yellow_0.p',fc2_struct_0)).

fof(f214,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl7_24
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f232,plain,
    ( spl7_26
    | ~ spl7_10
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f221,f210,f138,f230])).

fof(f210,plain,
    ( spl7_22
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f221,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl7_10
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f143,f219])).

fof(f219,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_22 ),
    inference(resolution,[],[f211,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t39_yellow_0.p',t7_boole)).

fof(f211,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f210])).

fof(f143,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl7_10 ),
    inference(resolution,[],[f139,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t39_yellow_0.p',redefinition_k6_domain_1)).

fof(f215,plain,
    ( spl7_22
    | spl7_24
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f142,f138,f213,f210])).

fof(f142,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl7_10 ),
    inference(resolution,[],[f139,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t39_yellow_0.p',t2_subset)).

fof(f208,plain,
    ( spl7_20
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f189,f166,f138,f127,f206])).

fof(f189,plain,
    ( r2_lattice3(sK0,k1_tarski(sK1),sK1)
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f188,f128])).

fof(f188,plain,
    ( ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,k1_tarski(sK1),sK1)
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f187,f139])).

fof(f187,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,k1_tarski(sK1),sK1)
    | ~ spl7_18 ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,k1_tarski(sK1),sK1)
    | ~ spl7_18 ),
    inference(resolution,[],[f167,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,k1_tarski(X2),X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f168,plain,
    ( spl7_18
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f164,f149,f138,f127,f119,f115,f166])).

fof(f119,plain,
    ( spl7_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f149,plain,
    ( spl7_12
  <=> r3_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f164,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f163,f116])).

fof(f163,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f162,f139])).

fof(f162,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f161,f128])).

fof(f161,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f160,f120])).

fof(f120,plain,
    ( v3_orders_2(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f160,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0)
    | ~ spl7_12 ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0)
    | ~ spl7_12 ),
    inference(resolution,[],[f150,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t39_yellow_0.p',redefinition_r3_orders_2)).

fof(f150,plain,
    ( r3_orders_2(sK0,sK1,sK1)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f149])).

fof(f158,plain,
    ( ~ spl7_15
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f64,f156,f153])).

fof(f64,plain,
    ( k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != sK1
    | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != sK1 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1
            | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1
            | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
              & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t39_yellow_0.p',t39_yellow_0)).

fof(f151,plain,
    ( spl7_12
    | spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f147,f138,f127,f119,f115,f149])).

fof(f147,plain,
    ( r3_orders_2(sK0,sK1,sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f146,f128])).

fof(f146,plain,
    ( ~ l1_orders_2(sK0)
    | r3_orders_2(sK0,sK1,sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f145,f120])).

fof(f145,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | r3_orders_2(sK0,sK1,sK1)
    | ~ spl7_1
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f141,f116])).

fof(f141,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | r3_orders_2(sK0,sK1,sK1)
    | ~ spl7_10 ),
    inference(resolution,[],[f139,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X1)
      | r3_orders_2(X1,X0,X0) ) ),
    inference(condensation,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t39_yellow_0.p',reflexivity_r3_orders_2)).

fof(f140,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f65,f138])).

fof(f65,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f136,plain,
    ( spl7_8
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f130,f127,f134])).

fof(f130,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_6 ),
    inference(resolution,[],[f128,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t39_yellow_0.p',dt_l1_orders_2)).

fof(f129,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f69,f127])).

fof(f69,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f125,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f68,f123])).

fof(f68,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f121,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f67,f119])).

fof(f67,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f117,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f66,f115])).

fof(f66,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
