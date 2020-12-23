%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1584+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:26 EST 2020

% Result     : Theorem 11.47s
% Output     : Refutation 11.47s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 424 expanded)
%              Number of leaves         :   31 ( 199 expanded)
%              Depth                    :   10
%              Number of atoms          :  613 (3120 expanded)
%              Number of equality atoms :   25 ( 233 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20922,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4521,f4531,f4541,f4546,f4556,f4575,f4585,f4595,f4596,f4620,f4772,f4777,f4787,f4795,f4832,f4993,f20536,f20547,f20911,f20921])).

fof(f20921,plain,
    ( ~ spl159_2
    | ~ spl159_4
    | ~ spl159_6
    | ~ spl159_7
    | ~ spl159_15
    | ~ spl159_20
    | ~ spl159_33
    | ~ spl159_36
    | spl159_37
    | ~ spl159_135 ),
    inference(avatar_contradiction_clause,[],[f20920])).

fof(f20920,plain,
    ( $false
    | ~ spl159_2
    | ~ spl159_4
    | ~ spl159_6
    | ~ spl159_7
    | ~ spl159_15
    | ~ spl159_20
    | ~ spl159_33
    | ~ spl159_36
    | spl159_37
    | ~ spl159_135 ),
    inference(subsumption_resolution,[],[f20912,f20919])).

fof(f20919,plain,
    ( ~ r1_orders_2(sK3,sK7(sK2,sK4,sK5),sK5)
    | ~ spl159_2
    | ~ spl159_4
    | ~ spl159_6
    | ~ spl159_7
    | ~ spl159_36
    | spl159_37
    | ~ spl159_135 ),
    inference(unit_resulting_resolution,[],[f4520,f4530,f4545,f4540,f4794,f4786,f20910,f4323])).

fof(f4323,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r1_orders_2(X1,X4,X5)
      | r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f4322])).

fof(f4322,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X1,X4,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3734])).

fof(f3734,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X1,X4,X5)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3093])).

fof(f3093,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3092])).

fof(f3092,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3051])).

fof(f3051,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X4,X5)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X0,X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_yellow_0)).

fof(f20910,plain,
    ( m1_subset_1(sK7(sK2,sK4,sK5),u1_struct_0(sK3))
    | ~ spl159_135 ),
    inference(avatar_component_clause,[],[f20908])).

fof(f20908,plain,
    ( spl159_135
  <=> m1_subset_1(sK7(sK2,sK4,sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl159_135])])).

fof(f4786,plain,
    ( m1_subset_1(sK7(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ spl159_36 ),
    inference(avatar_component_clause,[],[f4784])).

fof(f4784,plain,
    ( spl159_36
  <=> m1_subset_1(sK7(sK2,sK4,sK5),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl159_36])])).

fof(f4794,plain,
    ( ~ r1_orders_2(sK2,sK7(sK2,sK4,sK5),sK5)
    | spl159_37 ),
    inference(avatar_component_clause,[],[f4792])).

fof(f4792,plain,
    ( spl159_37
  <=> r1_orders_2(sK2,sK7(sK2,sK4,sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl159_37])])).

fof(f4540,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl159_6 ),
    inference(avatar_component_clause,[],[f4538])).

fof(f4538,plain,
    ( spl159_6
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl159_6])])).

fof(f4545,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl159_7 ),
    inference(avatar_component_clause,[],[f4543])).

fof(f4543,plain,
    ( spl159_7
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl159_7])])).

fof(f4530,plain,
    ( m1_yellow_0(sK3,sK2)
    | ~ spl159_4 ),
    inference(avatar_component_clause,[],[f4528])).

fof(f4528,plain,
    ( spl159_4
  <=> m1_yellow_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl159_4])])).

fof(f4520,plain,
    ( l1_orders_2(sK2)
    | ~ spl159_2 ),
    inference(avatar_component_clause,[],[f4518])).

fof(f4518,plain,
    ( spl159_2
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl159_2])])).

fof(f20912,plain,
    ( r1_orders_2(sK3,sK7(sK2,sK4,sK5),sK5)
    | ~ spl159_7
    | ~ spl159_15
    | ~ spl159_20
    | ~ spl159_33
    | ~ spl159_135 ),
    inference(unit_resulting_resolution,[],[f4619,f4545,f4584,f4771,f20910,f3708])).

fof(f3708,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3440])).

fof(f3440,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
                & r2_hidden(sK7(X0,X1,X2),X1)
                & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f3438,f3439])).

fof(f3439,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
        & r2_hidden(sK7(X0,X1,X2),X1)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3438,plain,(
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
    inference(rectify,[],[f3437])).

fof(f3437,plain,(
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
    inference(nnf_transformation,[],[f3079])).

fof(f3079,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3078])).

fof(f3078,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2832])).

fof(f2832,axiom,(
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

fof(f4771,plain,
    ( r2_hidden(sK7(sK2,sK4,sK5),sK4)
    | ~ spl159_33 ),
    inference(avatar_component_clause,[],[f4769])).

fof(f4769,plain,
    ( spl159_33
  <=> r2_hidden(sK7(sK2,sK4,sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl159_33])])).

fof(f4584,plain,
    ( r2_lattice3(sK3,sK4,sK5)
    | ~ spl159_15 ),
    inference(avatar_component_clause,[],[f4582])).

fof(f4582,plain,
    ( spl159_15
  <=> r2_lattice3(sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl159_15])])).

fof(f4619,plain,
    ( l1_orders_2(sK3)
    | ~ spl159_20 ),
    inference(avatar_component_clause,[],[f4617])).

fof(f4617,plain,
    ( spl159_20
  <=> l1_orders_2(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl159_20])])).

fof(f20911,plain,
    ( spl159_135
    | ~ spl159_9
    | ~ spl159_33 ),
    inference(avatar_split_clause,[],[f17910,f4769,f4553,f20908])).

fof(f4553,plain,
    ( spl159_9
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl159_9])])).

fof(f17910,plain,
    ( m1_subset_1(sK7(sK2,sK4,sK5),u1_struct_0(sK3))
    | ~ spl159_9
    | ~ spl159_33 ),
    inference(unit_resulting_resolution,[],[f4555,f4771,f3841])).

fof(f3841,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3160])).

fof(f3160,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f3159])).

fof(f3159,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f618])).

fof(f618,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f4555,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl159_9 ),
    inference(avatar_component_clause,[],[f4553])).

fof(f20547,plain,
    ( ~ spl159_2
    | ~ spl159_4
    | ~ spl159_6
    | ~ spl159_7
    | ~ spl159_17
    | ~ spl159_20
    | ~ spl159_34
    | ~ spl159_38
    | spl159_46
    | ~ spl159_133 ),
    inference(avatar_contradiction_clause,[],[f20546])).

fof(f20546,plain,
    ( $false
    | ~ spl159_2
    | ~ spl159_4
    | ~ spl159_6
    | ~ spl159_7
    | ~ spl159_17
    | ~ spl159_20
    | ~ spl159_34
    | ~ spl159_38
    | spl159_46
    | ~ spl159_133 ),
    inference(subsumption_resolution,[],[f20541,f20545])).

fof(f20545,plain,
    ( ~ r1_orders_2(sK3,sK5,sK8(sK2,sK4,sK5))
    | ~ spl159_2
    | ~ spl159_4
    | ~ spl159_6
    | ~ spl159_7
    | ~ spl159_38
    | spl159_46
    | ~ spl159_133 ),
    inference(unit_resulting_resolution,[],[f4520,f4530,f4540,f4545,f4992,f4831,f20535,f4323])).

fof(f20535,plain,
    ( m1_subset_1(sK8(sK2,sK4,sK5),u1_struct_0(sK3))
    | ~ spl159_133 ),
    inference(avatar_component_clause,[],[f20533])).

fof(f20533,plain,
    ( spl159_133
  <=> m1_subset_1(sK8(sK2,sK4,sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl159_133])])).

fof(f4831,plain,
    ( m1_subset_1(sK8(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ spl159_38 ),
    inference(avatar_component_clause,[],[f4829])).

fof(f4829,plain,
    ( spl159_38
  <=> m1_subset_1(sK8(sK2,sK4,sK5),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl159_38])])).

fof(f4992,plain,
    ( ~ r1_orders_2(sK2,sK5,sK8(sK2,sK4,sK5))
    | spl159_46 ),
    inference(avatar_component_clause,[],[f4990])).

fof(f4990,plain,
    ( spl159_46
  <=> r1_orders_2(sK2,sK5,sK8(sK2,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl159_46])])).

fof(f20541,plain,
    ( r1_orders_2(sK3,sK5,sK8(sK2,sK4,sK5))
    | ~ spl159_7
    | ~ spl159_17
    | ~ spl159_20
    | ~ spl159_34
    | ~ spl159_133 ),
    inference(unit_resulting_resolution,[],[f4619,f4545,f4594,f4776,f20535,f3727])).

fof(f3727,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3444])).

fof(f3444,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK8(X0,X1,X2))
                & r2_hidden(sK8(X0,X1,X2),X1)
                & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f3442,f3443])).

fof(f3443,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK8(X0,X1,X2))
        & r2_hidden(sK8(X0,X1,X2),X1)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3442,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3441])).

fof(f3441,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3088])).

fof(f3088,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3087])).

fof(f3087,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2831])).

fof(f2831,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(f4776,plain,
    ( r2_hidden(sK8(sK2,sK4,sK5),sK4)
    | ~ spl159_34 ),
    inference(avatar_component_clause,[],[f4774])).

fof(f4774,plain,
    ( spl159_34
  <=> r2_hidden(sK8(sK2,sK4,sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl159_34])])).

fof(f4594,plain,
    ( r1_lattice3(sK3,sK4,sK5)
    | ~ spl159_17 ),
    inference(avatar_component_clause,[],[f4592])).

fof(f4592,plain,
    ( spl159_17
  <=> r1_lattice3(sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl159_17])])).

fof(f20536,plain,
    ( spl159_133
    | ~ spl159_9
    | ~ spl159_34 ),
    inference(avatar_split_clause,[],[f11820,f4774,f4553,f20533])).

fof(f11820,plain,
    ( m1_subset_1(sK8(sK2,sK4,sK5),u1_struct_0(sK3))
    | ~ spl159_9
    | ~ spl159_34 ),
    inference(unit_resulting_resolution,[],[f4555,f4776,f3841])).

fof(f4993,plain,
    ( ~ spl159_46
    | ~ spl159_2
    | ~ spl159_6
    | spl159_12 ),
    inference(avatar_split_clause,[],[f4965,f4568,f4538,f4518,f4990])).

fof(f4568,plain,
    ( spl159_12
  <=> r1_lattice3(sK2,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl159_12])])).

fof(f4965,plain,
    ( ~ r1_orders_2(sK2,sK5,sK8(sK2,sK4,sK5))
    | ~ spl159_2
    | ~ spl159_6
    | spl159_12 ),
    inference(unit_resulting_resolution,[],[f4520,f4540,f4570,f3730])).

fof(f3730,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK8(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3444])).

fof(f4570,plain,
    ( ~ r1_lattice3(sK2,sK4,sK5)
    | spl159_12 ),
    inference(avatar_component_clause,[],[f4568])).

fof(f4832,plain,
    ( spl159_38
    | ~ spl159_2
    | ~ spl159_6
    | spl159_12 ),
    inference(avatar_split_clause,[],[f4640,f4568,f4538,f4518,f4829])).

fof(f4640,plain,
    ( m1_subset_1(sK8(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ spl159_2
    | ~ spl159_6
    | spl159_12 ),
    inference(unit_resulting_resolution,[],[f4520,f4570,f4540,f3728])).

fof(f3728,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3444])).

fof(f4795,plain,
    ( ~ spl159_37
    | ~ spl159_2
    | ~ spl159_6
    | spl159_13 ),
    inference(avatar_split_clause,[],[f4633,f4572,f4538,f4518,f4792])).

fof(f4572,plain,
    ( spl159_13
  <=> r2_lattice3(sK2,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl159_13])])).

fof(f4633,plain,
    ( ~ r1_orders_2(sK2,sK7(sK2,sK4,sK5),sK5)
    | ~ spl159_2
    | ~ spl159_6
    | spl159_13 ),
    inference(unit_resulting_resolution,[],[f4520,f4574,f4540,f3711])).

fof(f3711,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3440])).

fof(f4574,plain,
    ( ~ r2_lattice3(sK2,sK4,sK5)
    | spl159_13 ),
    inference(avatar_component_clause,[],[f4572])).

fof(f4787,plain,
    ( spl159_36
    | ~ spl159_2
    | ~ spl159_6
    | spl159_13 ),
    inference(avatar_split_clause,[],[f4631,f4572,f4538,f4518,f4784])).

fof(f4631,plain,
    ( m1_subset_1(sK7(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ spl159_2
    | ~ spl159_6
    | spl159_13 ),
    inference(unit_resulting_resolution,[],[f4520,f4574,f4540,f3709])).

fof(f3709,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3440])).

fof(f4777,plain,
    ( spl159_34
    | ~ spl159_2
    | ~ spl159_6
    | spl159_12 ),
    inference(avatar_split_clause,[],[f4624,f4568,f4538,f4518,f4774])).

fof(f4624,plain,
    ( r2_hidden(sK8(sK2,sK4,sK5),sK4)
    | ~ spl159_2
    | ~ spl159_6
    | spl159_12 ),
    inference(unit_resulting_resolution,[],[f4520,f4570,f4540,f3729])).

fof(f3729,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3444])).

fof(f4772,plain,
    ( spl159_33
    | ~ spl159_2
    | ~ spl159_6
    | spl159_13 ),
    inference(avatar_split_clause,[],[f4623,f4572,f4538,f4518,f4769])).

fof(f4623,plain,
    ( r2_hidden(sK7(sK2,sK4,sK5),sK4)
    | ~ spl159_2
    | ~ spl159_6
    | spl159_13 ),
    inference(unit_resulting_resolution,[],[f4520,f4574,f4540,f3710])).

fof(f3710,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3440])).

fof(f4620,plain,
    ( spl159_20
    | ~ spl159_2
    | ~ spl159_4 ),
    inference(avatar_split_clause,[],[f4609,f4528,f4518,f4617])).

fof(f4609,plain,
    ( l1_orders_2(sK3)
    | ~ spl159_2
    | ~ spl159_4 ),
    inference(unit_resulting_resolution,[],[f4530,f4520,f3735])).

fof(f3735,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_yellow_0(X1,X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f3094])).

fof(f3094,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2985])).

fof(f2985,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(f4596,plain,
    ( spl159_17
    | spl159_15 ),
    inference(avatar_split_clause,[],[f4479,f4582,f4592])).

fof(f4479,plain,
    ( r2_lattice3(sK3,sK4,sK5)
    | r1_lattice3(sK3,sK4,sK5) ),
    inference(forward_demodulation,[],[f4476,f3694])).

fof(f3694,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f3436])).

fof(f3436,plain,
    ( ( ( ~ r2_lattice3(sK2,sK4,sK5)
        & r2_lattice3(sK3,sK4,sK6) )
      | ( ~ r1_lattice3(sK2,sK4,sK5)
        & r1_lattice3(sK3,sK4,sK6) ) )
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_yellow_0(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f3069,f3435,f3434,f3433,f3432,f3431])).

fof(f3431,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ( ~ r2_lattice3(X0,X2,X3)
                            & r2_lattice3(X1,X2,X4) )
                          | ( ~ r1_lattice3(X0,X2,X3)
                            & r1_lattice3(X1,X2,X4) ) )
                        & X3 = X4
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( ~ r2_lattice3(sK2,X2,X3)
                          & r2_lattice3(X1,X2,X4) )
                        | ( ~ r1_lattice3(sK2,X2,X3)
                          & r1_lattice3(X1,X2,X4) ) )
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(sK2)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3432,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ( ~ r2_lattice3(sK2,X2,X3)
                        & r2_lattice3(X1,X2,X4) )
                      | ( ~ r1_lattice3(sK2,X2,X3)
                        & r1_lattice3(X1,X2,X4) ) )
                    & X3 = X4
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(sK2)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_yellow_0(X1,sK2)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ( ~ r2_lattice3(sK2,X2,X3)
                      & r2_lattice3(sK3,X2,X4) )
                    | ( ~ r1_lattice3(sK2,X2,X3)
                      & r1_lattice3(sK3,X2,X4) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(sK3)) )
              & m1_subset_1(X3,u1_struct_0(sK2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
      & m1_yellow_0(sK3,sK2)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3433,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ( ~ r2_lattice3(sK2,X2,X3)
                    & r2_lattice3(sK3,X2,X4) )
                  | ( ~ r1_lattice3(sK2,X2,X3)
                    & r1_lattice3(sK3,X2,X4) ) )
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(sK3)) )
            & m1_subset_1(X3,u1_struct_0(sK2)) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ( ~ r2_lattice3(sK2,sK4,X3)
                  & r2_lattice3(sK3,sK4,X4) )
                | ( ~ r1_lattice3(sK2,sK4,X3)
                  & r1_lattice3(sK3,sK4,X4) ) )
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(sK3)) )
          & m1_subset_1(X3,u1_struct_0(sK2)) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f3434,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ( ~ r2_lattice3(sK2,sK4,X3)
                & r2_lattice3(sK3,sK4,X4) )
              | ( ~ r1_lattice3(sK2,sK4,X3)
                & r1_lattice3(sK3,sK4,X4) ) )
            & X3 = X4
            & m1_subset_1(X4,u1_struct_0(sK3)) )
        & m1_subset_1(X3,u1_struct_0(sK2)) )
   => ( ? [X4] :
          ( ( ( ~ r2_lattice3(sK2,sK4,sK5)
              & r2_lattice3(sK3,sK4,X4) )
            | ( ~ r1_lattice3(sK2,sK4,sK5)
              & r1_lattice3(sK3,sK4,X4) ) )
          & sK5 = X4
          & m1_subset_1(X4,u1_struct_0(sK3)) )
      & m1_subset_1(sK5,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f3435,plain,
    ( ? [X4] :
        ( ( ( ~ r2_lattice3(sK2,sK4,sK5)
            & r2_lattice3(sK3,sK4,X4) )
          | ( ~ r1_lattice3(sK2,sK4,sK5)
            & r1_lattice3(sK3,sK4,X4) ) )
        & sK5 = X4
        & m1_subset_1(X4,u1_struct_0(sK3)) )
   => ( ( ( ~ r2_lattice3(sK2,sK4,sK5)
          & r2_lattice3(sK3,sK4,sK6) )
        | ( ~ r1_lattice3(sK2,sK4,sK5)
          & r1_lattice3(sK3,sK4,sK6) ) )
      & sK5 = sK6
      & m1_subset_1(sK6,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f3069,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( ~ r2_lattice3(X0,X2,X3)
                          & r2_lattice3(X1,X2,X4) )
                        | ( ~ r1_lattice3(X0,X2,X3)
                          & r1_lattice3(X1,X2,X4) ) )
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3068])).

fof(f3068,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( ~ r2_lattice3(X0,X2,X3)
                          & r2_lattice3(X1,X2,X4) )
                        | ( ~ r1_lattice3(X0,X2,X3)
                          & r1_lattice3(X1,X2,X4) ) )
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3055])).

fof(f3055,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ( X3 = X4
                         => ( ( r2_lattice3(X1,X2,X4)
                             => r2_lattice3(X0,X2,X3) )
                            & ( r1_lattice3(X1,X2,X4)
                             => r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3054])).

fof(f3054,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( X3 = X4
                       => ( ( r2_lattice3(X1,X2,X4)
                           => r2_lattice3(X0,X2,X3) )
                          & ( r1_lattice3(X1,X2,X4)
                           => r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_yellow_0)).

fof(f4476,plain,
    ( r1_lattice3(sK3,sK4,sK5)
    | r2_lattice3(sK3,sK4,sK6) ),
    inference(backward_demodulation,[],[f3695,f3694])).

fof(f3695,plain,
    ( r2_lattice3(sK3,sK4,sK6)
    | r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f3436])).

fof(f4595,plain,
    ( ~ spl159_13
    | spl159_17 ),
    inference(avatar_split_clause,[],[f4478,f4592,f4572])).

fof(f4478,plain,
    ( r1_lattice3(sK3,sK4,sK5)
    | ~ r2_lattice3(sK2,sK4,sK5) ),
    inference(backward_demodulation,[],[f3697,f3694])).

fof(f3697,plain,
    ( ~ r2_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f3436])).

fof(f4585,plain,
    ( ~ spl159_12
    | spl159_15 ),
    inference(avatar_split_clause,[],[f4477,f4582,f4568])).

fof(f4477,plain,
    ( r2_lattice3(sK3,sK4,sK5)
    | ~ r1_lattice3(sK2,sK4,sK5) ),
    inference(backward_demodulation,[],[f3696,f3694])).

fof(f3696,plain,
    ( r2_lattice3(sK3,sK4,sK6)
    | ~ r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f3436])).

fof(f4575,plain,
    ( ~ spl159_12
    | ~ spl159_13 ),
    inference(avatar_split_clause,[],[f3698,f4572,f4568])).

fof(f3698,plain,
    ( ~ r2_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f3436])).

fof(f4556,plain,(
    spl159_9 ),
    inference(avatar_split_clause,[],[f3691,f4553])).

fof(f3691,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f3436])).

fof(f4546,plain,(
    spl159_7 ),
    inference(avatar_split_clause,[],[f4480,f4543])).

fof(f4480,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f3693,f3694])).

fof(f3693,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f3436])).

fof(f4541,plain,(
    spl159_6 ),
    inference(avatar_split_clause,[],[f3692,f4538])).

fof(f3692,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f3436])).

fof(f4531,plain,(
    spl159_4 ),
    inference(avatar_split_clause,[],[f3690,f4528])).

fof(f3690,plain,(
    m1_yellow_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f3436])).

fof(f4521,plain,(
    spl159_2 ),
    inference(avatar_split_clause,[],[f3688,f4518])).

fof(f3688,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3436])).
%------------------------------------------------------------------------------
