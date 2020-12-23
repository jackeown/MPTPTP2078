%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t17_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:45 EDT 2019

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 454 expanded)
%              Number of leaves         :   44 ( 197 expanded)
%              Depth                    :   13
%              Number of atoms          :  857 (2619 expanded)
%              Number of equality atoms :   87 ( 220 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2063,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f157,f167,f204,f218,f222,f226,f228,f239,f241,f261,f268,f461,f463,f543,f564,f629,f633,f732,f1095,f1105,f1601,f1681,f2062])).

fof(f2062,plain,
    ( spl12_10
    | ~ spl12_23
    | ~ spl12_31
    | ~ spl12_1
    | ~ spl12_46
    | spl12_371 ),
    inference(avatar_split_clause,[],[f2061,f1599,f287,f145,f264,f210,f179])).

fof(f179,plain,
    ( spl12_10
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f210,plain,
    ( spl12_23
  <=> ~ l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_23])])).

fof(f264,plain,
    ( spl12_31
  <=> ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).

fof(f145,plain,
    ( spl12_1
  <=> ~ r2_hidden(sK2,k5_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f287,plain,
    ( spl12_46
  <=> k5_waybel_0(sK0,sK1) = a_2_0_waybel_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_46])])).

fof(f1599,plain,
    ( spl12_371
  <=> ~ r2_hidden(sK9(sK2,sK0,k1_tarski(sK1)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_371])])).

fof(f2061,plain,
    ( ~ r2_hidden(sK2,k5_waybel_0(sK0,sK1))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_46
    | ~ spl12_371 ),
    inference(forward_demodulation,[],[f2056,f288])).

fof(f288,plain,
    ( k5_waybel_0(sK0,sK1) = a_2_0_waybel_0(sK0,k1_tarski(sK1))
    | ~ spl12_46 ),
    inference(avatar_component_clause,[],[f287])).

fof(f2056,plain,
    ( ~ r2_hidden(sK2,a_2_0_waybel_0(sK0,k1_tarski(sK1)))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_371 ),
    inference(resolution,[],[f1600,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK9(X0,X1,X2),X2)
            & r1_orders_2(X1,sK8(X0,X1,X2),sK9(X0,X1,X2))
            & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))
            & sK8(X0,X1,X2) = X0
            & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f87,f89,f88])).

fof(f88,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X2)
              & r1_orders_2(X1,X5,X6)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,X2)
            & r1_orders_2(X1,sK8(X0,X1,X2),X6)
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK8(X0,X1,X2) = X0
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK9(X0,X1,X2),X2)
        & r1_orders_2(X1,X5,sK9(X0,X1,X2))
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,X2)
                  & r1_orders_2(X1,X5,X6)
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r1_orders_2(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t17_waybel_0.p',fraenkel_a_2_0_waybel_0)).

fof(f1600,plain,
    ( ~ r2_hidden(sK9(sK2,sK0,k1_tarski(sK1)),k1_tarski(sK1))
    | ~ spl12_371 ),
    inference(avatar_component_clause,[],[f1599])).

fof(f1681,plain,
    ( ~ spl12_0
    | ~ spl12_130
    | spl12_369 ),
    inference(avatar_contradiction_clause,[],[f1678])).

fof(f1678,plain,
    ( $false
    | ~ spl12_0
    | ~ spl12_130
    | ~ spl12_369 ),
    inference(subsumption_resolution,[],[f1597,f1659])).

fof(f1659,plain,
    ( m1_subset_1(sK9(sK2,sK0,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl12_0
    | ~ spl12_130 ),
    inference(resolution,[],[f632,f153])).

fof(f153,plain,
    ( r2_hidden(sK2,k5_waybel_0(sK0,sK1))
    | ~ spl12_0 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl12_0
  <=> r2_hidden(sK2,k5_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f632,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k5_waybel_0(sK0,sK1))
        | m1_subset_1(sK9(X2,sK0,k1_tarski(sK1)),u1_struct_0(sK0)) )
    | ~ spl12_130 ),
    inference(avatar_component_clause,[],[f631])).

fof(f631,plain,
    ( spl12_130
  <=> ! [X2] :
        ( ~ r2_hidden(X2,k5_waybel_0(sK0,sK1))
        | m1_subset_1(sK9(X2,sK0,k1_tarski(sK1)),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_130])])).

fof(f1597,plain,
    ( ~ m1_subset_1(sK9(sK2,sK0,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl12_369 ),
    inference(avatar_component_clause,[],[f1596])).

fof(f1596,plain,
    ( spl12_369
  <=> ~ m1_subset_1(sK9(sK2,sK0,k1_tarski(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_369])])).

fof(f1601,plain,
    ( ~ spl12_369
    | ~ spl12_371
    | ~ spl12_31
    | spl12_100
    | ~ spl12_1
    | ~ spl12_35
    | ~ spl12_0
    | ~ spl12_46
    | ~ spl12_104
    | ~ spl12_128 ),
    inference(avatar_split_clause,[],[f1594,f627,f541,f287,f152,f246,f145,f533,f264,f1599,f1596])).

fof(f533,plain,
    ( spl12_100
  <=> r2_hidden(sK2,a_2_5_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_100])])).

fof(f246,plain,
    ( spl12_35
  <=> ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_35])])).

fof(f541,plain,
    ( spl12_104
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(sK8(X2,sK0,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,a_2_0_waybel_0(sK0,X3))
        | ~ r2_hidden(sK9(X2,sK0,X3),k1_tarski(sK1))
        | r2_hidden(sK8(X2,sK0,X3),a_2_5_waybel_0(sK0,sK1))
        | ~ m1_subset_1(sK9(X2,sK0,X3),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_104])])).

fof(f627,plain,
    ( spl12_128
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k5_waybel_0(sK0,sK1))
        | sK8(X1,sK0,k1_tarski(sK1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_128])])).

fof(f1594,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(sK2,k5_waybel_0(sK0,sK1))
    | r2_hidden(sK2,a_2_5_waybel_0(sK0,sK1))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK9(sK2,sK0,k1_tarski(sK1)),k1_tarski(sK1))
    | ~ m1_subset_1(sK9(sK2,sK0,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl12_0
    | ~ spl12_46
    | ~ spl12_104
    | ~ spl12_128 ),
    inference(forward_demodulation,[],[f1593,f1581])).

fof(f1581,plain,
    ( sK2 = sK8(sK2,sK0,k1_tarski(sK1))
    | ~ spl12_0
    | ~ spl12_128 ),
    inference(resolution,[],[f628,f153])).

fof(f628,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_waybel_0(sK0,sK1))
        | sK8(X1,sK0,k1_tarski(sK1)) = X1 )
    | ~ spl12_128 ),
    inference(avatar_component_clause,[],[f627])).

fof(f1593,plain,
    ( ~ r2_hidden(sK2,k5_waybel_0(sK0,sK1))
    | r2_hidden(sK2,a_2_5_waybel_0(sK0,sK1))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK9(sK2,sK0,k1_tarski(sK1)),k1_tarski(sK1))
    | ~ m1_subset_1(sK8(sK2,sK0,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK9(sK2,sK0,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl12_0
    | ~ spl12_46
    | ~ spl12_104
    | ~ spl12_128 ),
    inference(forward_demodulation,[],[f1591,f288])).

fof(f1591,plain,
    ( r2_hidden(sK2,a_2_5_waybel_0(sK0,sK1))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,a_2_0_waybel_0(sK0,k1_tarski(sK1)))
    | ~ r2_hidden(sK9(sK2,sK0,k1_tarski(sK1)),k1_tarski(sK1))
    | ~ m1_subset_1(sK8(sK2,sK0,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK9(sK2,sK0,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ spl12_0
    | ~ spl12_104
    | ~ spl12_128 ),
    inference(superposition,[],[f542,f1581])).

fof(f542,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK8(X2,sK0,X3),a_2_5_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,a_2_0_waybel_0(sK0,X3))
        | ~ r2_hidden(sK9(X2,sK0,X3),k1_tarski(sK1))
        | ~ m1_subset_1(sK8(X2,sK0,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK9(X2,sK0,X3),u1_struct_0(sK0)) )
    | ~ spl12_104 ),
    inference(avatar_component_clause,[],[f541])).

fof(f1105,plain,
    ( spl12_10
    | ~ spl12_23
    | ~ spl12_25
    | ~ spl12_101
    | spl12_2
    | ~ spl12_26
    | ~ spl12_100
    | ~ spl12_120 ),
    inference(avatar_split_clause,[],[f1022,f588,f533,f216,f155,f963,f213,f210,f179])).

fof(f213,plain,
    ( spl12_25
  <=> ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).

fof(f963,plain,
    ( spl12_101
  <=> ~ r2_hidden(sK2,a_2_5_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_101])])).

fof(f155,plain,
    ( spl12_2
  <=> r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f216,plain,
    ( spl12_26
  <=> ! [X0] :
        ( r2_hidden(sK7(X0,sK0,sK1),k1_tarski(sK1))
        | ~ r2_hidden(X0,a_2_5_waybel_0(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_26])])).

fof(f588,plain,
    ( spl12_120
  <=> sK2 = sK6(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_120])])).

fof(f1022,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ r2_hidden(sK2,a_2_5_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_26
    | ~ spl12_100
    | ~ spl12_120 ),
    inference(forward_demodulation,[],[f1020,f589])).

fof(f589,plain,
    ( sK2 = sK6(sK2,sK0,sK1)
    | ~ spl12_120 ),
    inference(avatar_component_clause,[],[f588])).

fof(f1020,plain,
    ( r1_orders_2(sK0,sK6(sK2,sK0,sK1),sK1)
    | ~ r2_hidden(sK2,a_2_5_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_26
    | ~ spl12_100 ),
    inference(superposition,[],[f126,f951])).

fof(f951,plain,
    ( sK1 = sK7(sK2,sK0,sK1)
    | ~ spl12_26
    | ~ spl12_100 ),
    inference(resolution,[],[f504,f534])).

fof(f534,plain,
    ( r2_hidden(sK2,a_2_5_waybel_0(sK0,sK1))
    | ~ spl12_100 ),
    inference(avatar_component_clause,[],[f533])).

fof(f504,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,a_2_5_waybel_0(sK0,sK1))
        | sK1 = sK7(X1,sK0,sK1) )
    | ~ spl12_26 ),
    inference(resolution,[],[f217,f141])).

fof(f141,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f78,f79])).

fof(f79,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t17_waybel_0.p',d1_tarski)).

fof(f217,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(X0,sK0,sK1),k1_tarski(sK1))
        | ~ r2_hidden(X0,a_2_5_waybel_0(sK0,sK1)) )
    | ~ spl12_26 ),
    inference(avatar_component_clause,[],[f216])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X1,sK6(X0,X1,X2),sK7(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_5_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,k6_domain_1(u1_struct_0(X1),X2))
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK7(X0,X1,X2),k6_domain_1(u1_struct_0(X1),X2))
            & r1_orders_2(X1,sK6(X0,X1,X2),sK7(X0,X1,X2))
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
            & sK6(X0,X1,X2) = X0
            & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f82,f84,f83])).

fof(f83,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,k6_domain_1(u1_struct_0(X1),X2))
              & r1_orders_2(X1,X5,X6)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,k6_domain_1(u1_struct_0(X1),X2))
            & r1_orders_2(X1,sK6(X0,X1,X2),X6)
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK6(X0,X1,X2) = X0
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,k6_domain_1(u1_struct_0(X1),X2))
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK7(X0,X1,X2),k6_domain_1(u1_struct_0(X1),X2))
        & r1_orders_2(X1,X5,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,k6_domain_1(u1_struct_0(X1),X2))
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,k6_domain_1(u1_struct_0(X1),X2))
                  & r1_orders_2(X1,X5,X6)
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,k6_domain_1(u1_struct_0(X1),X2))
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,k6_domain_1(u1_struct_0(X1),X2))
                  & r1_orders_2(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_5_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,k6_domain_1(u1_struct_0(X1),X2))
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_5_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,k6_domain_1(u1_struct_0(X1),X2))
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_5_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,k6_domain_1(u1_struct_0(X1),X2))
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t17_waybel_0.p',fraenkel_a_2_5_waybel_0)).

fof(f1095,plain,
    ( spl12_0
    | ~ spl12_25
    | ~ spl12_35
    | ~ spl12_99
    | ~ spl12_2
    | ~ spl12_44
    | ~ spl12_46 ),
    inference(avatar_split_clause,[],[f1092,f287,f282,f155,f530,f246,f213,f152])).

fof(f530,plain,
    ( spl12_99
  <=> ~ r2_hidden(sK1,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_99])])).

fof(f282,plain,
    ( spl12_44
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK1))
        | r2_hidden(X1,a_2_0_waybel_0(sK0,k1_tarski(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_44])])).

fof(f1092,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(sK2,k5_waybel_0(sK0,sK1))
    | ~ spl12_2
    | ~ spl12_44
    | ~ spl12_46 ),
    inference(resolution,[],[f1090,f156])).

fof(f156,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f155])).

fof(f1090,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X1,X0)
        | ~ r2_hidden(X0,k1_tarski(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X1,k5_waybel_0(sK0,sK1)) )
    | ~ spl12_44
    | ~ spl12_46 ),
    inference(forward_demodulation,[],[f283,f288])).

fof(f283,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_tarski(sK1))
        | r2_hidden(X1,a_2_0_waybel_0(sK0,k1_tarski(sK1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0) )
    | ~ spl12_44 ),
    inference(avatar_component_clause,[],[f282])).

fof(f732,plain,
    ( spl12_10
    | ~ spl12_23
    | ~ spl12_25
    | spl12_120
    | ~ spl12_100 ),
    inference(avatar_split_clause,[],[f726,f533,f588,f213,f210,f179])).

fof(f726,plain,
    ( sK2 = sK6(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_100 ),
    inference(resolution,[],[f534,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_5_waybel_0(X1,X2))
      | sK6(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f633,plain,
    ( spl12_10
    | ~ spl12_23
    | ~ spl12_31
    | spl12_130
    | ~ spl12_46 ),
    inference(avatar_split_clause,[],[f621,f287,f631,f264,f210,f179])).

fof(f621,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k5_waybel_0(sK0,sK1))
        | m1_subset_1(sK9(X2,sK0,k1_tarski(sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_46 ),
    inference(superposition,[],[f131,f288])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f629,plain,
    ( spl12_10
    | ~ spl12_23
    | ~ spl12_31
    | spl12_128
    | ~ spl12_46 ),
    inference(avatar_split_clause,[],[f620,f287,f627,f264,f210,f179])).

fof(f620,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_waybel_0(sK0,sK1))
        | sK8(X1,sK0,k1_tarski(sK1)) = X1
        | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_46 ),
    inference(superposition,[],[f130,f288])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | sK8(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f564,plain,(
    spl12_99 ),
    inference(avatar_contradiction_clause,[],[f562])).

fof(f562,plain,
    ( $false
    | ~ spl12_99 ),
    inference(resolution,[],[f531,f140])).

fof(f140,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f531,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ spl12_99 ),
    inference(avatar_component_clause,[],[f530])).

fof(f543,plain,
    ( spl12_10
    | ~ spl12_23
    | spl12_104
    | ~ spl12_28 ),
    inference(avatar_split_clause,[],[f528,f220,f541,f210,f179])).

fof(f220,plain,
    ( spl12_28
  <=> ! [X1,X2] :
        ( ~ r2_hidden(X1,k1_tarski(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X2,a_2_5_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).

fof(f528,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK8(X2,sK0,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK9(X2,sK0,X3),u1_struct_0(sK0))
        | r2_hidden(sK8(X2,sK0,X3),a_2_5_waybel_0(sK0,sK1))
        | ~ r2_hidden(sK9(X2,sK0,X3),k1_tarski(sK1))
        | ~ r2_hidden(X2,a_2_0_waybel_0(sK0,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_28 ),
    inference(resolution,[],[f221,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X1,sK8(X0,X1,X2),sK9(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f221,plain,
    ( ! [X2,X1] :
        ( ~ r1_orders_2(sK0,X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X2,a_2_5_waybel_0(sK0,sK1))
        | ~ r2_hidden(X1,k1_tarski(sK1)) )
    | ~ spl12_28 ),
    inference(avatar_component_clause,[],[f220])).

fof(f463,plain,
    ( spl12_10
    | ~ spl12_23
    | spl12_46
    | ~ spl12_6
    | ~ spl12_30 ),
    inference(avatar_split_clause,[],[f462,f224,f165,f287,f210,f179])).

fof(f165,plain,
    ( spl12_6
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f224,plain,
    ( spl12_30
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f462,plain,
    ( k5_waybel_0(sK0,sK1) = a_2_0_waybel_0(sK0,k1_tarski(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_6
    | ~ spl12_30 ),
    inference(forward_demodulation,[],[f457,f205])).

fof(f205,plain,
    ( k5_waybel_0(sK0,sK1) = k3_waybel_0(sK0,k1_tarski(sK1))
    | ~ spl12_6 ),
    inference(backward_demodulation,[],[f166,f160])).

fof(f160,plain,(
    k5_waybel_0(sK0,sK1) = k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(global_subsumption,[],[f95,f96,f158])).

fof(f158,plain,
    ( k5_waybel_0(sK0,sK1) = k3_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f97,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t17_waybel_0.p',d17_waybel_0)).

fof(f97,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,
    ( ( ~ r1_orders_2(sK0,sK2,sK1)
      | ~ r2_hidden(sK2,k5_waybel_0(sK0,sK1)) )
    & ( r1_orders_2(sK0,sK2,sK1)
      | r2_hidden(sK2,k5_waybel_0(sK0,sK1)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f67,f70,f69,f68])).

fof(f68,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_orders_2(X0,X2,X1)
                  | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) )
                & ( r1_orders_2(X0,X2,X1)
                  | r2_hidden(X2,k5_waybel_0(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(sK0,X2,X1)
                | ~ r2_hidden(X2,k5_waybel_0(sK0,X1)) )
              & ( r1_orders_2(sK0,X2,X1)
                | r2_hidden(X2,k5_waybel_0(sK0,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X2,X1)
                | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) )
              & ( r1_orders_2(X0,X2,X1)
                | r2_hidden(X2,k5_waybel_0(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r1_orders_2(X0,X2,sK1)
              | ~ r2_hidden(X2,k5_waybel_0(X0,sK1)) )
            & ( r1_orders_2(X0,X2,sK1)
              | r2_hidden(X2,k5_waybel_0(X0,sK1)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_orders_2(X0,X2,X1)
            | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) )
          & ( r1_orders_2(X0,X2,X1)
            | r2_hidden(X2,k5_waybel_0(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r1_orders_2(X0,sK2,X1)
          | ~ r2_hidden(sK2,k5_waybel_0(X0,X1)) )
        & ( r1_orders_2(X0,sK2,X1)
          | r2_hidden(sK2,k5_waybel_0(X0,X1)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X2,X1)
                | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) )
              & ( r1_orders_2(X0,X2,X1)
                | r2_hidden(X2,k5_waybel_0(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X2,X1)
                | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) )
              & ( r1_orders_2(X0,X2,X1)
                | r2_hidden(X2,k5_waybel_0(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <~> r1_orders_2(X0,X2,X1) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <~> r1_orders_2(X0,X2,X1) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k5_waybel_0(X0,X1))
                <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t17_waybel_0.p',t17_waybel_0)).

fof(f96,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f95,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f166,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f165])).

fof(f457,plain,
    ( k3_waybel_0(sK0,k1_tarski(sK1)) = a_2_0_waybel_0(sK0,k1_tarski(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_30 ),
    inference(resolution,[],[f225,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k3_waybel_0(X0,X1) = a_2_0_waybel_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_waybel_0(X0,X1) = a_2_0_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_waybel_0(X0,X1) = a_2_0_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_waybel_0(X0,X1) = a_2_0_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t17_waybel_0.p',t14_waybel_0)).

fof(f225,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_30 ),
    inference(avatar_component_clause,[],[f224])).

fof(f461,plain,
    ( spl12_10
    | ~ spl12_23
    | spl12_44
    | ~ spl12_30 ),
    inference(avatar_split_clause,[],[f456,f224,f282,f210,f179])).

fof(f456,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_tarski(sK1))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,a_2_0_waybel_0(sK0,k1_tarski(sK1)))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_30 ),
    inference(resolution,[],[f225,f143])).

fof(f143,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X4,X2)
      | ~ r1_orders_2(X1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(X3,a_2_0_waybel_0(X1,X2))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f134])).

fof(f134,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_waybel_0(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r1_orders_2(X1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f268,plain,(
    spl12_35 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | ~ spl12_35 ),
    inference(subsumption_resolution,[],[f98,f247])).

fof(f247,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl12_35 ),
    inference(avatar_component_clause,[],[f246])).

fof(f98,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f71])).

fof(f261,plain,(
    spl12_23 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | ~ spl12_23 ),
    inference(subsumption_resolution,[],[f96,f211])).

fof(f211,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl12_23 ),
    inference(avatar_component_clause,[],[f210])).

fof(f241,plain,(
    ~ spl12_10 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl12_10 ),
    inference(subsumption_resolution,[],[f95,f180])).

fof(f180,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f179])).

fof(f239,plain,
    ( spl12_10
    | ~ spl12_13
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f236,f162,f182,f179])).

fof(f182,plain,
    ( spl12_13
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f162,plain,
    ( spl12_4
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f236,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_4 ),
    inference(resolution,[],[f163,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t17_waybel_0.p',fc2_struct_0)).

fof(f163,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f162])).

fof(f228,plain,(
    spl12_25 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl12_25 ),
    inference(subsumption_resolution,[],[f97,f214])).

fof(f214,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl12_25 ),
    inference(avatar_component_clause,[],[f213])).

fof(f226,plain,
    ( spl12_4
    | ~ spl12_25
    | spl12_30
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f208,f165,f224,f213,f162])).

fof(f208,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl12_6 ),
    inference(superposition,[],[f112,f166])).

fof(f112,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t17_waybel_0.p',dt_k6_domain_1)).

fof(f222,plain,
    ( spl12_10
    | ~ spl12_23
    | ~ spl12_25
    | spl12_28
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f207,f165,f220,f213,f210,f179])).

fof(f207,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X1,k1_tarski(sK1))
        | r2_hidden(X2,a_2_5_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_6 ),
    inference(superposition,[],[f142,f166])).

fof(f142,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r2_hidden(X4,k6_domain_1(u1_struct_0(X1),X2))
      | r2_hidden(X3,a_2_5_waybel_0(X1,X2))
      | ~ r1_orders_2(X1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_5_waybel_0(X1,X2))
      | ~ r2_hidden(X4,k6_domain_1(u1_struct_0(X1),X2))
      | ~ r1_orders_2(X1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f218,plain,
    ( spl12_10
    | ~ spl12_23
    | ~ spl12_25
    | spl12_26
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f206,f165,f216,f213,f210,f179])).

fof(f206,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(X0,sK0,sK1),k1_tarski(sK1))
        | ~ r2_hidden(X0,a_2_5_waybel_0(sK0,sK1))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_6 ),
    inference(superposition,[],[f127,f166])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),k6_domain_1(u1_struct_0(X1),X2))
      | ~ r2_hidden(X0,a_2_5_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f204,plain,(
    spl12_13 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f96,f193])).

fof(f193,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl12_13 ),
    inference(resolution,[],[f183,f102])).

fof(f102,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t17_waybel_0.p',dt_l1_orders_2)).

fof(f183,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl12_13 ),
    inference(avatar_component_clause,[],[f182])).

fof(f167,plain,
    ( spl12_4
    | spl12_6 ),
    inference(avatar_split_clause,[],[f159,f165,f162])).

fof(f159,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f97,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t17_waybel_0.p',redefinition_k6_domain_1)).

fof(f157,plain,
    ( spl12_0
    | spl12_2 ),
    inference(avatar_split_clause,[],[f99,f155,f152])).

fof(f99,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_hidden(sK2,k5_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f71])).

fof(f150,plain,
    ( ~ spl12_1
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f100,f148,f145])).

fof(f148,plain,
    ( spl12_3
  <=> ~ r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f100,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r2_hidden(sK2,k5_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f71])).
%------------------------------------------------------------------------------
