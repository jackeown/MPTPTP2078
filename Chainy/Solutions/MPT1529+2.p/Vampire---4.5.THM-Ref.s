%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1529+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:22 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 256 expanded)
%              Number of leaves         :   21 ( 110 expanded)
%              Depth                    :   13
%              Number of atoms          :  490 (1590 expanded)
%              Number of equality atoms :   36 ( 117 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3421,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3118,f3121,f3124,f3125,f3129,f3133,f3137,f3246,f3256,f3271,f3311,f3312,f3334,f3403,f3420])).

fof(f3420,plain,
    ( ~ spl10_3
    | spl10_4
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_23 ),
    inference(avatar_contradiction_clause,[],[f3419])).

fof(f3419,plain,
    ( $false
    | ~ spl10_3
    | spl10_4
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_23 ),
    inference(subsumption_resolution,[],[f3418,f3117])).

fof(f3117,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f3116])).

fof(f3116,plain,
    ( spl10_4
  <=> r2_lattice3(sK0,k1_tarski(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

% (7893)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_4 on theBenchmark
% (7894)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_48 on theBenchmark
fof(f3418,plain,
    ( r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_23 ),
    inference(subsumption_resolution,[],[f3416,f3123])).

fof(f3123,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f3113])).

% (7892)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
fof(f3113,plain,
    ( spl10_3
  <=> r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f3416,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_23 ),
    inference(superposition,[],[f3233,f3333])).

fof(f3333,plain,
    ( sK2 = sK3(sK0,k1_tarski(sK2),sK1)
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f3332])).

fof(f3332,plain,
    ( spl10_23
  <=> sK2 = sK3(sK0,k1_tarski(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f3233,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,sK3(sK0,X1,sK1),sK1)
        | r2_lattice3(sK0,X1,sK1) )
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(resolution,[],[f3211,f3132])).

fof(f3132,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f3131])).

fof(f3131,plain,
    ( spl10_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f3211,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3(sK0,X0,X1),X1)
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl10_7 ),
    inference(resolution,[],[f3052,f3136])).

fof(f3136,plain,
    ( l1_orders_2(sK0)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f3135])).

fof(f3135,plain,
    ( spl10_7
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f3052,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f3004])).

fof(f3004,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                & r2_hidden(sK3(X0,X1,X2),X1)
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f3002,f3003])).

fof(f3003,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3002,plain,(
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
    inference(rectify,[],[f3001])).

fof(f3001,plain,(
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
    inference(nnf_transformation,[],[f2981])).

fof(f2981,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f2980])).

fof(f2980,plain,(
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

fof(f3403,plain,
    ( spl10_15
    | spl10_4
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f3402,f3135,f3131,f3116,f3249])).

fof(f3249,plain,
    ( spl10_15
  <=> r2_hidden(sK3(sK0,k1_tarski(sK2),sK1),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f3402,plain,
    ( r2_hidden(sK3(sK0,k1_tarski(sK2),sK1),k1_tarski(sK2))
    | spl10_4
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(resolution,[],[f3117,f3201])).

fof(f3201,plain,
    ( ! [X1] :
        ( r2_lattice3(sK0,X1,sK1)
        | r2_hidden(sK3(sK0,X1,sK1),X1) )
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(resolution,[],[f3198,f3132])).

fof(f3198,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(sK3(sK0,X0,X1),X0)
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl10_7 ),
    inference(resolution,[],[f3051,f3136])).

fof(f3051,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f3004])).

fof(f3334,plain,
    ( spl10_23
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f3323,f3249,f3332])).

fof(f3323,plain,
    ( sK2 = sK3(sK0,k1_tarski(sK2),sK1)
    | ~ spl10_15 ),
    inference(resolution,[],[f3250,f3104])).

fof(f3104,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f3080])).

fof(f3080,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3025])).

fof(f3025,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f3023,f3024])).

fof(f3024,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f3023,plain,(
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
    inference(rectify,[],[f3022])).

fof(f3022,plain,(
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
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f3250,plain,
    ( r2_hidden(sK3(sK0,k1_tarski(sK2),sK1),k1_tarski(sK2))
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f3249])).

fof(f3312,plain,
    ( spl10_2
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f3302,f3269,f3135,f3131,f3107,f3110])).

fof(f3110,plain,
    ( spl10_2
  <=> r1_lattice3(sK0,k1_tarski(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f3107,plain,
    ( spl10_1
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f3269,plain,
    ( spl10_19
  <=> sK2 = sK4(sK0,k1_tarski(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f3302,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_19 ),
    inference(superposition,[],[f3277,f3270])).

fof(f3270,plain,
    ( sK2 = sK4(sK0,k1_tarski(sK2),sK1)
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f3269])).

fof(f3277,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,sK1,sK4(sK0,X1,sK1))
        | r1_lattice3(sK0,X1,sK1) )
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(resolution,[],[f3226,f3132])).

fof(f3226,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK4(sK0,X1,X0))
        | r1_lattice3(sK0,X1,X0) )
    | ~ spl10_7 ),
    inference(resolution,[],[f3061,f3136])).

fof(f3061,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f3011])).

fof(f3011,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3009,f3010])).

fof(f3010,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3009,plain,(
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
    inference(rectify,[],[f3008])).

fof(f3008,plain,(
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
    inference(nnf_transformation,[],[f2985])).

fof(f2985,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f2984])).

fof(f2984,plain,(
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

fof(f3311,plain,
    ( spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f3309])).

fof(f3309,plain,
    ( $false
    | spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f3136,f3103,f3122,f3132,f3128,f3114,f3049])).

fof(f3049,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2) ) ),
    inference(cnf_transformation,[],[f3004])).

fof(f3114,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f3113])).

fof(f3128,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f3127])).

fof(f3127,plain,
    ( spl10_5
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f3122,plain,
    ( r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f3116])).

fof(f3103,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f3102])).

fof(f3102,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f3081])).

fof(f3081,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3025])).

fof(f3271,plain,
    ( spl10_19
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f3260,f3254,f3269])).

fof(f3254,plain,
    ( spl10_16
  <=> r2_hidden(sK4(sK0,k1_tarski(sK2),sK1),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f3260,plain,
    ( sK2 = sK4(sK0,k1_tarski(sK2),sK1)
    | ~ spl10_16 ),
    inference(resolution,[],[f3255,f3104])).

fof(f3255,plain,
    ( r2_hidden(sK4(sK0,k1_tarski(sK2),sK1),k1_tarski(sK2))
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f3254])).

fof(f3256,plain,
    ( spl10_16
    | spl10_2
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f3252,f3135,f3131,f3110,f3254])).

fof(f3252,plain,
    ( r2_hidden(sK4(sK0,k1_tarski(sK2),sK1),k1_tarski(sK2))
    | spl10_2
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(resolution,[],[f3111,f3214])).

fof(f3214,plain,
    ( ! [X1] :
        ( r1_lattice3(sK0,X1,sK1)
        | r2_hidden(sK4(sK0,X1,sK1),X1) )
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(resolution,[],[f3203,f3132])).

fof(f3203,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(sK4(sK0,X0,X1),X0)
        | r1_lattice3(sK0,X0,X1) )
    | ~ spl10_7 ),
    inference(resolution,[],[f3060,f3136])).

fof(f3060,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f3011])).

fof(f3111,plain,
    ( ~ r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f3110])).

fof(f3246,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f3243])).

fof(f3243,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f3136,f3103,f3119,f3108,f3132,f3128,f3058])).

fof(f3058,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4) ) ),
    inference(cnf_transformation,[],[f3011])).

fof(f3108,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f3107])).

fof(f3119,plain,
    ( r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f3110])).

fof(f3137,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f3030,f3135])).

fof(f3030,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3000])).

fof(f3000,plain,
    ( ( ( ~ r2_lattice3(sK0,k1_tarski(sK2),sK1)
        & r1_orders_2(sK0,sK2,sK1) )
      | ( ~ r1_orders_2(sK0,sK2,sK1)
        & r2_lattice3(sK0,k1_tarski(sK2),sK1) )
      | ( ~ r1_lattice3(sK0,k1_tarski(sK2),sK1)
        & r1_orders_2(sK0,sK1,sK2) )
      | ( ~ r1_orders_2(sK0,sK1,sK2)
        & r1_lattice3(sK0,k1_tarski(sK2),sK1) ) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2979,f2999,f2998,f2997])).

fof(f2997,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ( ~ r2_lattice3(X0,k1_tarski(X2),X1)
                    & r1_orders_2(X0,X2,X1) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & r2_lattice3(X0,k1_tarski(X2),X1) )
                  | ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
                    & r1_orders_2(X0,X1,X2) )
                  | ( ~ r1_orders_2(X0,X1,X2)
                    & r1_lattice3(X0,k1_tarski(X2),X1) ) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r2_lattice3(sK0,k1_tarski(X2),X1)
                  & r1_orders_2(sK0,X2,X1) )
                | ( ~ r1_orders_2(sK0,X2,X1)
                  & r2_lattice3(sK0,k1_tarski(X2),X1) )
                | ( ~ r1_lattice3(sK0,k1_tarski(X2),X1)
                  & r1_orders_2(sK0,X1,X2) )
                | ( ~ r1_orders_2(sK0,X1,X2)
                  & r1_lattice3(sK0,k1_tarski(X2),X1) ) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2998,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ( ~ r2_lattice3(sK0,k1_tarski(X2),X1)
                & r1_orders_2(sK0,X2,X1) )
              | ( ~ r1_orders_2(sK0,X2,X1)
                & r2_lattice3(sK0,k1_tarski(X2),X1) )
              | ( ~ r1_lattice3(sK0,k1_tarski(X2),X1)
                & r1_orders_2(sK0,X1,X2) )
              | ( ~ r1_orders_2(sK0,X1,X2)
                & r1_lattice3(sK0,k1_tarski(X2),X1) ) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ( ~ r2_lattice3(sK0,k1_tarski(X2),sK1)
              & r1_orders_2(sK0,X2,sK1) )
            | ( ~ r1_orders_2(sK0,X2,sK1)
              & r2_lattice3(sK0,k1_tarski(X2),sK1) )
            | ( ~ r1_lattice3(sK0,k1_tarski(X2),sK1)
              & r1_orders_2(sK0,sK1,X2) )
            | ( ~ r1_orders_2(sK0,sK1,X2)
              & r1_lattice3(sK0,k1_tarski(X2),sK1) ) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2999,plain,
    ( ? [X2] :
        ( ( ( ~ r2_lattice3(sK0,k1_tarski(X2),sK1)
            & r1_orders_2(sK0,X2,sK1) )
          | ( ~ r1_orders_2(sK0,X2,sK1)
            & r2_lattice3(sK0,k1_tarski(X2),sK1) )
          | ( ~ r1_lattice3(sK0,k1_tarski(X2),sK1)
            & r1_orders_2(sK0,sK1,X2) )
          | ( ~ r1_orders_2(sK0,sK1,X2)
            & r1_lattice3(sK0,k1_tarski(X2),sK1) ) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ( ~ r2_lattice3(sK0,k1_tarski(sK2),sK1)
          & r1_orders_2(sK0,sK2,sK1) )
        | ( ~ r1_orders_2(sK0,sK2,sK1)
          & r2_lattice3(sK0,k1_tarski(sK2),sK1) )
        | ( ~ r1_lattice3(sK0,k1_tarski(sK2),sK1)
          & r1_orders_2(sK0,sK1,sK2) )
        | ( ~ r1_orders_2(sK0,sK1,sK2)
          & r1_lattice3(sK0,k1_tarski(sK2),sK1) ) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2979,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r2_lattice3(X0,k1_tarski(X2),X1)
                  & r1_orders_2(X0,X2,X1) )
                | ( ~ r1_orders_2(X0,X2,X1)
                  & r2_lattice3(X0,k1_tarski(X2),X1) )
                | ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
                  & r1_orders_2(X0,X1,X2) )
                | ( ~ r1_orders_2(X0,X1,X2)
                  & r1_lattice3(X0,k1_tarski(X2),X1) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2970])).

fof(f2970,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f2969])).

fof(f2969,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_0)).

fof(f3133,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f3031,f3131])).

fof(f3031,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3000])).

fof(f3129,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f3032,f3127])).

fof(f3032,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3000])).

fof(f3125,plain,
    ( spl10_2
    | spl10_1
    | spl10_4
    | spl10_3 ),
    inference(avatar_split_clause,[],[f3033,f3113,f3116,f3107,f3110])).

fof(f3033,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k1_tarski(sK2),sK1) ),
    inference(cnf_transformation,[],[f3000])).

fof(f3124,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | spl10_4
    | spl10_3 ),
    inference(avatar_split_clause,[],[f3036,f3113,f3116,f3110,f3107])).

fof(f3036,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3000])).

fof(f3121,plain,
    ( spl10_2
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f3045,f3116,f3113,f3107,f3110])).

fof(f3045,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k1_tarski(sK2),sK1) ),
    inference(cnf_transformation,[],[f3000])).

fof(f3118,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f3048,f3116,f3113,f3110,f3107])).

fof(f3048,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3000])).
%------------------------------------------------------------------------------
