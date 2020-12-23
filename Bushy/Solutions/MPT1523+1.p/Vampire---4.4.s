%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t1_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:38 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 576 expanded)
%              Number of leaves         :   21 ( 283 expanded)
%              Depth                    :   21
%              Number of atoms          :  565 (7018 expanded)
%              Number of equality atoms :   84 (1599 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f558,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f134,f135,f266,f279,f280,f502,f523,f555])).

fof(f555,plain,
    ( ~ spl10_0
    | spl10_3
    | ~ spl10_6
    | ~ spl10_22 ),
    inference(avatar_contradiction_clause,[],[f554])).

fof(f554,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f553,f136])).

fof(f136,plain,(
    sP8(sK0) ),
    inference(resolution,[],[f70,f103])).

fof(f103,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP8(X0) ) ),
    inference(cnf_transformation,[],[f103_D])).

fof(f103_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,u1_struct_0(X0))
    <=> ~ sP8(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).

fof(f70,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( ( ( ~ r2_orders_2(sK1,sK4,sK5)
        & r2_orders_2(sK0,sK2,sK3) )
      | ( ~ r1_orders_2(sK1,sK4,sK5)
        & r1_orders_2(sK0,sK2,sK3) ) )
    & sK3 = sK5
    & sK2 = sK4
    & m1_subset_1(sK5,u1_struct_0(sK1))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f33,f58,f57,f56,f55,f54,f53])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ( ~ r2_orders_2(X1,X4,X5)
                                & r2_orders_2(X0,X2,X3) )
                              | ( ~ r1_orders_2(X1,X4,X5)
                                & r1_orders_2(X0,X2,X3) ) )
                            & X3 = X5
                            & X2 = X4
                            & m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( ~ r2_orders_2(X1,X4,X5)
                              & r2_orders_2(sK0,X2,X3) )
                            | ( ~ r1_orders_2(X1,X4,X5)
                              & r1_orders_2(sK0,X2,X3) ) )
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( ~ r2_orders_2(X1,X4,X5)
                              & r2_orders_2(X0,X2,X3) )
                            | ( ~ r1_orders_2(X1,X4,X5)
                              & r1_orders_2(X0,X2,X3) ) )
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ( ~ r2_orders_2(sK1,X4,X5)
                            & r2_orders_2(X0,X2,X3) )
                          | ( ~ r1_orders_2(sK1,X4,X5)
                            & r1_orders_2(X0,X2,X3) ) )
                        & X3 = X5
                        & X2 = X4
                        & m1_subset_1(X5,u1_struct_0(sK1)) )
                    & m1_subset_1(X4,u1_struct_0(sK1)) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        & l1_orders_2(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ( ~ r2_orders_2(X1,X4,X5)
                          & r2_orders_2(X0,X2,X3) )
                        | ( ~ r1_orders_2(X1,X4,X5)
                          & r1_orders_2(X0,X2,X3) ) )
                      & X3 = X5
                      & X2 = X4
                      & m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ( ~ r2_orders_2(X1,X4,X5)
                        & r2_orders_2(X0,sK2,X3) )
                      | ( ~ r1_orders_2(X1,X4,X5)
                        & r1_orders_2(X0,sK2,X3) ) )
                    & X3 = X5
                    & sK2 = X4
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ( ~ r2_orders_2(X1,X4,X5)
                      & r2_orders_2(X0,X2,X3) )
                    | ( ~ r1_orders_2(X1,X4,X5)
                      & r1_orders_2(X0,X2,X3) ) )
                  & X3 = X5
                  & X2 = X4
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ( ~ r2_orders_2(X1,X4,X5)
                    & r2_orders_2(X0,X2,sK3) )
                  | ( ~ r1_orders_2(X1,X4,X5)
                    & r1_orders_2(X0,X2,sK3) ) )
                & sK3 = X5
                & X2 = X4
                & m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ( ~ r2_orders_2(X1,X4,X5)
                  & r2_orders_2(X0,X2,X3) )
                | ( ~ r1_orders_2(X1,X4,X5)
                  & r1_orders_2(X0,X2,X3) ) )
              & X3 = X5
              & X2 = X4
              & m1_subset_1(X5,u1_struct_0(X1)) )
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ? [X5] :
            ( ( ( ~ r2_orders_2(X1,sK4,X5)
                & r2_orders_2(X0,X2,X3) )
              | ( ~ r1_orders_2(X1,sK4,X5)
                & r1_orders_2(X0,X2,X3) ) )
            & X3 = X5
            & sK4 = X2
            & m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ( ~ r2_orders_2(X1,X4,X5)
              & r2_orders_2(X0,X2,X3) )
            | ( ~ r1_orders_2(X1,X4,X5)
              & r1_orders_2(X0,X2,X3) ) )
          & X3 = X5
          & X2 = X4
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ( ( ~ r2_orders_2(X1,X4,sK5)
            & r2_orders_2(X0,X2,X3) )
          | ( ~ r1_orders_2(X1,X4,sK5)
            & r1_orders_2(X0,X2,X3) ) )
        & sK5 = X3
        & X2 = X4
        & m1_subset_1(sK5,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( ~ r2_orders_2(X1,X4,X5)
                              & r2_orders_2(X0,X2,X3) )
                            | ( ~ r1_orders_2(X1,X4,X5)
                              & r1_orders_2(X0,X2,X3) ) )
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( ~ r2_orders_2(X1,X4,X5)
                              & r2_orders_2(X0,X2,X3) )
                            | ( ~ r1_orders_2(X1,X4,X5)
                              & r1_orders_2(X0,X2,X3) ) )
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ( ( X3 = X5
                                  & X2 = X4 )
                               => ( ( r2_orders_2(X0,X2,X3)
                                   => r2_orders_2(X1,X4,X5) )
                                  & ( r1_orders_2(X0,X2,X3)
                                   => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => ( ( r2_orders_2(X0,X2,X3)
                                 => r2_orders_2(X1,X4,X5) )
                                & ( r1_orders_2(X0,X2,X3)
                                 => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t1_yellow_0.p',t1_yellow_0)).

fof(f553,plain,
    ( ~ sP8(sK0)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f552,f67])).

fof(f67,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f552,plain,
    ( ~ l1_orders_2(sK0)
    | ~ sP8(sK0)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f546,f70])).

fof(f546,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ sP8(sK0)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_22 ),
    inference(resolution,[],[f538,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ sP8(X0) ) ),
    inference(general_splitting,[],[f98,f103_D])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => ~ r2_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t1_yellow_0.p',irreflexivity_r2_orders_2)).

fof(f538,plain,
    ( r2_orders_2(sK0,sK2,sK2)
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_22 ),
    inference(backward_demodulation,[],[f533,f133])).

fof(f133,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl10_6
  <=> r2_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f533,plain,
    ( sK2 = sK3
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f532,f70])).

fof(f532,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK2 = sK3
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_22 ),
    inference(forward_demodulation,[],[f531,f330])).

fof(f330,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl10_22 ),
    inference(equality_resolution,[],[f219])).

fof(f219,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X2 )
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl10_22
  <=> ! [X3,X2] :
        ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f531,plain,
    ( sK2 = sK3
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f530,f71])).

fof(f71,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f59])).

fof(f530,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | sK2 = sK3
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_3
    | ~ spl10_22 ),
    inference(forward_demodulation,[],[f529,f330])).

fof(f529,plain,
    ( sK2 = sK3
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f528,f68])).

fof(f68,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f528,plain,
    ( sK2 = sK3
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl10_0
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f526,f507])).

fof(f507,plain,
    ( ~ r2_orders_2(sK1,sK2,sK3)
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f506,f74])).

fof(f74,plain,(
    sK2 = sK4 ),
    inference(cnf_transformation,[],[f59])).

fof(f506,plain,
    ( ~ r2_orders_2(sK1,sK4,sK3)
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f119,f75])).

fof(f75,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f59])).

fof(f119,plain,
    ( ~ r2_orders_2(sK1,sK4,sK5)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl10_3
  <=> ~ r2_orders_2(sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f526,plain,
    ( sK2 = sK3
    | r2_orders_2(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl10_0 ),
    inference(resolution,[],[f525,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | X1 = X2
      | r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t1_yellow_0.p',d10_orders_2)).

fof(f525,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | ~ spl10_0 ),
    inference(forward_demodulation,[],[f524,f74])).

fof(f524,plain,
    ( r1_orders_2(sK1,sK4,sK3)
    | ~ spl10_0 ),
    inference(forward_demodulation,[],[f110,f75])).

fof(f110,plain,
    ( r1_orders_2(sK1,sK4,sK5)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl10_0
  <=> r1_orders_2(sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f523,plain,
    ( spl10_1
    | ~ spl10_6
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f521,f165])).

fof(f165,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f164,f74])).

fof(f164,plain,
    ( ~ r1_orders_2(sK1,sK4,sK3)
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f113,f75])).

fof(f113,plain,
    ( ~ r1_orders_2(sK1,sK4,sK5)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl10_1
  <=> ~ r1_orders_2(sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f521,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | ~ spl10_6
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f520,f70])).

fof(f520,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK1,sK2,sK3)
    | ~ spl10_6
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f513,f71])).

fof(f513,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK1,sK2,sK3)
    | ~ spl10_6
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(resolution,[],[f512,f390])).

fof(f390,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK1,X0,X1) )
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(forward_demodulation,[],[f389,f330])).

fof(f389,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(forward_demodulation,[],[f388,f330])).

fof(f388,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f386,f68])).

fof(f386,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl10_24 ),
    inference(superposition,[],[f84,f383])).

fof(f383,plain,
    ( u1_orders_2(sK0) = u1_orders_2(sK1)
    | ~ spl10_24 ),
    inference(equality_resolution,[],[f223])).

fof(f223,plain,
    ( ! [X6,X7] :
        ( g1_orders_2(X6,X7) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK1) = X7 )
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl10_24
  <=> ! [X7,X6] :
        ( g1_orders_2(X6,X7) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK1) = X7 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t1_yellow_0.p',d9_orders_2)).

fof(f512,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f511,f67])).

fof(f511,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f510,f70])).

fof(f510,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f509,f71])).

fof(f509,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_6 ),
    inference(resolution,[],[f505,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f505,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f504,f67])).

fof(f504,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ l1_orders_2(sK0)
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f503,f70])).

fof(f503,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f487,f71])).

fof(f487,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_6 ),
    inference(resolution,[],[f133,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f502,plain,
    ( spl10_1
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(avatar_contradiction_clause,[],[f501])).

fof(f501,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f500,f165])).

fof(f500,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f499,f70])).

fof(f499,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK1,sK2,sK3)
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f492,f71])).

fof(f492,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK1,sK2,sK3)
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(resolution,[],[f180,f390])).

fof(f180,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f179,f67])).

fof(f179,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f178,f70])).

fof(f178,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f167,f71])).

fof(f167,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_4 ),
    inference(resolution,[],[f126,f83])).

fof(f126,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl10_4
  <=> r1_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f280,plain,
    ( ~ spl10_21
    | spl10_24 ),
    inference(avatar_split_clause,[],[f278,f222,f215])).

fof(f215,plain,
    ( spl10_21
  <=> ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f278,plain,(
    ! [X6,X7] :
      ( g1_orders_2(X6,X7) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_orders_2(sK1) = X7
      | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ) ),
    inference(superposition,[],[f95,f69])).

fof(f69,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t1_yellow_0.p',free_g1_orders_2)).

fof(f279,plain,
    ( ~ spl10_21
    | spl10_22 ),
    inference(avatar_split_clause,[],[f276,f218,f215])).

fof(f276,plain,(
    ! [X2,X3] :
      ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK1) = X2
      | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ) ),
    inference(superposition,[],[f94,f69])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f266,plain,(
    spl10_21 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f264,f68])).

fof(f264,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl10_21 ),
    inference(resolution,[],[f216,f81])).

fof(f81,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t1_yellow_0.p',dt_u1_orders_2)).

fof(f216,plain,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f215])).

fof(f135,plain,
    ( spl10_4
    | spl10_6 ),
    inference(avatar_split_clause,[],[f76,f132,f125])).

fof(f76,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f134,plain,
    ( ~ spl10_1
    | spl10_6 ),
    inference(avatar_split_clause,[],[f77,f132,f112])).

fof(f77,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f120,plain,
    ( ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f79,f118,f112])).

fof(f79,plain,
    ( ~ r2_orders_2(sK1,sK4,sK5)
    | ~ r1_orders_2(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
