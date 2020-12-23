%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_6__t20_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:54 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 181 expanded)
%              Number of leaves         :   20 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :  361 ( 920 expanded)
%              Number of equality atoms :   25 ( 121 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f584,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f115,f119,f123,f137,f141,f149,f157,f163,f167,f171,f175,f179,f183,f205,f583])).

fof(f583,plain,
    ( ~ spl13_8
    | spl13_13
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_32 ),
    inference(avatar_contradiction_clause,[],[f582])).

fof(f582,plain,
    ( $false
    | ~ spl13_8
    | ~ spl13_13
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_32 ),
    inference(subsumption_resolution,[],[f581,f148])).

fof(f148,plain,
    ( ~ r1_orders_2(sK1,sK3,sK4)
    | ~ spl13_13 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl13_13
  <=> ~ r1_orders_2(sK1,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f581,plain,
    ( r1_orders_2(sK1,sK3,sK4)
    | ~ spl13_8
    | ~ spl13_18
    | ~ spl13_20
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_32 ),
    inference(subsumption_resolution,[],[f580,f166])).

fof(f166,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl13_20 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl13_20
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f580,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK3,sK4)
    | ~ spl13_8
    | ~ spl13_18
    | ~ spl13_24
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_32 ),
    inference(subsumption_resolution,[],[f579,f174])).

fof(f174,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ spl13_24 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl13_24
  <=> m1_subset_1(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).

fof(f579,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK3,sK4)
    | ~ spl13_8
    | ~ spl13_18
    | ~ spl13_26
    | ~ spl13_28
    | ~ spl13_32 ),
    inference(subsumption_resolution,[],[f578,f182])).

fof(f182,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl13_28 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl13_28
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).

fof(f578,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK3,sK4)
    | ~ spl13_8
    | ~ spl13_18
    | ~ spl13_26
    | ~ spl13_32 ),
    inference(subsumption_resolution,[],[f577,f162])).

fof(f162,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl13_18
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f577,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK3,sK4)
    | ~ spl13_8
    | ~ spl13_26
    | ~ spl13_32 ),
    inference(resolution,[],[f219,f178])).

fof(f178,plain,
    ( r1_orders_2(sK2,sK3,sK4)
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl13_26
  <=> r1_orders_2(sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK2,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_orders_2(sK1,X0,X1) )
    | ~ spl13_8
    | ~ spl13_32 ),
    inference(subsumption_resolution,[],[f218,f136])).

fof(f136,plain,
    ( l1_orders_2(sK1)
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl13_8
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_orders_2(sK2,X0,X1)
        | r1_orders_2(sK1,X0,X1) )
    | ~ spl13_32 ),
    inference(resolution,[],[f204,f105])).

fof(f105,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X4,X5)
      | r1_orders_2(X0,X4,X5) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | X3 != X5
      | ~ r1_orders_2(X1,X4,X5)
      | r1_orders_2(X0,X4,X3) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | X2 != X4
      | X3 != X5
      | ~ r1_orders_2(X1,X4,X5)
      | r1_orders_2(X0,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_6__t20_yellow_6.p',t60_yellow_0)).

fof(f204,plain,
    ( m1_yellow_0(sK2,sK1)
    | ~ spl13_32 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl13_32
  <=> m1_yellow_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).

fof(f205,plain,
    ( spl13_32
    | ~ spl13_0
    | ~ spl13_6
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f193,f169,f121,f108,f203])).

fof(f108,plain,
    ( spl13_0
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_0])])).

fof(f121,plain,
    ( spl13_6
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f169,plain,
    ( spl13_22
  <=> m1_yellow_6(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).

fof(f193,plain,
    ( m1_yellow_0(sK2,sK1)
    | ~ spl13_0
    | ~ spl13_6
    | ~ spl13_22 ),
    inference(subsumption_resolution,[],[f192,f109])).

fof(f109,plain,
    ( l1_struct_0(sK0)
    | ~ spl13_0 ),
    inference(avatar_component_clause,[],[f108])).

fof(f192,plain,
    ( m1_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl13_0
    | ~ spl13_6
    | ~ spl13_22 ),
    inference(subsumption_resolution,[],[f191,f190])).

fof(f190,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ spl13_0
    | ~ spl13_6
    | ~ spl13_22 ),
    inference(subsumption_resolution,[],[f189,f109])).

fof(f189,plain,
    ( ~ l1_struct_0(sK0)
    | l1_waybel_0(sK2,sK0)
    | ~ spl13_6
    | ~ spl13_22 ),
    inference(subsumption_resolution,[],[f186,f122])).

fof(f122,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f186,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | l1_waybel_0(sK2,sK0)
    | ~ spl13_22 ),
    inference(resolution,[],[f170,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_waybel_0(X2,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t20_yellow_6.p',dt_m1_yellow_6)).

fof(f170,plain,
    ( m1_yellow_6(sK2,sK0,sK1)
    | ~ spl13_22 ),
    inference(avatar_component_clause,[],[f169])).

fof(f191,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | m1_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl13_6
    | ~ spl13_22 ),
    inference(subsumption_resolution,[],[f187,f122])).

fof(f187,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_waybel_0(sK2,sK0)
    | m1_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl13_22 ),
    inference(resolution,[],[f170,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_waybel_0(X2,X0)
      | m1_yellow_0(X2,X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( l1_waybel_0(X2,X0)
             => ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t20_yellow_6.p',d8_yellow_6)).

fof(f183,plain,
    ( spl13_28
    | ~ spl13_2
    | ~ spl13_16 ),
    inference(avatar_split_clause,[],[f158,f155,f113,f181])).

fof(f113,plain,
    ( spl13_2
  <=> sK3 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f155,plain,
    ( spl13_16
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f158,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl13_2
    | ~ spl13_16 ),
    inference(forward_demodulation,[],[f156,f114])).

fof(f114,plain,
    ( sK3 = sK5
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f156,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl13_16 ),
    inference(avatar_component_clause,[],[f155])).

fof(f179,plain,
    ( spl13_26
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f143,f139,f117,f113,f177])).

fof(f117,plain,
    ( spl13_4
  <=> sK4 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f139,plain,
    ( spl13_10
  <=> r1_orders_2(sK2,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f143,plain,
    ( r1_orders_2(sK2,sK3,sK4)
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_10 ),
    inference(forward_demodulation,[],[f142,f114])).

fof(f142,plain,
    ( r1_orders_2(sK2,sK5,sK4)
    | ~ spl13_4
    | ~ spl13_10 ),
    inference(forward_demodulation,[],[f140,f118])).

fof(f118,plain,
    ( sK4 = sK6
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f140,plain,
    ( r1_orders_2(sK2,sK5,sK6)
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f139])).

fof(f175,plain,(
    spl13_24 ),
    inference(avatar_split_clause,[],[f106,f173])).

fof(f106,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f66,f68])).

fof(f68,plain,(
    sK4 = sK6 ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X1,X3,X4)
                              & r1_orders_2(X2,X5,X6)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X1,X3,X4)
                              & r1_orders_2(X2,X5,X6)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_waybel_0(X1,X0)
           => ! [X2] :
                ( m1_yellow_6(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_orders_2(X2,X5,X6)
                                    & X4 = X6
                                    & X3 = X5 )
                                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( ( r1_orders_2(X2,X5,X6)
                                  & X4 = X6
                                  & X3 = X5 )
                               => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t20_yellow_6.p',t20_yellow_6)).

fof(f66,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f171,plain,(
    spl13_22 ),
    inference(avatar_split_clause,[],[f74,f169])).

fof(f74,plain,(
    m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f167,plain,(
    spl13_20 ),
    inference(avatar_split_clause,[],[f73,f165])).

fof(f73,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f163,plain,(
    spl13_18 ),
    inference(avatar_split_clause,[],[f72,f161])).

fof(f72,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f157,plain,(
    spl13_16 ),
    inference(avatar_split_clause,[],[f71,f155])).

fof(f71,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f149,plain,(
    ~ spl13_13 ),
    inference(avatar_split_clause,[],[f70,f147])).

fof(f70,plain,(
    ~ r1_orders_2(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f141,plain,(
    spl13_10 ),
    inference(avatar_split_clause,[],[f69,f139])).

fof(f69,plain,(
    r1_orders_2(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f137,plain,
    ( spl13_8
    | ~ spl13_0
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f131,f121,f108,f135])).

fof(f131,plain,
    ( l1_orders_2(sK1)
    | ~ spl13_0
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f126,f109])).

fof(f126,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK1)
    | ~ spl13_6 ),
    inference(resolution,[],[f122,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t20_yellow_6.p',dt_l1_waybel_0)).

fof(f123,plain,(
    spl13_6 ),
    inference(avatar_split_clause,[],[f75,f121])).

fof(f75,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f119,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f68,f117])).

fof(f115,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f67,f113])).

fof(f67,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f37])).

fof(f110,plain,(
    spl13_0 ),
    inference(avatar_split_clause,[],[f76,f108])).

fof(f76,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
