%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t45_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:07 EDT 2019

% Result     : Theorem 17.24s
% Output     : Refutation 17.24s
% Verified   : 
% Statistics : Number of formulae       :  367 ( 988 expanded)
%              Number of leaves         :   71 ( 435 expanded)
%              Depth                    :   22
%              Number of atoms          : 2480 (8253 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4098,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f219,f226,f233,f240,f247,f254,f261,f265,f272,f279,f286,f293,f314,f328,f443,f449,f538,f572,f629,f653,f783,f2061,f3083,f3188,f3234,f3403,f3408,f3416,f3475,f3502,f3520,f3894,f3929,f3965,f3970,f4092,f4097])).

fof(f4097,plain,
    ( ~ spl17_295
    | ~ spl17_8
    | ~ spl17_22
    | spl17_55
    | ~ spl17_100
    | spl17_251 ),
    inference(avatar_split_clause,[],[f4096,f3278,f861,f432,f284,f238,f3675])).

fof(f3675,plain,
    ( spl17_295
  <=> ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK5),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_295])])).

fof(f238,plain,
    ( spl17_8
  <=> m1_subset_1(sK5,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_8])])).

fof(f284,plain,
    ( spl17_22
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_22])])).

fof(f432,plain,
    ( spl17_55
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_55])])).

fof(f861,plain,
    ( spl17_100
  <=> m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_100])])).

fof(f3278,plain,
    ( spl17_251
  <=> ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK5),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_251])])).

fof(f4096,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ spl17_8
    | ~ spl17_22
    | ~ spl17_55
    | ~ spl17_100
    | ~ spl17_251 ),
    inference(subsumption_resolution,[],[f4095,f433])).

fof(f433,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl17_55 ),
    inference(avatar_component_clause,[],[f432])).

fof(f4095,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | v2_struct_0(sK0)
    | ~ spl17_8
    | ~ spl17_22
    | ~ spl17_100
    | ~ spl17_251 ),
    inference(subsumption_resolution,[],[f4094,f285])).

fof(f285,plain,
    ( l1_orders_2(sK0)
    | ~ spl17_22 ),
    inference(avatar_component_clause,[],[f284])).

fof(f4094,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_8
    | ~ spl17_100
    | ~ spl17_251 ),
    inference(subsumption_resolution,[],[f4093,f862])).

fof(f862,plain,
    ( m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl17_100 ),
    inference(avatar_component_clause,[],[f861])).

fof(f4093,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_8
    | ~ spl17_251 ),
    inference(subsumption_resolution,[],[f3824,f239])).

fof(f239,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ spl17_8 ),
    inference(avatar_component_clause,[],[f238])).

fof(f3824,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_251 ),
    inference(duplicate_literal_removal,[],[f3823])).

fof(f3823,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_251 ),
    inference(superposition,[],[f3279,f184])).

fof(f184,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_yellow_3(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_yellow_3(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_yellow_3(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,u1_struct_0(X1))
        & m1_subset_1(X2,u1_struct_0(X0))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k7_yellow_3(X0,X1,X2,X3) = k4_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',redefinition_k7_yellow_3)).

fof(f3279,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ spl17_251 ),
    inference(avatar_component_clause,[],[f3278])).

fof(f4092,plain,
    ( ~ spl17_12
    | ~ spl17_14
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30
    | spl17_307 ),
    inference(avatar_contradiction_clause,[],[f4091])).

fof(f4091,plain,
    ( $false
    | ~ spl17_12
    | ~ spl17_14
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30
    | ~ spl17_307 ),
    inference(subsumption_resolution,[],[f4090,f313])).

fof(f313,plain,
    ( v5_orders_2(sK0)
    | ~ spl17_30 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl17_30
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_30])])).

fof(f4090,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl17_12
    | ~ spl17_14
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_307 ),
    inference(subsumption_resolution,[],[f4089,f292])).

fof(f292,plain,
    ( v2_lattice3(sK0)
    | ~ spl17_24 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl17_24
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_24])])).

fof(f4089,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl17_12
    | ~ spl17_14
    | ~ spl17_22
    | ~ spl17_307 ),
    inference(subsumption_resolution,[],[f4088,f285])).

fof(f4088,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl17_12
    | ~ spl17_14
    | ~ spl17_307 ),
    inference(subsumption_resolution,[],[f4087,f260])).

fof(f260,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl17_14 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl17_14
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_14])])).

fof(f4087,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl17_12
    | ~ spl17_307 ),
    inference(subsumption_resolution,[],[f4079,f253])).

fof(f253,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl17_12 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl17_12
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_12])])).

fof(f4079,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl17_307 ),
    inference(resolution,[],[f3924,f962])).

fof(f962,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f205,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',dt_k12_lattice3)).

fof(f205,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f153])).

fof(f153,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK6(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK6(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK6(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f108,f109])).

fof(f109,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK6(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK6(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK6(X0,X1,X2,X3),X1)
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f108,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f107])).

fof(f107,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',t23_yellow_0)).

fof(f3924,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK3)
    | ~ spl17_307 ),
    inference(avatar_component_clause,[],[f3923])).

fof(f3923,plain,
    ( spl17_307
  <=> ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_307])])).

fof(f3970,plain,
    ( ~ spl17_293
    | ~ spl17_10
    | ~ spl17_22
    | spl17_55
    | ~ spl17_100
    | spl17_245 ),
    inference(avatar_split_clause,[],[f3969,f3256,f861,f432,f284,f245,f3662])).

fof(f3662,plain,
    ( spl17_293
  <=> ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_293])])).

fof(f245,plain,
    ( spl17_10
  <=> m1_subset_1(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_10])])).

fof(f3256,plain,
    ( spl17_245
  <=> ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_245])])).

fof(f3969,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ spl17_10
    | ~ spl17_22
    | ~ spl17_55
    | ~ spl17_100
    | ~ spl17_245 ),
    inference(subsumption_resolution,[],[f3968,f433])).

fof(f3968,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl17_10
    | ~ spl17_22
    | ~ spl17_100
    | ~ spl17_245 ),
    inference(subsumption_resolution,[],[f3967,f285])).

fof(f3967,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_10
    | ~ spl17_100
    | ~ spl17_245 ),
    inference(subsumption_resolution,[],[f3966,f862])).

fof(f3966,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_10
    | ~ spl17_245 ),
    inference(subsumption_resolution,[],[f3818,f246])).

fof(f246,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl17_10 ),
    inference(avatar_component_clause,[],[f245])).

fof(f3818,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_245 ),
    inference(duplicate_literal_removal,[],[f3817])).

fof(f3817,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_245 ),
    inference(superposition,[],[f3257,f184])).

fof(f3257,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ spl17_245 ),
    inference(avatar_component_clause,[],[f3256])).

fof(f3965,plain,
    ( ~ spl17_12
    | ~ spl17_14
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30
    | spl17_303 ),
    inference(avatar_contradiction_clause,[],[f3964])).

fof(f3964,plain,
    ( $false
    | ~ spl17_12
    | ~ spl17_14
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30
    | ~ spl17_303 ),
    inference(subsumption_resolution,[],[f3963,f313])).

fof(f3963,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl17_12
    | ~ spl17_14
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_303 ),
    inference(subsumption_resolution,[],[f3962,f292])).

fof(f3962,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl17_12
    | ~ spl17_14
    | ~ spl17_22
    | ~ spl17_303 ),
    inference(subsumption_resolution,[],[f3961,f285])).

fof(f3961,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl17_12
    | ~ spl17_14
    | ~ spl17_303 ),
    inference(subsumption_resolution,[],[f3960,f260])).

fof(f3960,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl17_12
    | ~ spl17_303 ),
    inference(subsumption_resolution,[],[f3952,f253])).

fof(f3952,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl17_303 ),
    inference(resolution,[],[f3889,f986])).

fof(f986,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f206,f151])).

fof(f206,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f152])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f110])).

fof(f3889,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK2)
    | ~ spl17_303 ),
    inference(avatar_component_clause,[],[f3888])).

fof(f3888,plain,
    ( spl17_303
  <=> ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_303])])).

fof(f3929,plain,
    ( ~ spl17_307
    | ~ spl17_8
    | ~ spl17_12
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_56
    | ~ spl17_100
    | ~ spl17_248
    | ~ spl17_276
    | spl17_295 ),
    inference(avatar_split_clause,[],[f3928,f3675,f3473,f3269,f861,f441,f284,f270,f252,f238,f3923])).

fof(f270,plain,
    ( spl17_18
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_18])])).

fof(f441,plain,
    ( spl17_56
  <=> v2_waybel_4(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_56])])).

fof(f3269,plain,
    ( spl17_248
  <=> r1_orders_2(sK0,sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_248])])).

fof(f3473,plain,
    ( spl17_276
  <=> r2_hidden(k4_tarski(sK3,sK5),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_276])])).

fof(f3928,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK3)
    | ~ spl17_8
    | ~ spl17_12
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_56
    | ~ spl17_100
    | ~ spl17_248
    | ~ spl17_276
    | ~ spl17_295 ),
    inference(subsumption_resolution,[],[f3927,f3270])).

fof(f3270,plain,
    ( r1_orders_2(sK0,sK5,sK5)
    | ~ spl17_248 ),
    inference(avatar_component_clause,[],[f3269])).

fof(f3927,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK3)
    | ~ r1_orders_2(sK0,sK5,sK5)
    | ~ spl17_8
    | ~ spl17_12
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_56
    | ~ spl17_100
    | ~ spl17_276
    | ~ spl17_295 ),
    inference(subsumption_resolution,[],[f3926,f239])).

fof(f3926,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK5,sK5)
    | ~ spl17_8
    | ~ spl17_12
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_56
    | ~ spl17_100
    | ~ spl17_276
    | ~ spl17_295 ),
    inference(subsumption_resolution,[],[f3901,f862])).

fof(f3901,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK3)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK5,sK5)
    | ~ spl17_8
    | ~ spl17_12
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_56
    | ~ spl17_276
    | ~ spl17_295 ),
    inference(resolution,[],[f3548,f3676])).

fof(f3676,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ spl17_295 ),
    inference(avatar_component_clause,[],[f3675])).

fof(f3548,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X1,X0),sK1)
        | ~ r1_orders_2(sK0,X1,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5,X0) )
    | ~ spl17_8
    | ~ spl17_12
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_56
    | ~ spl17_276 ),
    inference(subsumption_resolution,[],[f3547,f253])).

fof(f3547,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK5,X0)
        | ~ r1_orders_2(sK0,X1,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X1,X0),sK1) )
    | ~ spl17_8
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_56
    | ~ spl17_276 ),
    inference(subsumption_resolution,[],[f3543,f239])).

fof(f3543,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK5,X0)
        | ~ r1_orders_2(sK0,X1,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X1,X0),sK1) )
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_56
    | ~ spl17_276 ),
    inference(resolution,[],[f3474,f1090])).

fof(f1090,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ r2_hidden(k4_tarski(X7,X5),sK1)
        | ~ r1_orders_2(sK0,X5,X6)
        | ~ r1_orders_2(sK0,X8,X7)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X8,X6),sK1) )
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_56 ),
    inference(subsumption_resolution,[],[f1089,f285])).

fof(f1089,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ r1_orders_2(sK0,X5,X6)
        | ~ r2_hidden(k4_tarski(X7,X5),sK1)
        | ~ r1_orders_2(sK0,X8,X7)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X8,X6),sK1)
        | ~ l1_orders_2(sK0) )
    | ~ spl17_18
    | ~ spl17_56 ),
    inference(subsumption_resolution,[],[f1084,f442])).

fof(f442,plain,
    ( v2_waybel_4(sK1,sK0)
    | ~ spl17_56 ),
    inference(avatar_component_clause,[],[f441])).

fof(f1084,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ r1_orders_2(sK0,X5,X6)
        | ~ r2_hidden(k4_tarski(X7,X5),sK1)
        | ~ r1_orders_2(sK0,X8,X7)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ v2_waybel_4(sK1,sK0)
        | r2_hidden(k4_tarski(X8,X6),sK1)
        | ~ l1_orders_2(sK0) )
    | ~ spl17_18 ),
    inference(resolution,[],[f174,f271])).

fof(f271,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl17_18 ),
    inference(avatar_component_clause,[],[f270])).

fof(f174,plain,(
    ! [X6,X0,X8,X7,X1,X9] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ r1_orders_2(X0,X7,X8)
      | ~ r2_hidden(k4_tarski(X6,X7),X1)
      | ~ r1_orders_2(X0,X9,X6)
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v2_waybel_4(X1,X0)
      | r2_hidden(k4_tarski(X9,X8),X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f124])).

fof(f124,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_4(X1,X0)
              | ( ~ r2_hidden(k4_tarski(sK13(X0,X1),sK12(X0,X1)),X1)
                & r1_orders_2(X0,sK11(X0,X1),sK12(X0,X1))
                & r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X1)
                & r1_orders_2(X0,sK13(X0,X1),sK10(X0,X1))
                & m1_subset_1(sK13(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK12(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK11(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ! [X8] :
                          ( ! [X9] :
                              ( r2_hidden(k4_tarski(X9,X8),X1)
                              | ~ r1_orders_2(X0,X7,X8)
                              | ~ r2_hidden(k4_tarski(X6,X7),X1)
                              | ~ r1_orders_2(X0,X9,X6)
                              | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                          | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ v2_waybel_4(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12,sK13])],[f119,f123,f122,f121,f120])).

fof(f120,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                      & r1_orders_2(X0,X3,X4)
                      & r2_hidden(k4_tarski(X2,X3),X1)
                      & r1_orders_2(X0,X5,X2)
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                    & r1_orders_2(X0,X3,X4)
                    & r2_hidden(k4_tarski(sK10(X0,X1),X3),X1)
                    & r1_orders_2(X0,X5,sK10(X0,X1))
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                & m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f121,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                  & r1_orders_2(X0,X3,X4)
                  & r2_hidden(k4_tarski(X2,X3),X1)
                  & r1_orders_2(X0,X5,X2)
                  & m1_subset_1(X5,u1_struct_0(X0)) )
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                & r1_orders_2(X0,sK11(X0,X1),X4)
                & r2_hidden(k4_tarski(X2,sK11(X0,X1)),X1)
                & r1_orders_2(X0,X5,X2)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK11(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f122,plain,(
    ! [X2,X3,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_hidden(k4_tarski(X5,X4),X1)
              & r1_orders_2(X0,X3,X4)
              & r2_hidden(k4_tarski(X2,X3),X1)
              & r1_orders_2(X0,X5,X2)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ? [X5] :
            ( ~ r2_hidden(k4_tarski(X5,sK12(X0,X1)),X1)
            & r1_orders_2(X0,X3,sK12(X0,X1))
            & r2_hidden(k4_tarski(X2,X3),X1)
            & r1_orders_2(X0,X5,X2)
            & m1_subset_1(X5,u1_struct_0(X0)) )
        & m1_subset_1(sK12(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f123,plain,(
    ! [X4,X2,X3,X1,X0] :
      ( ? [X5] :
          ( ~ r2_hidden(k4_tarski(X5,X4),X1)
          & r1_orders_2(X0,X3,X4)
          & r2_hidden(k4_tarski(X2,X3),X1)
          & r1_orders_2(X0,X5,X2)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK13(X0,X1),X4),X1)
        & r1_orders_2(X0,X3,X4)
        & r2_hidden(k4_tarski(X2,X3),X1)
        & r1_orders_2(X0,sK13(X0,X1),X2)
        & m1_subset_1(sK13(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f119,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_4(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ? [X4] :
                          ( ? [X5] :
                              ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                              & r1_orders_2(X0,X3,X4)
                              & r2_hidden(k4_tarski(X2,X3),X1)
                              & r1_orders_2(X0,X5,X2)
                              & m1_subset_1(X5,u1_struct_0(X0)) )
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ! [X8] :
                          ( ! [X9] :
                              ( r2_hidden(k4_tarski(X9,X8),X1)
                              | ~ r1_orders_2(X0,X7,X8)
                              | ~ r2_hidden(k4_tarski(X6,X7),X1)
                              | ~ r1_orders_2(X0,X9,X6)
                              | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                          | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ v2_waybel_4(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f118])).

fof(f118,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_4(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ? [X4] :
                          ( ? [X5] :
                              ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                              & r1_orders_2(X0,X3,X4)
                              & r2_hidden(k4_tarski(X2,X3),X1)
                              & r1_orders_2(X0,X5,X2)
                              & m1_subset_1(X5,u1_struct_0(X0)) )
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( ! [X4] :
                          ( ! [X5] :
                              ( r2_hidden(k4_tarski(X5,X4),X1)
                              | ~ r1_orders_2(X0,X3,X4)
                              | ~ r2_hidden(k4_tarski(X2,X3),X1)
                              | ~ r1_orders_2(X0,X5,X2)
                              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_4(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_4(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r1_orders_2(X0,X3,X4)
                            | ~ r2_hidden(k4_tarski(X2,X3),X1)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_4(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r1_orders_2(X0,X3,X4)
                            | ~ r2_hidden(k4_tarski(X2,X3),X1)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
         => ( v2_waybel_4(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X3,X4)
                                & r2_hidden(k4_tarski(X2,X3),X1)
                                & r1_orders_2(X0,X5,X2) )
                             => r2_hidden(k4_tarski(X5,X4),X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',d5_waybel_4)).

fof(f3474,plain,
    ( r2_hidden(k4_tarski(sK3,sK5),sK1)
    | ~ spl17_276 ),
    inference(avatar_component_clause,[],[f3473])).

fof(f3894,plain,
    ( ~ spl17_303
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_56
    | ~ spl17_100
    | ~ spl17_198
    | ~ spl17_206
    | spl17_293 ),
    inference(avatar_split_clause,[],[f3893,f3662,f2055,f2014,f861,f441,f284,f270,f259,f245,f3888])).

fof(f2014,plain,
    ( spl17_198
  <=> r2_hidden(k4_tarski(sK2,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_198])])).

fof(f2055,plain,
    ( spl17_206
  <=> r1_orders_2(sK0,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_206])])).

fof(f3893,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK2)
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_56
    | ~ spl17_100
    | ~ spl17_198
    | ~ spl17_206
    | ~ spl17_293 ),
    inference(subsumption_resolution,[],[f3892,f2056])).

fof(f2056,plain,
    ( r1_orders_2(sK0,sK4,sK4)
    | ~ spl17_206 ),
    inference(avatar_component_clause,[],[f2055])).

fof(f3892,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK2)
    | ~ r1_orders_2(sK0,sK4,sK4)
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_56
    | ~ spl17_100
    | ~ spl17_198
    | ~ spl17_293 ),
    inference(subsumption_resolution,[],[f3891,f246])).

fof(f3891,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK4,sK4)
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_56
    | ~ spl17_100
    | ~ spl17_198
    | ~ spl17_293 ),
    inference(subsumption_resolution,[],[f3865,f862])).

fof(f3865,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK4,sK4)
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_56
    | ~ spl17_198
    | ~ spl17_293 ),
    inference(resolution,[],[f3526,f3663])).

fof(f3663,plain,
    ( ~ r2_hidden(k4_tarski(k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ spl17_293 ),
    inference(avatar_component_clause,[],[f3662])).

fof(f3526,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X1,X0),sK1)
        | ~ r1_orders_2(sK0,X1,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4,X0) )
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_56
    | ~ spl17_198 ),
    inference(subsumption_resolution,[],[f3525,f260])).

fof(f3525,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK4,X0)
        | ~ r1_orders_2(sK0,X1,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X1,X0),sK1) )
    | ~ spl17_10
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_56
    | ~ spl17_198 ),
    inference(subsumption_resolution,[],[f3521,f246])).

fof(f3521,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK4,X0)
        | ~ r1_orders_2(sK0,X1,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X1,X0),sK1) )
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_56
    | ~ spl17_198 ),
    inference(resolution,[],[f2015,f1090])).

fof(f2015,plain,
    ( r2_hidden(k4_tarski(sK2,sK4),sK1)
    | ~ spl17_198 ),
    inference(avatar_component_clause,[],[f2014])).

fof(f3520,plain,
    ( spl17_198
    | ~ spl17_6
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_22
    | spl17_55 ),
    inference(avatar_split_clause,[],[f3519,f432,f284,f259,f245,f231,f2014])).

fof(f231,plain,
    ( spl17_6
  <=> r2_hidden(k7_yellow_3(sK0,sK0,sK2,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_6])])).

fof(f3519,plain,
    ( r2_hidden(k4_tarski(sK2,sK4),sK1)
    | ~ spl17_6
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_22
    | ~ spl17_55 ),
    inference(subsumption_resolution,[],[f3518,f433])).

fof(f3518,plain,
    ( r2_hidden(k4_tarski(sK2,sK4),sK1)
    | v2_struct_0(sK0)
    | ~ spl17_6
    | ~ spl17_10
    | ~ spl17_14
    | ~ spl17_22 ),
    inference(subsumption_resolution,[],[f3517,f285])).

fof(f3517,plain,
    ( r2_hidden(k4_tarski(sK2,sK4),sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_6
    | ~ spl17_10
    | ~ spl17_14 ),
    inference(subsumption_resolution,[],[f3516,f260])).

fof(f3516,plain,
    ( r2_hidden(k4_tarski(sK2,sK4),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_6
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f3507,f246])).

fof(f3507,plain,
    ( r2_hidden(k4_tarski(sK2,sK4),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_6 ),
    inference(duplicate_literal_removal,[],[f3506])).

fof(f3506,plain,
    ( r2_hidden(k4_tarski(sK2,sK4),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_6 ),
    inference(superposition,[],[f232,f184])).

fof(f232,plain,
    ( r2_hidden(k7_yellow_3(sK0,sK0,sK2,sK4),sK1)
    | ~ spl17_6 ),
    inference(avatar_component_clause,[],[f231])).

fof(f3502,plain,
    ( spl17_248
    | ~ spl17_8
    | ~ spl17_22
    | ~ spl17_34
    | spl17_55
    | ~ spl17_98 ),
    inference(avatar_split_clause,[],[f3501,f761,f432,f326,f284,f238,f3269])).

fof(f326,plain,
    ( spl17_34
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_34])])).

fof(f761,plain,
    ( spl17_98
  <=> r3_orders_2(sK0,sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_98])])).

fof(f3501,plain,
    ( r1_orders_2(sK0,sK5,sK5)
    | ~ spl17_8
    | ~ spl17_22
    | ~ spl17_34
    | ~ spl17_55
    | ~ spl17_98 ),
    inference(subsumption_resolution,[],[f3500,f433])).

fof(f3500,plain,
    ( r1_orders_2(sK0,sK5,sK5)
    | v2_struct_0(sK0)
    | ~ spl17_8
    | ~ spl17_22
    | ~ spl17_34
    | ~ spl17_98 ),
    inference(subsumption_resolution,[],[f3499,f327])).

fof(f327,plain,
    ( v3_orders_2(sK0)
    | ~ spl17_34 ),
    inference(avatar_component_clause,[],[f326])).

fof(f3499,plain,
    ( r1_orders_2(sK0,sK5,sK5)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_8
    | ~ spl17_22
    | ~ spl17_98 ),
    inference(subsumption_resolution,[],[f3498,f285])).

fof(f3498,plain,
    ( r1_orders_2(sK0,sK5,sK5)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_8
    | ~ spl17_98 ),
    inference(subsumption_resolution,[],[f3480,f239])).

fof(f3480,plain,
    ( r1_orders_2(sK0,sK5,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_98 ),
    inference(duplicate_literal_removal,[],[f3479])).

fof(f3479,plain,
    ( r1_orders_2(sK0,sK5,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_98 ),
    inference(resolution,[],[f762,f196])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',redefinition_r3_orders_2)).

fof(f762,plain,
    ( r3_orders_2(sK0,sK5,sK5)
    | ~ spl17_98 ),
    inference(avatar_component_clause,[],[f761])).

fof(f3475,plain,
    ( spl17_276
    | ~ spl17_4
    | ~ spl17_8
    | ~ spl17_12
    | ~ spl17_22
    | spl17_55 ),
    inference(avatar_split_clause,[],[f3468,f432,f284,f252,f238,f224,f3473])).

fof(f224,plain,
    ( spl17_4
  <=> r2_hidden(k7_yellow_3(sK0,sK0,sK3,sK5),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_4])])).

fof(f3468,plain,
    ( r2_hidden(k4_tarski(sK3,sK5),sK1)
    | ~ spl17_4
    | ~ spl17_8
    | ~ spl17_12
    | ~ spl17_22
    | ~ spl17_55 ),
    inference(subsumption_resolution,[],[f3467,f433])).

fof(f3467,plain,
    ( r2_hidden(k4_tarski(sK3,sK5),sK1)
    | v2_struct_0(sK0)
    | ~ spl17_4
    | ~ spl17_8
    | ~ spl17_12
    | ~ spl17_22 ),
    inference(subsumption_resolution,[],[f3466,f285])).

fof(f3466,plain,
    ( r2_hidden(k4_tarski(sK3,sK5),sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_4
    | ~ spl17_8
    | ~ spl17_12 ),
    inference(subsumption_resolution,[],[f3465,f253])).

fof(f3465,plain,
    ( r2_hidden(k4_tarski(sK3,sK5),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_4
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f3462,f239])).

fof(f3462,plain,
    ( r2_hidden(k4_tarski(sK3,sK5),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_4 ),
    inference(duplicate_literal_removal,[],[f3461])).

fof(f3461,plain,
    ( r2_hidden(k4_tarski(sK3,sK5),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_4 ),
    inference(superposition,[],[f225,f184])).

fof(f225,plain,
    ( r2_hidden(k7_yellow_3(sK0,sK0,sK3,sK5),sK1)
    | ~ spl17_4 ),
    inference(avatar_component_clause,[],[f224])).

fof(f3416,plain,
    ( spl17_98
    | ~ spl17_8
    | ~ spl17_22
    | ~ spl17_34
    | spl17_55 ),
    inference(avatar_split_clause,[],[f3415,f432,f326,f284,f238,f761])).

fof(f3415,plain,
    ( r3_orders_2(sK0,sK5,sK5)
    | ~ spl17_8
    | ~ spl17_22
    | ~ spl17_34
    | ~ spl17_55 ),
    inference(subsumption_resolution,[],[f3414,f433])).

fof(f3414,plain,
    ( r3_orders_2(sK0,sK5,sK5)
    | v2_struct_0(sK0)
    | ~ spl17_8
    | ~ spl17_22
    | ~ spl17_34 ),
    inference(subsumption_resolution,[],[f3413,f327])).

fof(f3413,plain,
    ( r3_orders_2(sK0,sK5,sK5)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_8
    | ~ spl17_22 ),
    inference(subsumption_resolution,[],[f3410,f285])).

fof(f3410,plain,
    ( r3_orders_2(sK0,sK5,sK5)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_8 ),
    inference(resolution,[],[f239,f451])).

fof(f451,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(X4))
      | r3_orders_2(X4,X5,X5)
      | ~ l1_orders_2(X4)
      | ~ v3_orders_2(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f198,f185])).

fof(f185,plain,(
    ! [X0] : m1_subset_1(sK14(X0),X0) ),
    inference(cnf_transformation,[],[f126])).

fof(f126,plain,(
    ! [X0] : m1_subset_1(sK14(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f25,f125])).

fof(f125,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK14(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',existence_m1_subset_1)).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',reflexivity_r3_orders_2)).

fof(f3408,plain,
    ( ~ spl17_1
    | ~ spl17_101
    | ~ spl17_11
    | ~ spl17_9
    | ~ spl17_245
    | ~ spl17_251
    | spl17_3
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30 ),
    inference(avatar_split_clause,[],[f3407,f312,f291,f284,f270,f217,f3278,f3256,f235,f242,f864,f211])).

fof(f211,plain,
    ( spl17_1
  <=> ~ v5_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).

fof(f864,plain,
    ( spl17_101
  <=> ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_101])])).

fof(f242,plain,
    ( spl17_11
  <=> ~ m1_subset_1(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_11])])).

fof(f235,plain,
    ( spl17_9
  <=> ~ m1_subset_1(sK5,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_9])])).

fof(f217,plain,
    ( spl17_3
  <=> ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k12_lattice3(sK0,sK4,sK5)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_3])])).

fof(f3407,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ v5_waybel_7(sK1,sK0)
    | ~ spl17_3
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30 ),
    inference(subsumption_resolution,[],[f3406,f313])).

fof(f3406,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ v5_waybel_7(sK1,sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl17_3
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_24 ),
    inference(subsumption_resolution,[],[f3405,f292])).

fof(f3405,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ v5_waybel_7(sK1,sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl17_3
    | ~ spl17_18
    | ~ spl17_22 ),
    inference(subsumption_resolution,[],[f3404,f285])).

fof(f3404,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ v5_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl17_3
    | ~ spl17_18 ),
    inference(subsumption_resolution,[],[f3145,f271])).

fof(f3145,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK5),sK1)
    | ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),sK4),sK1)
    | ~ m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl17_3 ),
    inference(resolution,[],[f1103,f218])).

fof(f218,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k12_lattice3(sK0,sK4,sK5)),sK1)
    | ~ spl17_3 ),
    inference(avatar_component_clause,[],[f217])).

fof(f1103,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k7_yellow_3(X0,X0,X3,k12_lattice3(X0,X1,X2)),X4)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X3,X2),X4)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X3,X1),X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_waybel_7(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f1101,f195])).

fof(f195,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',cc2_lattice3)).

fof(f1101,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k7_yellow_3(X0,X0,X3,k12_lattice3(X0,X1,X2)),X4)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X3,X2),X4)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X3,X1),X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_waybel_7(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f1098])).

fof(f1098,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k7_yellow_3(X0,X0,X3,k12_lattice3(X0,X1,X2)),X4)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X3,X2),X4)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X3,X1),X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_waybel_7(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(superposition,[],[f167,f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',redefinition_k12_lattice3)).

fof(f167,plain,(
    ! [X6,X0,X7,X5,X1] :
      ( r2_hidden(k7_yellow_3(X0,X0,X5,k11_lattice3(X0,X6,X7)),X1)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X7),X1)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X6),X1)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_7(X1,X0)
              | ( ~ r2_hidden(k7_yellow_3(X0,X0,sK7(X0,X1),k11_lattice3(X0,sK8(X0,X1),sK9(X0,X1))),X1)
                & r2_hidden(k7_yellow_3(X0,X0,sK7(X0,X1),sK9(X0,X1)),X1)
                & r2_hidden(k7_yellow_3(X0,X0,sK7(X0,X1),sK8(X0,X1)),X1)
                & m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( ! [X7] :
                          ( r2_hidden(k7_yellow_3(X0,X0,X5,k11_lattice3(X0,X6,X7)),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X7),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X6),X1)
                          | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ v5_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f113,f116,f115,f114])).

fof(f114,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                  & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                  & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ r2_hidden(k7_yellow_3(X0,X0,sK7(X0,X1),k11_lattice3(X0,X3,X4)),X1)
                & r2_hidden(k7_yellow_3(X0,X0,sK7(X0,X1),X4),X1)
                & r2_hidden(k7_yellow_3(X0,X0,sK7(X0,X1),X3),X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f115,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
              & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
              & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,sK8(X0,X1),X4)),X1)
            & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
            & r2_hidden(k7_yellow_3(X0,X0,X2,sK8(X0,X1)),X1)
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f116,plain,(
    ! [X2,X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
          & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
          & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,sK9(X0,X1))),X1)
        & r2_hidden(k7_yellow_3(X0,X0,X2,sK9(X0,X1)),X1)
        & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
        & m1_subset_1(sK9(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f113,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ? [X4] :
                          ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                          & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                          & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( ! [X7] :
                          ( r2_hidden(k7_yellow_3(X0,X0,X5,k11_lattice3(X0,X6,X7)),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X7),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X6),X1)
                          | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ v5_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f112])).

fof(f112,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ? [X4] :
                          ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                          & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                          & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( ! [X4] :
                          ( r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v5_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                        | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                        | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                        | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                        | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
         => ( v5_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1) )
                         => r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',d7_waybel_7)).

fof(f3403,plain,
    ( ~ spl17_15
    | ~ spl17_13
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30
    | spl17_101 ),
    inference(avatar_split_clause,[],[f3402,f864,f312,f291,f284,f249,f256])).

fof(f256,plain,
    ( spl17_15
  <=> ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_15])])).

fof(f249,plain,
    ( spl17_13
  <=> ~ m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_13])])).

fof(f3402,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30
    | ~ spl17_101 ),
    inference(subsumption_resolution,[],[f3401,f313])).

fof(f3401,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_101 ),
    inference(subsumption_resolution,[],[f3400,f292])).

fof(f3400,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl17_22
    | ~ spl17_101 ),
    inference(subsumption_resolution,[],[f896,f285])).

fof(f896,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl17_101 ),
    inference(resolution,[],[f865,f151])).

fof(f865,plain,
    ( ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl17_101 ),
    inference(avatar_component_clause,[],[f864])).

fof(f3234,plain,
    ( spl17_0
    | ~ spl17_18
    | ~ spl17_22
    | spl17_55
    | ~ spl17_62
    | ~ spl17_74
    | ~ spl17_238 ),
    inference(avatar_split_clause,[],[f3233,f3081,f627,f520,f432,f284,f270,f208])).

fof(f208,plain,
    ( spl17_0
  <=> v5_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_0])])).

fof(f520,plain,
    ( spl17_62
  <=> m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_62])])).

fof(f627,plain,
    ( spl17_74
  <=> r3_orders_2(sK0,sK7(sK0,sK1),sK7(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_74])])).

fof(f3081,plain,
    ( spl17_238
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,sK7(sK0,sK1),X1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X1,sK9(sK0,sK1)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_238])])).

fof(f3233,plain,
    ( v5_waybel_7(sK1,sK0)
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_55
    | ~ spl17_62
    | ~ spl17_74
    | ~ spl17_238 ),
    inference(subsumption_resolution,[],[f3232,f433])).

fof(f3232,plain,
    ( v5_waybel_7(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_62
    | ~ spl17_74
    | ~ spl17_238 ),
    inference(subsumption_resolution,[],[f3231,f285])).

fof(f3231,plain,
    ( v5_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_18
    | ~ spl17_62
    | ~ spl17_74
    | ~ spl17_238 ),
    inference(subsumption_resolution,[],[f3222,f271])).

fof(f3222,plain,
    ( v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_62
    | ~ spl17_74
    | ~ spl17_238 ),
    inference(subsumption_resolution,[],[f3221,f521])).

fof(f521,plain,
    ( m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_62 ),
    inference(avatar_component_clause,[],[f520])).

fof(f3221,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_74
    | ~ spl17_238 ),
    inference(subsumption_resolution,[],[f3217,f628])).

fof(f628,plain,
    ( r3_orders_2(sK0,sK7(sK0,sK1),sK7(sK0,sK1))
    | ~ spl17_74 ),
    inference(avatar_component_clause,[],[f627])).

fof(f3217,plain,
    ( ~ r3_orders_2(sK0,sK7(sK0,sK1),sK7(sK0,sK1))
    | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_238 ),
    inference(resolution,[],[f3082,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( r2_hidden(k7_yellow_3(X0,X0,sK7(X0,X1),sK9(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f3082,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X1,sK9(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK7(sK0,sK1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl17_238 ),
    inference(avatar_component_clause,[],[f3081])).

fof(f3188,plain,
    ( spl17_1
    | ~ spl17_18
    | ~ spl17_22
    | spl17_55
    | spl17_237 ),
    inference(avatar_contradiction_clause,[],[f3187])).

fof(f3187,plain,
    ( $false
    | ~ spl17_1
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_55
    | ~ spl17_237 ),
    inference(subsumption_resolution,[],[f3186,f433])).

fof(f3186,plain,
    ( v2_struct_0(sK0)
    | ~ spl17_1
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_237 ),
    inference(subsumption_resolution,[],[f3185,f285])).

fof(f3185,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_1
    | ~ spl17_18
    | ~ spl17_237 ),
    inference(subsumption_resolution,[],[f3184,f271])).

fof(f3184,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_1
    | ~ spl17_237 ),
    inference(subsumption_resolution,[],[f3180,f212])).

fof(f212,plain,
    ( ~ v5_waybel_7(sK1,sK0)
    | ~ spl17_1 ),
    inference(avatar_component_clause,[],[f211])).

fof(f3180,plain,
    ( v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_237 ),
    inference(resolution,[],[f3079,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( r2_hidden(k7_yellow_3(X0,X0,sK7(X0,X1),sK8(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f3079,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,sK7(sK0,sK1),sK8(sK0,sK1)),sK1)
    | ~ spl17_237 ),
    inference(avatar_component_clause,[],[f3078])).

fof(f3078,plain,
    ( spl17_237
  <=> ~ r2_hidden(k7_yellow_3(sK0,sK0,sK7(sK0,sK1),sK8(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_237])])).

fof(f3083,plain,
    ( ~ spl17_237
    | spl17_238
    | spl17_1
    | ~ spl17_16
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30
    | ~ spl17_34
    | ~ spl17_62
    | ~ spl17_64
    | ~ spl17_70 ),
    inference(avatar_split_clause,[],[f3073,f570,f536,f520,f326,f312,f291,f284,f270,f263,f211,f3081,f3078])).

fof(f263,plain,
    ( spl17_16
  <=> ! [X9,X7,X8,X6] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X6,X7),k12_lattice3(sK0,X8,X9)),sK1)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X6,X8),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X7,X9),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_16])])).

fof(f536,plain,
    ( spl17_64
  <=> m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_64])])).

fof(f570,plain,
    ( spl17_70
  <=> m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_70])])).

fof(f3073,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,sK7(sK0,sK1),sK8(sK0,sK1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X1,sK9(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK7(sK0,sK1),X1) )
    | ~ spl17_1
    | ~ spl17_16
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30
    | ~ spl17_34
    | ~ spl17_62
    | ~ spl17_64
    | ~ spl17_70 ),
    inference(subsumption_resolution,[],[f3072,f521])).

fof(f3072,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,sK7(sK0,sK1),sK8(sK0,sK1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X1,sK9(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK7(sK0,sK1),X1) )
    | ~ spl17_1
    | ~ spl17_16
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30
    | ~ spl17_34
    | ~ spl17_64
    | ~ spl17_70 ),
    inference(subsumption_resolution,[],[f3071,f313])).

fof(f3071,plain,
    ( ! [X1] :
        ( ~ v5_orders_2(sK0)
        | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,sK7(sK0,sK1),sK8(sK0,sK1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X1,sK9(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK7(sK0,sK1),X1) )
    | ~ spl17_1
    | ~ spl17_16
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30
    | ~ spl17_34
    | ~ spl17_64
    | ~ spl17_70 ),
    inference(subsumption_resolution,[],[f3070,f292])).

fof(f3070,plain,
    ( ! [X1] :
        ( ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,sK7(sK0,sK1),sK8(sK0,sK1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X1,sK9(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK7(sK0,sK1),X1) )
    | ~ spl17_1
    | ~ spl17_16
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30
    | ~ spl17_34
    | ~ spl17_64
    | ~ spl17_70 ),
    inference(subsumption_resolution,[],[f3069,f537])).

fof(f537,plain,
    ( m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_64 ),
    inference(avatar_component_clause,[],[f536])).

fof(f3069,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,sK7(sK0,sK1),sK8(sK0,sK1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X1,sK9(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK7(sK0,sK1),X1) )
    | ~ spl17_1
    | ~ spl17_16
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30
    | ~ spl17_34
    | ~ spl17_70 ),
    inference(subsumption_resolution,[],[f3068,f571])).

fof(f571,plain,
    ( m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_70 ),
    inference(avatar_component_clause,[],[f570])).

fof(f3068,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,sK7(sK0,sK1),sK8(sK0,sK1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X1,sK9(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK7(sK0,sK1),X1) )
    | ~ spl17_1
    | ~ spl17_16
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30
    | ~ spl17_34 ),
    inference(subsumption_resolution,[],[f3067,f285])).

fof(f3067,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,sK7(sK0,sK1),sK8(sK0,sK1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X1,sK9(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK7(sK0,sK1),X1) )
    | ~ spl17_1
    | ~ spl17_16
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30
    | ~ spl17_34 ),
    inference(subsumption_resolution,[],[f3066,f271])).

fof(f3066,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,sK7(sK0,sK1),sK8(sK0,sK1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X1,sK9(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK7(sK0,sK1),X1) )
    | ~ spl17_1
    | ~ spl17_16
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30
    | ~ spl17_34 ),
    inference(subsumption_resolution,[],[f3062,f212])).

fof(f3062,plain,
    ( ! [X1] :
        ( v5_waybel_7(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,sK7(sK0,sK1),sK8(sK0,sK1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X1,sK9(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK7(sK0,sK1),X1) )
    | ~ spl17_16
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30
    | ~ spl17_34 ),
    inference(duplicate_literal_removal,[],[f3050])).

fof(f3050,plain,
    ( ! [X1] :
        ( v5_waybel_7(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,sK7(sK0,sK1),sK8(sK0,sK1)),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X1,sK9(sK0,sK1)),sK1)
        | ~ r3_orders_2(sK0,sK7(sK0,sK1),X1) )
    | ~ spl17_16
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30
    | ~ spl17_34 ),
    inference(resolution,[],[f1028,f928])).

fof(f928,plain,
    ( ! [X6,X4,X7,X5] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,X4,k12_lattice3(sK0,X6,X7)),sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X4,X6),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X5,X7),sK1)
        | ~ r3_orders_2(sK0,X4,X5) )
    | ~ spl17_16
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30
    | ~ spl17_34 ),
    inference(subsumption_resolution,[],[f927,f327])).

fof(f927,plain,
    ( ! [X6,X4,X7,X5] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,X4,k12_lattice3(sK0,X6,X7)),sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X4,X6),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X5,X7),sK1)
        | ~ r3_orders_2(sK0,X4,X5)
        | ~ v3_orders_2(sK0) )
    | ~ spl17_16
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_30 ),
    inference(subsumption_resolution,[],[f926,f313])).

fof(f926,plain,
    ( ! [X6,X4,X7,X5] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,X4,k12_lattice3(sK0,X6,X7)),sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X4,X6),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X5,X7),sK1)
        | ~ r3_orders_2(sK0,X4,X5)
        | ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl17_16
    | ~ spl17_22
    | ~ spl17_24 ),
    inference(subsumption_resolution,[],[f925,f292])).

fof(f925,plain,
    ( ! [X6,X4,X7,X5] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,X4,k12_lattice3(sK0,X6,X7)),sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X4,X6),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X5,X7),sK1)
        | ~ r3_orders_2(sK0,X4,X5)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl17_16
    | ~ spl17_22 ),
    inference(subsumption_resolution,[],[f917,f285])).

fof(f917,plain,
    ( ! [X6,X4,X7,X5] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,X4,k12_lattice3(sK0,X6,X7)),sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X4,X6),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X5,X7),sK1)
        | ~ r3_orders_2(sK0,X4,X5)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl17_16 ),
    inference(duplicate_literal_removal,[],[f904])).

fof(f904,plain,
    ( ! [X6,X4,X7,X5] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,X4,k12_lattice3(sK0,X6,X7)),sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X4,X6),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X5,X7),sK1)
        | ~ r3_orders_2(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl17_16 ),
    inference(superposition,[],[f264,f160])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = X1
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k12_lattice3(X0,X1,X2) = X1
                  | ~ r3_orders_2(X0,X1,X2) )
                & ( r3_orders_2(X0,X1,X2)
                  | k12_lattice3(X0,X1,X2) != X1 ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',t25_yellow_0)).

fof(f264,plain,
    ( ! [X6,X8,X7,X9] :
        ( r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X6,X7),k12_lattice3(sK0,X8,X9)),sK1)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X6,X8),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X7,X9),sK1) )
    | ~ spl17_16 ),
    inference(avatar_component_clause,[],[f263])).

fof(f1028,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k7_yellow_3(X0,X0,sK7(X0,X1),k12_lattice3(X0,sK8(X0,X1),sK9(X0,X1))),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f1027,f195])).

fof(f1027,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k7_yellow_3(X0,X0,sK7(X0,X1),k12_lattice3(X0,sK8(X0,X1),sK9(X0,X1))),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f1024])).

fof(f1024,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k7_yellow_3(X0,X0,sK7(X0,X1),k12_lattice3(X0,sK8(X0,X1),sK9(X0,X1))),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(superposition,[],[f173,f150])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k7_yellow_3(X0,X0,sK7(X0,X1),k11_lattice3(X0,sK8(X0,X1),sK9(X0,X1))),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f2061,plain,
    ( ~ spl17_11
    | spl17_206
    | ~ spl17_22
    | ~ spl17_34
    | spl17_55
    | ~ spl17_96 ),
    inference(avatar_split_clause,[],[f2060,f754,f432,f326,f284,f2055,f242])).

fof(f754,plain,
    ( spl17_96
  <=> r3_orders_2(sK0,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_96])])).

fof(f2060,plain,
    ( r1_orders_2(sK0,sK4,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl17_22
    | ~ spl17_34
    | ~ spl17_55
    | ~ spl17_96 ),
    inference(subsumption_resolution,[],[f2059,f433])).

fof(f2059,plain,
    ( r1_orders_2(sK0,sK4,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl17_22
    | ~ spl17_34
    | ~ spl17_96 ),
    inference(subsumption_resolution,[],[f2058,f327])).

fof(f2058,plain,
    ( r1_orders_2(sK0,sK4,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_22
    | ~ spl17_96 ),
    inference(subsumption_resolution,[],[f2049,f285])).

fof(f2049,plain,
    ( r1_orders_2(sK0,sK4,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_96 ),
    inference(duplicate_literal_removal,[],[f2048])).

fof(f2048,plain,
    ( r1_orders_2(sK0,sK4,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_96 ),
    inference(resolution,[],[f755,f196])).

fof(f755,plain,
    ( r3_orders_2(sK0,sK4,sK4)
    | ~ spl17_96 ),
    inference(avatar_component_clause,[],[f754])).

fof(f783,plain,
    ( spl17_96
    | ~ spl17_10
    | ~ spl17_22
    | ~ spl17_34
    | spl17_55 ),
    inference(avatar_split_clause,[],[f772,f432,f326,f284,f245,f754])).

fof(f772,plain,
    ( r3_orders_2(sK0,sK4,sK4)
    | ~ spl17_10
    | ~ spl17_22
    | ~ spl17_34
    | ~ spl17_55 ),
    inference(resolution,[],[f663,f246])).

fof(f663,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,X0,X0) )
    | ~ spl17_10
    | ~ spl17_22
    | ~ spl17_34
    | ~ spl17_55 ),
    inference(subsumption_resolution,[],[f662,f433])).

fof(f662,plain,
    ( ! [X0] :
        ( r3_orders_2(sK0,X0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl17_10
    | ~ spl17_22
    | ~ spl17_34 ),
    inference(subsumption_resolution,[],[f661,f327])).

fof(f661,plain,
    ( ! [X0] :
        ( r3_orders_2(sK0,X0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl17_10
    | ~ spl17_22 ),
    inference(subsumption_resolution,[],[f659,f285])).

fof(f659,plain,
    ( ! [X0] :
        ( r3_orders_2(sK0,X0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl17_10 ),
    inference(resolution,[],[f246,f198])).

fof(f653,plain,
    ( spl17_0
    | spl17_62
    | ~ spl17_18
    | ~ spl17_22
    | spl17_55 ),
    inference(avatar_split_clause,[],[f652,f432,f284,f270,f520,f208])).

fof(f652,plain,
    ( m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_55 ),
    inference(subsumption_resolution,[],[f651,f433])).

fof(f651,plain,
    ( m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl17_18
    | ~ spl17_22 ),
    inference(subsumption_resolution,[],[f508,f285])).

fof(f508,plain,
    ( m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_18 ),
    inference(resolution,[],[f168,f271])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
      | v5_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f629,plain,
    ( spl17_74
    | ~ spl17_22
    | ~ spl17_34
    | spl17_55
    | ~ spl17_62 ),
    inference(avatar_split_clause,[],[f615,f520,f432,f326,f284,f627])).

fof(f615,plain,
    ( r3_orders_2(sK0,sK7(sK0,sK1),sK7(sK0,sK1))
    | ~ spl17_22
    | ~ spl17_34
    | ~ spl17_55
    | ~ spl17_62 ),
    inference(resolution,[],[f543,f521])).

fof(f543,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,X0,X0) )
    | ~ spl17_22
    | ~ spl17_34
    | ~ spl17_55
    | ~ spl17_62 ),
    inference(subsumption_resolution,[],[f542,f433])).

fof(f542,plain,
    ( ! [X0] :
        ( r3_orders_2(sK0,X0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl17_22
    | ~ spl17_34
    | ~ spl17_62 ),
    inference(subsumption_resolution,[],[f541,f327])).

fof(f541,plain,
    ( ! [X0] :
        ( r3_orders_2(sK0,X0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl17_22
    | ~ spl17_62 ),
    inference(subsumption_resolution,[],[f539,f285])).

fof(f539,plain,
    ( ! [X0] :
        ( r3_orders_2(sK0,X0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl17_62 ),
    inference(resolution,[],[f521,f198])).

fof(f572,plain,
    ( spl17_70
    | spl17_1
    | ~ spl17_18
    | ~ spl17_22
    | spl17_55 ),
    inference(avatar_split_clause,[],[f565,f432,f284,f270,f211,f570])).

fof(f565,plain,
    ( m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_1
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_55 ),
    inference(subsumption_resolution,[],[f564,f433])).

fof(f564,plain,
    ( m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl17_1
    | ~ spl17_18
    | ~ spl17_22 ),
    inference(subsumption_resolution,[],[f563,f285])).

fof(f563,plain,
    ( m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_1
    | ~ spl17_18 ),
    inference(subsumption_resolution,[],[f558,f212])).

fof(f558,plain,
    ( m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_18 ),
    inference(resolution,[],[f170,f271])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
      | v5_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f538,plain,
    ( spl17_64
    | spl17_1
    | ~ spl17_18
    | ~ spl17_22
    | spl17_55 ),
    inference(avatar_split_clause,[],[f531,f432,f284,f270,f211,f536])).

fof(f531,plain,
    ( m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl17_1
    | ~ spl17_18
    | ~ spl17_22
    | ~ spl17_55 ),
    inference(subsumption_resolution,[],[f530,f433])).

fof(f530,plain,
    ( m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl17_1
    | ~ spl17_18
    | ~ spl17_22 ),
    inference(subsumption_resolution,[],[f529,f285])).

fof(f529,plain,
    ( m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_1
    | ~ spl17_18 ),
    inference(subsumption_resolution,[],[f524,f212])).

fof(f524,plain,
    ( m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_18 ),
    inference(resolution,[],[f169,f271])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | v5_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f449,plain,
    ( ~ spl17_22
    | ~ spl17_24
    | ~ spl17_54 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | ~ spl17_22
    | ~ spl17_24
    | ~ spl17_54 ),
    inference(subsumption_resolution,[],[f447,f285])).

fof(f447,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl17_24
    | ~ spl17_54 ),
    inference(subsumption_resolution,[],[f445,f292])).

fof(f445,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl17_54 ),
    inference(resolution,[],[f436,f195])).

fof(f436,plain,
    ( v2_struct_0(sK0)
    | ~ spl17_54 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl17_54
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_54])])).

fof(f443,plain,
    ( spl17_54
    | spl17_56
    | ~ spl17_18
    | ~ spl17_20
    | ~ spl17_22 ),
    inference(avatar_split_clause,[],[f430,f284,f277,f270,f441,f435])).

fof(f277,plain,
    ( spl17_20
  <=> v5_waybel_4(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_20])])).

fof(f430,plain,
    ( v2_waybel_4(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl17_18
    | ~ spl17_20
    | ~ spl17_22 ),
    inference(subsumption_resolution,[],[f429,f285])).

fof(f429,plain,
    ( v2_waybel_4(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_18
    | ~ spl17_20 ),
    inference(subsumption_resolution,[],[f426,f278])).

fof(f278,plain,
    ( v5_waybel_4(sK1,sK0)
    | ~ spl17_20 ),
    inference(avatar_component_clause,[],[f277])).

fof(f426,plain,
    ( ~ v5_waybel_4(sK1,sK0)
    | v2_waybel_4(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_18 ),
    inference(resolution,[],[f193,f271])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ v5_waybel_4(X1,X0)
      | v2_waybel_4(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_waybel_4(X1,X0)
          | ~ v5_waybel_4(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_waybel_4(X1,X0)
          | ~ v5_waybel_4(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
         => ( v5_waybel_4(X1,X0)
           => v2_waybel_4(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
         => ( v5_waybel_4(X1,X0)
           => ( v2_waybel_4(X1,X0)
              & v1_waybel_4(X1,X0) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
         => ( v5_waybel_4(X1,X0)
           => ( v3_waybel_4(X1,X0)
              & v2_waybel_4(X1,X0)
              & v1_waybel_4(X1,X0) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
         => ( v5_waybel_4(X1,X0)
           => ( v4_waybel_4(X1,X0)
              & v3_waybel_4(X1,X0)
              & v2_waybel_4(X1,X0)
              & v1_waybel_4(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',cc1_waybel_4)).

fof(f328,plain,(
    spl17_34 ),
    inference(avatar_split_clause,[],[f132,f326])).

fof(f132,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,
    ( ( ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k12_lattice3(sK0,sK4,sK5)),sK1)
        & r2_hidden(k7_yellow_3(sK0,sK0,sK3,sK5),sK1)
        & r2_hidden(k7_yellow_3(sK0,sK0,sK2,sK4),sK1)
        & m1_subset_1(sK5,u1_struct_0(sK0))
        & m1_subset_1(sK4,u1_struct_0(sK0))
        & m1_subset_1(sK3,u1_struct_0(sK0))
        & m1_subset_1(sK2,u1_struct_0(sK0)) )
      | ~ v5_waybel_7(sK1,sK0) )
    & ( ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X6,X7),k12_lattice3(sK0,X8,X9)),sK1)
                      | ~ r2_hidden(k7_yellow_3(sK0,sK0,X7,X9),sK1)
                      | ~ r2_hidden(k7_yellow_3(sK0,sK0,X6,X8),sK1)
                      | ~ m1_subset_1(X9,u1_struct_0(sK0)) )
                  | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
              | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
          | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
      | v5_waybel_7(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    & v5_waybel_4(sK1,sK0)
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v1_yellow_0(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f98,f104,f103,f102,f101,f100,f99])).

fof(f99,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ? [X4] :
                          ( ? [X5] :
                              ( ~ r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                              & r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                              & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                              & m1_subset_1(X5,u1_struct_0(X0)) )
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v5_waybel_7(X1,X0) )
            & ( ! [X6] :
                  ( ! [X7] :
                      ( ! [X8] :
                          ( ! [X9] :
                              ( r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X6,X7),k12_lattice3(X0,X8,X9)),X1)
                              | ~ r2_hidden(k7_yellow_3(X0,X0,X7,X9),X1)
                              | ~ r2_hidden(k7_yellow_3(X0,X0,X6,X8),X1)
                              | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                          | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | v5_waybel_7(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
            & v5_waybel_4(X1,X0) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X2,X3),k12_lattice3(sK0,X4,X5)),X1)
                            & r2_hidden(k7_yellow_3(sK0,sK0,X3,X5),X1)
                            & r2_hidden(k7_yellow_3(sK0,sK0,X2,X4),X1)
                            & m1_subset_1(X5,u1_struct_0(sK0)) )
                        & m1_subset_1(X4,u1_struct_0(sK0)) )
                    & m1_subset_1(X3,u1_struct_0(sK0)) )
                & m1_subset_1(X2,u1_struct_0(sK0)) )
            | ~ v5_waybel_7(X1,sK0) )
          & ( ! [X6] :
                ( ! [X7] :
                    ( ! [X8] :
                        ( ! [X9] :
                            ( r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X6,X7),k12_lattice3(sK0,X8,X9)),X1)
                            | ~ r2_hidden(k7_yellow_3(sK0,sK0,X7,X9),X1)
                            | ~ r2_hidden(k7_yellow_3(sK0,sK0,X6,X8),X1)
                            | ~ m1_subset_1(X9,u1_struct_0(sK0)) )
                        | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
                    | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
                | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
            | v5_waybel_7(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
          & v5_waybel_4(X1,sK0) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v1_yellow_0(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f100,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                            & r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                            & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v5_waybel_7(X1,X0) )
          & ( ! [X6] :
                ( ! [X7] :
                    ( ! [X8] :
                        ( ! [X9] :
                            ( r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X6,X7),k12_lattice3(X0,X8,X9)),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X7,X9),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X6,X8),X1)
                            | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                        | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | v5_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
     => ( ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),sK1)
                          & r2_hidden(k7_yellow_3(X0,X0,X3,X5),sK1)
                          & r2_hidden(k7_yellow_3(X0,X0,X2,X4),sK1)
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v5_waybel_7(sK1,X0) )
        & ( ! [X6] :
              ( ! [X7] :
                  ( ! [X8] :
                      ( ! [X9] :
                          ( r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X6,X7),k12_lattice3(X0,X8,X9)),sK1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X7,X9),sK1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X6,X8),sK1)
                          | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          | v5_waybel_7(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v5_waybel_4(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                      & r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                      & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,sK2,X3),k12_lattice3(X0,X4,X5)),X1)
                    & r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                    & r2_hidden(k7_yellow_3(X0,X0,sK2,X4),X1)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                & m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                  & r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                  & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                  & m1_subset_1(X5,u1_struct_0(X0)) )
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,sK3),k12_lattice3(X0,X4,X5)),X1)
                & r2_hidden(k7_yellow_3(X0,X0,sK3,X5),X1)
                & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
              & r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
              & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ? [X5] :
            ( ~ r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,sK4,X5)),X1)
            & r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
            & r2_hidden(k7_yellow_3(X0,X0,X2,sK4),X1)
            & m1_subset_1(X5,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f104,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ~ r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
          & r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
          & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,sK5)),X1)
        & r2_hidden(k7_yellow_3(X0,X0,X3,sK5),X1)
        & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f98,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                            & r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                            & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v5_waybel_7(X1,X0) )
          & ( ! [X6] :
                ( ! [X7] :
                    ( ! [X8] :
                        ( ! [X9] :
                            ( r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X6,X7),k12_lattice3(X0,X8,X9)),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X7,X9),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X6,X8),X1)
                            | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                        | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            | v5_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(rectify,[],[f97])).

fof(f97,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                            & r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                            & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v5_waybel_7(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v5_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f96])).

fof(f96,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                            & r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                            & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v5_waybel_7(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v5_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_waybel_7(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_waybel_7(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                            | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              & v5_waybel_4(X1,X0) )
           => ( v5_waybel_7(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ( ( r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                                  & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1) )
                               => r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
            & v5_waybel_4(X1,X0) )
         => ( v5_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r2_hidden(k7_yellow_3(X0,X0,X3,X5),X1)
                                & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1) )
                             => r2_hidden(k7_yellow_3(X0,X0,k12_lattice3(X0,X2,X3),k12_lattice3(X0,X4,X5)),X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t45_waybel_7.p',t45_waybel_7)).

fof(f314,plain,(
    spl17_30 ),
    inference(avatar_split_clause,[],[f134,f312])).

fof(f134,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f293,plain,(
    spl17_24 ),
    inference(avatar_split_clause,[],[f137,f291])).

fof(f137,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f286,plain,(
    spl17_22 ),
    inference(avatar_split_clause,[],[f138,f284])).

fof(f138,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f279,plain,(
    spl17_20 ),
    inference(avatar_split_clause,[],[f139,f277])).

fof(f139,plain,(
    v5_waybel_4(sK1,sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f272,plain,(
    spl17_18 ),
    inference(avatar_split_clause,[],[f140,f270])).

fof(f140,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f105])).

fof(f265,plain,
    ( spl17_0
    | spl17_16 ),
    inference(avatar_split_clause,[],[f141,f263,f208])).

fof(f141,plain,(
    ! [X6,X8,X7,X9] :
      ( r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,X6,X7),k12_lattice3(sK0,X8,X9)),sK1)
      | ~ r2_hidden(k7_yellow_3(sK0,sK0,X7,X9),sK1)
      | ~ r2_hidden(k7_yellow_3(sK0,sK0,X6,X8),sK1)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | v5_waybel_7(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f261,plain,
    ( ~ spl17_1
    | spl17_14 ),
    inference(avatar_split_clause,[],[f142,f259,f211])).

fof(f142,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f254,plain,
    ( ~ spl17_1
    | spl17_12 ),
    inference(avatar_split_clause,[],[f143,f252,f211])).

fof(f143,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v5_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f247,plain,
    ( ~ spl17_1
    | spl17_10 ),
    inference(avatar_split_clause,[],[f144,f245,f211])).

fof(f144,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ v5_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f240,plain,
    ( ~ spl17_1
    | spl17_8 ),
    inference(avatar_split_clause,[],[f145,f238,f211])).

fof(f145,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ v5_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f233,plain,
    ( ~ spl17_1
    | spl17_6 ),
    inference(avatar_split_clause,[],[f146,f231,f211])).

fof(f146,plain,
    ( r2_hidden(k7_yellow_3(sK0,sK0,sK2,sK4),sK1)
    | ~ v5_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f226,plain,
    ( ~ spl17_1
    | spl17_4 ),
    inference(avatar_split_clause,[],[f147,f224,f211])).

fof(f147,plain,
    ( r2_hidden(k7_yellow_3(sK0,sK0,sK3,sK5),sK1)
    | ~ v5_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f219,plain,
    ( ~ spl17_1
    | ~ spl17_3 ),
    inference(avatar_split_clause,[],[f148,f217,f211])).

fof(f148,plain,
    ( ~ r2_hidden(k7_yellow_3(sK0,sK0,k12_lattice3(sK0,sK2,sK3),k12_lattice3(sK0,sK4,sK5)),sK1)
    | ~ v5_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f105])).
%------------------------------------------------------------------------------
