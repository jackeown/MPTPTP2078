%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1651+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:28 EST 2020

% Result     : Theorem 38.20s
% Output     : Refutation 38.20s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 454 expanded)
%              Number of leaves         :   36 ( 189 expanded)
%              Depth                    :   12
%              Number of atoms          :  765 (2609 expanded)
%              Number of equality atoms :   26 (  57 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81370,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5044,f5049,f5054,f5059,f5064,f5069,f5093,f5099,f5182,f5274,f5279,f5288,f14521,f20002,f36959,f52442,f58905,f59328,f81337,f81342,f81347,f81369])).

fof(f81369,plain,
    ( ~ spl206_4
    | ~ spl206_5
    | ~ spl206_11
    | ~ spl206_25
    | spl206_33
    | ~ spl206_271 ),
    inference(avatar_contradiction_clause,[],[f81368])).

fof(f81368,plain,
    ( $false
    | ~ spl206_4
    | ~ spl206_5
    | ~ spl206_11
    | ~ spl206_25
    | spl206_33
    | ~ spl206_271 ),
    inference(subsumption_resolution,[],[f81366,f38159])).

fof(f38159,plain,
    ( r2_hidden(sK13(sK0,sK1,sK2),k3_waybel_0(sK0,sK1))
    | ~ spl206_271 ),
    inference(avatar_component_clause,[],[f38158])).

fof(f38158,plain,
    ( spl206_271
  <=> r2_hidden(sK13(sK0,sK1,sK2),k3_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_271])])).

fof(f81366,plain,
    ( ~ r2_hidden(sK13(sK0,sK1,sK2),k3_waybel_0(sK0,sK1))
    | ~ spl206_4
    | ~ spl206_5
    | ~ spl206_11
    | ~ spl206_25
    | spl206_33 ),
    inference(unit_resulting_resolution,[],[f5058,f5181,f5287,f5063,f5092,f3935])).

fof(f3935,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3654])).

fof(f3654,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK13(X0,X1,X2),X2)
                & r2_hidden(sK13(X0,X1,X2),X1)
                & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f3652,f3653])).

fof(f3653,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK13(X0,X1,X2),X2)
        & r2_hidden(sK13(X0,X1,X2),X1)
        & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3652,plain,(
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
    inference(rectify,[],[f3651])).

fof(f3651,plain,(
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
    inference(nnf_transformation,[],[f3254])).

fof(f3254,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3253])).

fof(f3253,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f5092,plain,
    ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ~ spl206_11 ),
    inference(avatar_component_clause,[],[f5090])).

fof(f5090,plain,
    ( spl206_11
  <=> r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_11])])).

fof(f5063,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl206_5 ),
    inference(avatar_component_clause,[],[f5061])).

fof(f5061,plain,
    ( spl206_5
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_5])])).

fof(f5287,plain,
    ( ~ r1_orders_2(sK0,sK13(sK0,sK1,sK2),sK2)
    | spl206_33 ),
    inference(avatar_component_clause,[],[f5285])).

fof(f5285,plain,
    ( spl206_33
  <=> r1_orders_2(sK0,sK13(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_33])])).

fof(f5181,plain,
    ( m1_subset_1(sK13(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl206_25 ),
    inference(avatar_component_clause,[],[f5179])).

fof(f5179,plain,
    ( spl206_25
  <=> m1_subset_1(sK13(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_25])])).

fof(f5058,plain,
    ( l1_orders_2(sK0)
    | ~ spl206_4 ),
    inference(avatar_component_clause,[],[f5056])).

fof(f5056,plain,
    ( spl206_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_4])])).

fof(f81347,plain,
    ( ~ spl206_4
    | ~ spl206_6
    | ~ spl206_25
    | ~ spl206_201
    | spl206_271
    | ~ spl206_299 ),
    inference(avatar_contradiction_clause,[],[f81346])).

fof(f81346,plain,
    ( $false
    | ~ spl206_4
    | ~ spl206_6
    | ~ spl206_25
    | ~ spl206_201
    | spl206_271
    | ~ spl206_299 ),
    inference(subsumption_resolution,[],[f81345,f52447])).

fof(f52447,plain,
    ( ~ r2_hidden(sK13(sK0,sK1,sK2),sK1)
    | ~ spl206_4
    | ~ spl206_6
    | ~ spl206_25
    | spl206_271
    | ~ spl206_299 ),
    inference(unit_resulting_resolution,[],[f5058,f5068,f5181,f5181,f38160,f52441,f5005])).

fof(f5005,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ r1_orders_2(X0,X6,X7)
      | ~ r2_hidden(X7,X1)
      | r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f4663,f3893])).

fof(f3893,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3237])).

fof(f3237,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3236])).

fof(f3236,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3170])).

fof(f3170,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_waybel_0)).

fof(f4663,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r1_orders_2(X0,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3901])).

fof(f3901,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r1_orders_2(X0,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k3_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3636])).

fof(f3636,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k3_waybel_0(X0,X1) = X2
                  | ( ( ! [X4] :
                          ( ~ r2_hidden(X4,X1)
                          | ~ r1_orders_2(X0,sK3(X0,X1,X2),X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r2_hidden(sK3(X0,X1,X2),X2) )
                    & ( ( r2_hidden(sK4(X0,X1,X2),X1)
                        & r1_orders_2(X0,sK3(X0,X1,X2),sK4(X0,X1,X2))
                        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
                      | r2_hidden(sK3(X0,X1,X2),X2) )
                    & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ! [X7] :
                              ( ~ r2_hidden(X7,X1)
                              | ~ r1_orders_2(X0,X6,X7)
                              | ~ m1_subset_1(X7,u1_struct_0(X0)) ) )
                        & ( ( r2_hidden(sK5(X0,X1,X6),X1)
                            & r1_orders_2(X0,X6,sK5(X0,X1,X6))
                            & m1_subset_1(sK5(X0,X1,X6),u1_struct_0(X0)) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k3_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f3632,f3635,f3634,f3633])).

fof(f3633,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r1_orders_2(X0,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r1_orders_2(X0,X3,X5)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r1_orders_2(X0,sK3(X0,X1,X2),X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r1_orders_2(X0,sK3(X0,X1,X2),X5)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | r2_hidden(sK3(X0,X1,X2),X2) )
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3634,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r1_orders_2(X0,sK3(X0,X1,X2),X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r1_orders_2(X0,sK3(X0,X1,X2),sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3635,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r1_orders_2(X0,X6,X8)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( r2_hidden(sK5(X0,X1,X6),X1)
        & r1_orders_2(X0,X6,sK5(X0,X1,X6))
        & m1_subset_1(sK5(X0,X1,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3632,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k3_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X3,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r1_orders_2(X0,X3,X5)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ! [X7] :
                              ( ~ r2_hidden(X7,X1)
                              | ~ r1_orders_2(X0,X6,X7)
                              | ~ m1_subset_1(X7,u1_struct_0(X0)) ) )
                        & ( ? [X8] :
                              ( r2_hidden(X8,X1)
                              & r1_orders_2(X0,X6,X8)
                              & m1_subset_1(X8,u1_struct_0(X0)) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k3_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3631])).

fof(f3631,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k3_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X3,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X4] :
                            ( r2_hidden(X4,X1)
                            & r1_orders_2(X0,X3,X4)
                            & m1_subset_1(X4,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ! [X4] :
                              ( ~ r2_hidden(X4,X1)
                              | ~ r1_orders_2(X0,X3,X4)
                              | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
                        & ( ? [X4] :
                              ( r2_hidden(X4,X1)
                              & r1_orders_2(X0,X3,X4)
                              & m1_subset_1(X4,u1_struct_0(X0)) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k3_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3630])).

fof(f3630,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k3_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X3,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X4] :
                            ( r2_hidden(X4,X1)
                            & r1_orders_2(X0,X3,X4)
                            & m1_subset_1(X4,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ! [X4] :
                              ( ~ r2_hidden(X4,X1)
                              | ~ r1_orders_2(X0,X3,X4)
                              | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
                        & ( ? [X4] :
                              ( r2_hidden(X4,X1)
                              & r1_orders_2(X0,X3,X4)
                              & m1_subset_1(X4,u1_struct_0(X0)) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k3_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3244])).

fof(f3244,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3158])).

fof(f3158,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_waybel_0)).

fof(f52441,plain,
    ( r1_orders_2(sK0,sK13(sK0,sK1,sK2),sK13(sK0,sK1,sK2))
    | ~ spl206_299 ),
    inference(avatar_component_clause,[],[f52439])).

fof(f52439,plain,
    ( spl206_299
  <=> r1_orders_2(sK0,sK13(sK0,sK1,sK2),sK13(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_299])])).

fof(f38160,plain,
    ( ~ r2_hidden(sK13(sK0,sK1,sK2),k3_waybel_0(sK0,sK1))
    | spl206_271 ),
    inference(avatar_component_clause,[],[f38158])).

fof(f5068,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl206_6 ),
    inference(avatar_component_clause,[],[f5066])).

fof(f5066,plain,
    ( spl206_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_6])])).

fof(f81345,plain,
    ( r2_hidden(sK13(sK0,sK1,sK2),sK1)
    | ~ spl206_201 ),
    inference(subsumption_resolution,[],[f14706,f4680])).

fof(f4680,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f4125])).

fof(f4125,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3739])).

fof(f3739,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f3738])).

fof(f3738,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f14706,plain,
    ( ~ r1_tarski(sK1,sK1)
    | r2_hidden(sK13(sK0,sK1,sK2),sK1)
    | ~ spl206_201 ),
    inference(superposition,[],[f4063,f14520])).

fof(f14520,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK13(sK0,sK1,sK2)),sK1)
    | ~ spl206_201 ),
    inference(avatar_component_clause,[],[f14518])).

fof(f14518,plain,
    ( spl206_201
  <=> sK1 = k2_xboole_0(k1_tarski(sK13(sK0,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_201])])).

fof(f4063,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3321])).

fof(f3321,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f403])).

fof(f403,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f81342,plain,
    ( ~ spl206_3
    | ~ spl206_4
    | ~ spl206_5
    | ~ spl206_10
    | spl206_31
    | ~ spl206_32
    | ~ spl206_302
    | ~ spl206_304
    | ~ spl206_315 ),
    inference(avatar_contradiction_clause,[],[f81341])).

fof(f81341,plain,
    ( $false
    | ~ spl206_3
    | ~ spl206_4
    | ~ spl206_5
    | ~ spl206_10
    | spl206_31
    | ~ spl206_32
    | ~ spl206_302
    | ~ spl206_304
    | ~ spl206_315 ),
    inference(subsumption_resolution,[],[f81338,f59329])).

fof(f59329,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK13(sK0,k3_waybel_0(sK0,sK1),sK2)),sK2)
    | ~ spl206_4
    | ~ spl206_5
    | ~ spl206_10
    | ~ spl206_302
    | ~ spl206_304 ),
    inference(unit_resulting_resolution,[],[f5058,f5063,f5088,f58904,f59327,f3935])).

fof(f59327,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK13(sK0,k3_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))
    | ~ spl206_304 ),
    inference(avatar_component_clause,[],[f59325])).

fof(f59325,plain,
    ( spl206_304
  <=> m1_subset_1(sK5(sK0,sK1,sK13(sK0,k3_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_304])])).

fof(f58904,plain,
    ( r2_hidden(sK5(sK0,sK1,sK13(sK0,k3_waybel_0(sK0,sK1),sK2)),sK1)
    | ~ spl206_302 ),
    inference(avatar_component_clause,[],[f58902])).

fof(f58902,plain,
    ( spl206_302
  <=> r2_hidden(sK5(sK0,sK1,sK13(sK0,k3_waybel_0(sK0,sK1),sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_302])])).

fof(f5088,plain,
    ( r2_lattice3(sK0,sK1,sK2)
    | ~ spl206_10 ),
    inference(avatar_component_clause,[],[f5086])).

fof(f5086,plain,
    ( spl206_10
  <=> r2_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_10])])).

fof(f81338,plain,
    ( ~ r1_orders_2(sK0,sK5(sK0,sK1,sK13(sK0,k3_waybel_0(sK0,sK1),sK2)),sK2)
    | ~ spl206_3
    | ~ spl206_4
    | ~ spl206_5
    | spl206_31
    | ~ spl206_32
    | ~ spl206_304
    | ~ spl206_315 ),
    inference(unit_resulting_resolution,[],[f5053,f5058,f5063,f5273,f5278,f59327,f81336,f4008])).

fof(f4008,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f3283])).

fof(f3283,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f3282])).

fof(f3282,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1954])).

fof(f1954,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

fof(f81336,plain,
    ( r1_orders_2(sK0,sK13(sK0,k3_waybel_0(sK0,sK1),sK2),sK5(sK0,sK1,sK13(sK0,k3_waybel_0(sK0,sK1),sK2)))
    | ~ spl206_315 ),
    inference(avatar_component_clause,[],[f81334])).

fof(f81334,plain,
    ( spl206_315
  <=> r1_orders_2(sK0,sK13(sK0,k3_waybel_0(sK0,sK1),sK2),sK5(sK0,sK1,sK13(sK0,k3_waybel_0(sK0,sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_315])])).

fof(f5278,plain,
    ( m1_subset_1(sK13(sK0,k3_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0))
    | ~ spl206_32 ),
    inference(avatar_component_clause,[],[f5276])).

fof(f5276,plain,
    ( spl206_32
  <=> m1_subset_1(sK13(sK0,k3_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_32])])).

fof(f5273,plain,
    ( ~ r1_orders_2(sK0,sK13(sK0,k3_waybel_0(sK0,sK1),sK2),sK2)
    | spl206_31 ),
    inference(avatar_component_clause,[],[f5271])).

fof(f5271,plain,
    ( spl206_31
  <=> r1_orders_2(sK0,sK13(sK0,k3_waybel_0(sK0,sK1),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_31])])).

fof(f5053,plain,
    ( v4_orders_2(sK0)
    | ~ spl206_3 ),
    inference(avatar_component_clause,[],[f5051])).

fof(f5051,plain,
    ( spl206_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_3])])).

fof(f81337,plain,
    ( spl206_315
    | ~ spl206_4
    | ~ spl206_6
    | ~ spl206_32
    | ~ spl206_218 ),
    inference(avatar_split_clause,[],[f20004,f19999,f5276,f5066,f5056,f81334])).

fof(f19999,plain,
    ( spl206_218
  <=> r2_hidden(sK13(sK0,k3_waybel_0(sK0,sK1),sK2),k3_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_218])])).

fof(f20004,plain,
    ( r1_orders_2(sK0,sK13(sK0,k3_waybel_0(sK0,sK1),sK2),sK5(sK0,sK1,sK13(sK0,k3_waybel_0(sK0,sK1),sK2)))
    | ~ spl206_4
    | ~ spl206_6
    | ~ spl206_32
    | ~ spl206_218 ),
    inference(unit_resulting_resolution,[],[f5058,f5068,f5278,f20001,f5007])).

fof(f5007,plain,(
    ! [X6,X0,X1] :
      ( r1_orders_2(X0,X6,sK5(X0,X1,X6))
      | ~ r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f4665,f3893])).

fof(f4665,plain,(
    ! [X6,X0,X1] :
      ( r1_orders_2(X0,X6,sK5(X0,X1,X6))
      | ~ r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3899])).

fof(f3899,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,X6,sK5(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k3_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3636])).

fof(f20001,plain,
    ( r2_hidden(sK13(sK0,k3_waybel_0(sK0,sK1),sK2),k3_waybel_0(sK0,sK1))
    | ~ spl206_218 ),
    inference(avatar_component_clause,[],[f19999])).

fof(f59328,plain,
    ( spl206_304
    | ~ spl206_4
    | ~ spl206_6
    | ~ spl206_32
    | ~ spl206_218 ),
    inference(avatar_split_clause,[],[f20003,f19999,f5276,f5066,f5056,f59325])).

fof(f20003,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK13(sK0,k3_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))
    | ~ spl206_4
    | ~ spl206_6
    | ~ spl206_32
    | ~ spl206_218 ),
    inference(unit_resulting_resolution,[],[f5058,f5068,f5278,f20001,f5008])).

fof(f5008,plain,(
    ! [X6,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f4666,f3893])).

fof(f4666,plain,(
    ! [X6,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3898])).

fof(f3898,plain,(
    ! [X6,X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k3_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3636])).

fof(f58905,plain,
    ( spl206_302
    | ~ spl206_4
    | ~ spl206_6
    | ~ spl206_32
    | ~ spl206_218 ),
    inference(avatar_split_clause,[],[f20005,f19999,f5276,f5066,f5056,f58902])).

fof(f20005,plain,
    ( r2_hidden(sK5(sK0,sK1,sK13(sK0,k3_waybel_0(sK0,sK1),sK2)),sK1)
    | ~ spl206_4
    | ~ spl206_6
    | ~ spl206_32
    | ~ spl206_218 ),
    inference(unit_resulting_resolution,[],[f5058,f5068,f5278,f20001,f5006])).

fof(f5006,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f4664,f3893])).

fof(f4664,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3900])).

fof(f3900,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k3_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3636])).

fof(f52442,plain,
    ( spl206_299
    | spl206_1
    | ~ spl206_2
    | ~ spl206_4
    | ~ spl206_25 ),
    inference(avatar_split_clause,[],[f51616,f5179,f5056,f5046,f5041,f52439])).

fof(f5041,plain,
    ( spl206_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_1])])).

fof(f5046,plain,
    ( spl206_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_2])])).

fof(f51616,plain,
    ( r1_orders_2(sK0,sK13(sK0,sK1,sK2),sK13(sK0,sK1,sK2))
    | spl206_1
    | ~ spl206_2
    | ~ spl206_4
    | ~ spl206_25 ),
    inference(unit_resulting_resolution,[],[f5043,f5048,f5058,f5181,f4010])).

fof(f4010,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3287])).

fof(f3287,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3286])).

fof(f3286,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1952])).

fof(f1952,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f5048,plain,
    ( v3_orders_2(sK0)
    | ~ spl206_2 ),
    inference(avatar_component_clause,[],[f5046])).

fof(f5043,plain,
    ( ~ v2_struct_0(sK0)
    | spl206_1 ),
    inference(avatar_component_clause,[],[f5041])).

fof(f36959,plain,
    ( spl206_10
    | ~ spl206_4
    | ~ spl206_5
    | spl206_24 ),
    inference(avatar_split_clause,[],[f5388,f5174,f5061,f5056,f5086])).

fof(f5174,plain,
    ( spl206_24
  <=> r2_hidden(sK13(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_24])])).

fof(f5388,plain,
    ( r2_lattice3(sK0,sK1,sK2)
    | ~ spl206_4
    | ~ spl206_5
    | spl206_24 ),
    inference(unit_resulting_resolution,[],[f5058,f5063,f5175,f3937])).

fof(f3937,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK13(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3654])).

fof(f5175,plain,
    ( ~ r2_hidden(sK13(sK0,sK1,sK2),sK1)
    | spl206_24 ),
    inference(avatar_component_clause,[],[f5174])).

fof(f20002,plain,
    ( spl206_218
    | ~ spl206_4
    | ~ spl206_5
    | spl206_11 ),
    inference(avatar_split_clause,[],[f19974,f5090,f5061,f5056,f19999])).

fof(f19974,plain,
    ( r2_hidden(sK13(sK0,k3_waybel_0(sK0,sK1),sK2),k3_waybel_0(sK0,sK1))
    | ~ spl206_4
    | ~ spl206_5
    | spl206_11 ),
    inference(unit_resulting_resolution,[],[f5058,f5063,f5091,f3937])).

fof(f5091,plain,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | spl206_11 ),
    inference(avatar_component_clause,[],[f5090])).

fof(f14521,plain,
    ( spl206_201
    | ~ spl206_24 ),
    inference(avatar_split_clause,[],[f6128,f5174,f14518])).

fof(f6128,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK13(sK0,sK1,sK2)),sK1)
    | ~ spl206_24 ),
    inference(unit_resulting_resolution,[],[f5176,f4066])).

fof(f4066,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f3324])).

fof(f3324,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f404])).

fof(f404,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f5176,plain,
    ( r2_hidden(sK13(sK0,sK1,sK2),sK1)
    | ~ spl206_24 ),
    inference(avatar_component_clause,[],[f5174])).

fof(f5288,plain,
    ( ~ spl206_33
    | ~ spl206_4
    | ~ spl206_5
    | spl206_10 ),
    inference(avatar_split_clause,[],[f5280,f5086,f5061,f5056,f5285])).

fof(f5280,plain,
    ( ~ r1_orders_2(sK0,sK13(sK0,sK1,sK2),sK2)
    | ~ spl206_4
    | ~ spl206_5
    | spl206_10 ),
    inference(unit_resulting_resolution,[],[f5058,f5063,f5087,f3938])).

fof(f3938,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK13(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3654])).

fof(f5087,plain,
    ( ~ r2_lattice3(sK0,sK1,sK2)
    | spl206_10 ),
    inference(avatar_component_clause,[],[f5086])).

fof(f5279,plain,
    ( spl206_32
    | ~ spl206_4
    | ~ spl206_5
    | spl206_11 ),
    inference(avatar_split_clause,[],[f5184,f5090,f5061,f5056,f5276])).

fof(f5184,plain,
    ( m1_subset_1(sK13(sK0,k3_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0))
    | ~ spl206_4
    | ~ spl206_5
    | spl206_11 ),
    inference(unit_resulting_resolution,[],[f5058,f5063,f5091,f3936])).

fof(f3936,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3654])).

fof(f5274,plain,
    ( ~ spl206_31
    | ~ spl206_4
    | ~ spl206_5
    | spl206_11 ),
    inference(avatar_split_clause,[],[f5183,f5090,f5061,f5056,f5271])).

fof(f5183,plain,
    ( ~ r1_orders_2(sK0,sK13(sK0,k3_waybel_0(sK0,sK1),sK2),sK2)
    | ~ spl206_4
    | ~ spl206_5
    | spl206_11 ),
    inference(unit_resulting_resolution,[],[f5058,f5063,f5091,f3938])).

fof(f5182,plain,
    ( spl206_25
    | ~ spl206_4
    | ~ spl206_5
    | spl206_10 ),
    inference(avatar_split_clause,[],[f5124,f5086,f5061,f5056,f5179])).

fof(f5124,plain,
    ( m1_subset_1(sK13(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl206_4
    | ~ spl206_5
    | spl206_10 ),
    inference(unit_resulting_resolution,[],[f5058,f5087,f5063,f3936])).

fof(f5099,plain,
    ( ~ spl206_10
    | ~ spl206_11 ),
    inference(avatar_split_clause,[],[f3892,f5090,f5086])).

fof(f3892,plain,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ~ r2_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3628])).

fof(f3628,plain,
    ( ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
      | ~ r2_lattice3(sK0,sK1,sK2) )
    & ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
      | r2_lattice3(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f3624,f3627,f3626,f3625])).

fof(f3625,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                  | ~ r2_lattice3(X0,X1,X2) )
                & ( r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                  | r2_lattice3(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,X1),X2)
                | ~ r2_lattice3(sK0,X1,X2) )
              & ( r2_lattice3(sK0,k3_waybel_0(sK0,X1),X2)
                | r2_lattice3(sK0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3626,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,X1),X2)
              | ~ r2_lattice3(sK0,X1,X2) )
            & ( r2_lattice3(sK0,k3_waybel_0(sK0,X1),X2)
              | r2_lattice3(sK0,X1,X2) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X2)
            | ~ r2_lattice3(sK0,sK1,X2) )
          & ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X2)
            | r2_lattice3(sK0,sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f3627,plain,
    ( ? [X2] :
        ( ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X2)
          | ~ r2_lattice3(sK0,sK1,X2) )
        & ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X2)
          | r2_lattice3(sK0,sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
        | ~ r2_lattice3(sK0,sK1,sK2) )
      & ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
        | r2_lattice3(sK0,sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3624,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                | ~ r2_lattice3(X0,X1,X2) )
              & ( r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                | r2_lattice3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3623])).

fof(f3623,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                | ~ r2_lattice3(X0,X1,X2) )
              & ( r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                | r2_lattice3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3235])).

fof(f3235,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_lattice3(X0,X1,X2)
              <~> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3234])).

fof(f3234,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_lattice3(X0,X1,X2)
              <~> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3220])).

fof(f3220,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X2)
                <=> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f3219])).

fof(f3219,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_lattice3(X0,X1,X2)
              <=> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_0)).

fof(f5093,plain,
    ( spl206_10
    | spl206_11 ),
    inference(avatar_split_clause,[],[f3891,f5090,f5086])).

fof(f3891,plain,
    ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | r2_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3628])).

fof(f5069,plain,(
    spl206_6 ),
    inference(avatar_split_clause,[],[f3889,f5066])).

fof(f3889,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f3628])).

fof(f5064,plain,(
    spl206_5 ),
    inference(avatar_split_clause,[],[f3890,f5061])).

fof(f3890,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3628])).

fof(f5059,plain,(
    spl206_4 ),
    inference(avatar_split_clause,[],[f3888,f5056])).

fof(f3888,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3628])).

fof(f5054,plain,(
    spl206_3 ),
    inference(avatar_split_clause,[],[f3887,f5051])).

fof(f3887,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3628])).

fof(f5049,plain,(
    spl206_2 ),
    inference(avatar_split_clause,[],[f3886,f5046])).

fof(f3886,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3628])).

fof(f5044,plain,(
    ~ spl206_1 ),
    inference(avatar_split_clause,[],[f3885,f5041])).

fof(f3885,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3628])).
%------------------------------------------------------------------------------
