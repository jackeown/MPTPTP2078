%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1650+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:15 EST 2020

% Result     : Theorem 32.50s
% Output     : Refutation 32.50s
% Verified   : 
% Statistics : Number of formulae       :  404 (1500 expanded)
%              Number of leaves         :   90 ( 680 expanded)
%              Depth                    :   14
%              Number of atoms          : 2596 (11109 expanded)
%              Number of equality atoms :   13 ( 231 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60048,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f92,f96,f100,f104,f108,f112,f124,f131,f140,f144,f147,f159,f166,f184,f198,f214,f226,f260,f274,f346,f487,f510,f514,f564,f676,f690,f705,f754,f5758,f8530,f8544,f8554,f8869,f10935,f10949,f10969,f11015,f11034,f11057,f11067,f11082,f11092,f11111,f11121,f11135,f11207,f11600,f11612,f11635,f11652,f11691,f11748,f11752,f11860,f12491,f12506,f12516,f13037,f13061,f13081,f13095,f13196,f13214,f13238,f13254,f14065,f14087,f22274,f59074,f59339,f59648,f59675,f60039])).

fof(f60039,plain,
    ( ~ spl9_1552
    | ~ spl9_11
    | ~ spl9_2
    | ~ spl9_19
    | ~ spl9_1691
    | ~ spl9_1544
    | ~ spl9_57
    | ~ spl9_4
    | ~ spl9_9335 ),
    inference(avatar_split_clause,[],[f60038,f59337,f98,f493,f11587,f12485,f209,f87,f138,f11622])).

fof(f11622,plain,
    ( spl9_1552
  <=> r2_hidden(sK3(sK0,sK1),k3_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1552])])).

fof(f138,plain,
    ( spl9_11
  <=> m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f87,plain,
    ( spl9_2
  <=> v1_waybel_0(k3_waybel_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f209,plain,
    ( spl9_19
  <=> m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f12485,plain,
    ( spl9_1691
  <=> r2_hidden(sK2(sK0,sK1),k3_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1691])])).

fof(f11587,plain,
    ( spl9_1544
  <=> r1_orders_2(sK0,sK2(sK0,sK1),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1544])])).

fof(f493,plain,
    ( spl9_57
  <=> m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_57])])).

fof(f98,plain,
    ( spl9_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f59337,plain,
    ( spl9_9335
  <=> ! [X5] :
        ( ~ r1_orders_2(sK0,X5,sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1)))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9335])])).

fof(f60038,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2(sK0,sK1),sK2(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,sK1),k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_waybel_0(k3_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK0,sK1),k3_waybel_0(sK0,sK1))
    | ~ spl9_4
    | ~ spl9_9335 ),
    inference(duplicate_literal_removal,[],[f60029])).

fof(f60029,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2(sK0,sK1),sK2(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,sK1),k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_waybel_0(k3_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK0,sK1),k3_waybel_0(sK0,sK1))
    | ~ spl9_4
    | ~ spl9_9335 ),
    inference(resolution,[],[f59338,f384])).

fof(f384,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X2,sK4(sK0,X1,X2,X0))
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v1_waybel_0(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,X1) )
    | ~ spl9_4 ),
    inference(resolution,[],[f56,f99])).

fof(f99,plain,
    ( l1_orders_2(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f56,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_orders_2(X0,X5,sK4(X0,X1,X5,X6)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_0(X1,X0)
              | ( ! [X4] :
                    ( ~ r1_orders_2(X0,sK3(X0,X1),X4)
                    | ~ r1_orders_2(X0,sK2(X0,X1),X4)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(sK3(X0,X1),X1)
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( ( r1_orders_2(X0,X6,sK4(X0,X1,X5,X6))
                        & r1_orders_2(X0,X5,sK4(X0,X1,X5,X6))
                        & r2_hidden(sK4(X0,X1,X5,X6),X1)
                        & m1_subset_1(sK4(X0,X1,X5,X6),u1_struct_0(X0)) )
                      | ~ r2_hidden(X6,X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ v1_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f35,f34,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r1_orders_2(X0,X3,X4)
                  | ~ r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_orders_2(X0,X3,X4)
                | ~ r1_orders_2(X0,sK2(X0,X1),X4)
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(X3,X1)
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_orders_2(X0,X3,X4)
              | ~ r1_orders_2(X0,sK2(X0,X1),X4)
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & r2_hidden(sK2(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r1_orders_2(X0,sK3(X0,X1),X4)
            | ~ r1_orders_2(X0,sK2(X0,X1),X4)
            | ~ r2_hidden(X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X6,X5,X1,X0] :
      ( ? [X7] :
          ( r1_orders_2(X0,X6,X7)
          & r1_orders_2(X0,X5,X7)
          & r2_hidden(X7,X1)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,X6,sK4(X0,X1,X5,X6))
        & r1_orders_2(X0,X5,sK4(X0,X1,X5,X6))
        & r2_hidden(sK4(X0,X1,X5,X6),X1)
        & m1_subset_1(sK4(X0,X1,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ! [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r2_hidden(X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( ? [X7] :
                          ( r1_orders_2(X0,X6,X7)
                          & r1_orders_2(X0,X5,X7)
                          & r2_hidden(X7,X1)
                          & m1_subset_1(X7,u1_struct_0(X0)) )
                      | ~ r2_hidden(X6,X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ v1_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ! [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r2_hidden(X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r2_hidden(X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r2_hidden(X3,X1)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v1_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        & r1_orders_2(X0,X2,X4)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X3,X4)
                                & r1_orders_2(X0,X2,X4)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_waybel_0)).

fof(f59338,plain,
    ( ! [X5] :
        ( ~ r1_orders_2(sK0,X5,sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1)))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X5) )
    | ~ spl9_9335 ),
    inference(avatar_component_clause,[],[f59337])).

fof(f59675,plain,
    ( ~ spl9_4
    | ~ spl9_11
    | ~ spl9_2
    | ~ spl9_57
    | ~ spl9_1691
    | ~ spl9_1552
    | spl9_1803 ),
    inference(avatar_split_clause,[],[f59671,f13260,f11622,f12485,f493,f87,f138,f98])).

fof(f13260,plain,
    ( spl9_1803
  <=> m1_subset_1(sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1803])])).

fof(f59671,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),k3_waybel_0(sK0,sK1))
    | ~ r2_hidden(sK2(sK0,sK1),k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_waybel_0(k3_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl9_1803 ),
    inference(resolution,[],[f13261,f117])).

fof(f117,plain,(
    ! [X6,X0,X5,X1] :
      ( m1_subset_1(sK4(X0,X1,X5,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f54,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f54,plain,(
    ! [X6,X0,X5,X1] :
      ( m1_subset_1(sK4(X0,X1,X5,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13261,plain,
    ( ~ m1_subset_1(sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1)),u1_struct_0(sK0))
    | spl9_1803 ),
    inference(avatar_component_clause,[],[f13260])).

fof(f59648,plain,
    ( ~ spl9_1552
    | ~ spl9_11
    | ~ spl9_2
    | ~ spl9_57
    | ~ spl9_19
    | ~ spl9_1691
    | ~ spl9_4
    | spl9_9334 ),
    inference(avatar_split_clause,[],[f59646,f59334,f98,f12485,f209,f493,f87,f138,f11622])).

fof(f59334,plain,
    ( spl9_9334
  <=> r2_hidden(sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1)),k3_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9334])])).

fof(f59646,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_waybel_0(k3_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK0,sK1),k3_waybel_0(sK0,sK1))
    | ~ spl9_4
    | spl9_9334 ),
    inference(resolution,[],[f59335,f312])).

fof(f312,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK4(sK0,X1,X2,X0),X1)
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v1_waybel_0(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,X1) )
    | ~ spl9_4 ),
    inference(resolution,[],[f55,f99])).

fof(f55,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK4(X0,X1,X5,X6),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f59335,plain,
    ( ~ r2_hidden(sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1)),k3_waybel_0(sK0,sK1))
    | spl9_9334 ),
    inference(avatar_component_clause,[],[f59334])).

fof(f59339,plain,
    ( ~ spl9_9334
    | ~ spl9_1803
    | spl9_9335
    | ~ spl9_1801
    | ~ spl9_9307 ),
    inference(avatar_split_clause,[],[f59271,f59072,f13252,f59337,f13260,f59334])).

fof(f13252,plain,
    ( spl9_1801
  <=> r1_orders_2(sK0,sK3(sK0,sK1),sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1801])])).

fof(f59072,plain,
    ( spl9_9307
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X0)
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k3_waybel_0(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9307])])).

fof(f59271,plain,
    ( ! [X5] :
        ( ~ r1_orders_2(sK0,X5,sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1)))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1)),k3_waybel_0(sK0,sK1)) )
    | ~ spl9_1801
    | ~ spl9_9307 ),
    inference(resolution,[],[f59073,f13253])).

fof(f13253,plain,
    ( r1_orders_2(sK0,sK3(sK0,sK1),sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1)))
    | ~ spl9_1801 ),
    inference(avatar_component_clause,[],[f13252])).

fof(f59073,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK3(sK0,sK1),X1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k3_waybel_0(sK0,sK1)) )
    | ~ spl9_9307 ),
    inference(avatar_component_clause,[],[f59072])).

fof(f59074,plain,
    ( ~ spl9_4
    | ~ spl9_3
    | spl9_9307
    | ~ spl9_3094 ),
    inference(avatar_split_clause,[],[f59070,f22271,f59072,f94,f98])).

fof(f94,plain,
    ( spl9_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f22271,plain,
    ( spl9_3094
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X2)
        | ~ r2_hidden(X2,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,X2))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X1)
        | ~ r1_orders_2(sK0,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3094])])).

fof(f59070,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X1)
        | ~ r2_hidden(X1,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X0)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_3094 ),
    inference(duplicate_literal_removal,[],[f59065])).

fof(f59065,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X1)
        | ~ r2_hidden(X1,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X0)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X1,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_3094 ),
    inference(resolution,[],[f22272,f114])).

fof(f114,plain,(
    ! [X6,X0,X1] :
      ( r1_orders_2(X0,X6,sK7(X0,X1,X6))
      | ~ r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f81,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_waybel_0)).

fof(f81,plain,(
    ! [X6,X0,X1] :
      ( r1_orders_2(X0,X6,sK7(X0,X1,X6))
      | ~ r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,X6,sK7(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k3_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k3_waybel_0(X0,X1) = X2
                  | ( ( ! [X4] :
                          ( ~ r2_hidden(X4,X1)
                          | ~ r1_orders_2(X0,sK5(X0,X1,X2),X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r2_hidden(sK5(X0,X1,X2),X2) )
                    & ( ( r2_hidden(sK6(X0,X1,X2),X1)
                        & r1_orders_2(X0,sK5(X0,X1,X2),sK6(X0,X1,X2))
                        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
                      | r2_hidden(sK5(X0,X1,X2),X2) )
                    & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ! [X7] :
                              ( ~ r2_hidden(X7,X1)
                              | ~ r1_orders_2(X0,X6,X7)
                              | ~ m1_subset_1(X7,u1_struct_0(X0)) ) )
                        & ( ( r2_hidden(sK7(X0,X1,X6),X1)
                            & r1_orders_2(X0,X6,sK7(X0,X1,X6))
                            & m1_subset_1(sK7(X0,X1,X6),u1_struct_0(X0)) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k3_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f39,f42,f41,f40])).

fof(f40,plain,(
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
              | ~ r1_orders_2(X0,sK5(X0,X1,X2),X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r1_orders_2(X0,sK5(X0,X1,X2),X5)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | r2_hidden(sK5(X0,X1,X2),X2) )
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r1_orders_2(X0,sK5(X0,X1,X2),X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( r2_hidden(sK6(X0,X1,X2),X1)
        & r1_orders_2(X0,sK5(X0,X1,X2),sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r1_orders_2(X0,X6,X8)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( r2_hidden(sK7(X0,X1,X6),X1)
        & r1_orders_2(X0,X6,sK7(X0,X1,X6))
        & m1_subset_1(sK7(X0,X1,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_waybel_0)).

fof(f22272,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X2)
        | ~ r2_hidden(X2,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X1)
        | ~ r1_orders_2(sK0,X1,X0) )
    | ~ spl9_3094 ),
    inference(avatar_component_clause,[],[f22271])).

fof(f22274,plain,
    ( ~ spl9_3
    | spl9_3094
    | ~ spl9_4
    | ~ spl9_1941 ),
    inference(avatar_split_clause,[],[f22268,f14085,f98,f22271,f94])).

fof(f14085,plain,
    ( spl9_1941
  <=> ! [X1,X3,X2] :
        ( ~ r1_orders_2(sK0,sK2(sK0,sK1),X1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,X2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X3)
        | ~ r1_orders_2(sK0,X3,sK7(sK0,sK1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k3_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1941])])).

fof(f22268,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X4)
        | ~ r1_orders_2(sK0,X4,X3)
        | ~ r1_orders_2(sK0,X3,sK7(sK0,sK1,X5))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X5,k3_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X5)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_4
    | ~ spl9_1941 ),
    inference(duplicate_literal_removal,[],[f22266])).

fof(f22266,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X4)
        | ~ r1_orders_2(sK0,X4,X3)
        | ~ r1_orders_2(sK0,X3,sK7(sK0,sK1,X5))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X5,k3_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X5)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X5,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl9_4
    | ~ spl9_1941 ),
    inference(resolution,[],[f14086,f151])).

fof(f151,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK7(sK0,X1,X0),X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_4 ),
    inference(resolution,[],[f150,f78])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK7(sK0,X1,X0),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,X1)) )
    | ~ spl9_4 ),
    inference(resolution,[],[f115,f99])).

fof(f115,plain,(
    ! [X6,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK7(X0,X1,X6),X1) ) ),
    inference(subsumption_resolution,[],[f80,f74])).

fof(f80,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k3_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f14086,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(sK7(sK0,sK1,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X1)
        | ~ r1_orders_2(sK0,X1,X3)
        | ~ r1_orders_2(sK0,X3,sK7(sK0,sK1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k3_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_1941 ),
    inference(avatar_component_clause,[],[f14085])).

fof(f14087,plain,
    ( ~ spl9_5
    | ~ spl9_4
    | spl9_1941
    | ~ spl9_1937 ),
    inference(avatar_split_clause,[],[f14078,f14063,f14085,f98,f102])).

fof(f102,plain,
    ( spl9_5
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f14063,plain,
    ( spl9_1937
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,sK1,X0))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X0)
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1937])])).

fof(f14078,plain,
    ( ! [X2,X3,X1] :
        ( ~ r1_orders_2(sK0,sK2(sK0,sK1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X2)
        | ~ r2_hidden(X2,k3_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,X3,sK7(sK0,sK1,X2))
        | ~ r1_orders_2(sK0,X1,X3)
        | ~ m1_subset_1(sK7(sK0,sK1,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0) )
    | ~ spl9_1937 ),
    inference(duplicate_literal_removal,[],[f14075])).

fof(f14075,plain,
    ( ! [X2,X3,X1] :
        ( ~ r1_orders_2(sK0,sK2(sK0,sK1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X2)
        | ~ r2_hidden(X2,k3_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,X3,sK7(sK0,sK1,X2))
        | ~ r1_orders_2(sK0,X1,X3)
        | ~ m1_subset_1(sK7(sK0,sK1,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0) )
    | ~ spl9_1937 ),
    inference(resolution,[],[f14064,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(f14064,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X1,sK7(sK0,sK1,X0))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X0)
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1)) )
    | ~ spl9_1937 ),
    inference(avatar_component_clause,[],[f14063])).

fof(f14065,plain,
    ( ~ spl9_4
    | ~ spl9_3
    | spl9_1937
    | ~ spl9_1795 ),
    inference(avatar_split_clause,[],[f14061,f13211,f14063,f94,f98])).

fof(f13211,plain,
    ( spl9_1795
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k3_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X2)
        | ~ r1_orders_2(sK0,X2,sK7(sK0,sK1,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,X1))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1795])])).

fof(f14061,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,sK1,X0))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_1795 ),
    inference(duplicate_literal_removal,[],[f14056])).

fof(f14056,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK7(sK0,sK1,X0))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X1)
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_1795 ),
    inference(resolution,[],[f13212,f114])).

fof(f13212,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X2,sK7(sK0,sK1,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k3_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK7(sK0,sK1,X1))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X0) )
    | ~ spl9_1795 ),
    inference(avatar_component_clause,[],[f13211])).

fof(f13254,plain,
    ( spl9_7
    | ~ spl9_6
    | ~ spl9_4
    | spl9_23
    | spl9_1801
    | ~ spl9_19
    | ~ spl9_1799 ),
    inference(avatar_split_clause,[],[f13250,f13236,f209,f13252,f237,f98,f106,f110])).

fof(f110,plain,
    ( spl9_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f106,plain,
    ( spl9_6
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f237,plain,
    ( spl9_23
  <=> ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f13236,plain,
    ( spl9_1799
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,X2,sK3(sK0,sK1))
        | r1_orders_2(sK0,X2,sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1799])])).

fof(f13250,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3(sK0,sK1),sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_1799 ),
    inference(duplicate_literal_removal,[],[f13247])).

fof(f13247,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3(sK0,sK1),sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_1799 ),
    inference(resolution,[],[f13237,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f13237,plain,
    ( ! [X2] :
        ( ~ r3_orders_2(sK0,X2,sK3(sK0,sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),X2)) )
    | ~ spl9_1799 ),
    inference(avatar_component_clause,[],[f13236])).

fof(f13238,plain,
    ( spl9_7
    | ~ spl9_6
    | ~ spl9_4
    | ~ spl9_19
    | spl9_1799
    | ~ spl9_1792 ),
    inference(avatar_split_clause,[],[f13229,f13194,f13236,f209,f98,f106,f110])).

fof(f13194,plain,
    ( spl9_1792
  <=> ! [X4] :
        ( r1_orders_2(sK0,X4,sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),X4))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,sK3(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1792])])).

fof(f13229,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),X2))
        | ~ r3_orders_2(sK0,X2,sK3(sK0,sK1))
        | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_1792 ),
    inference(duplicate_literal_removal,[],[f13228])).

fof(f13228,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),X2))
        | ~ r3_orders_2(sK0,X2,sK3(sK0,sK1))
        | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_1792 ),
    inference(resolution,[],[f13195,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f13195,plain,
    ( ! [X4] :
        ( ~ r1_orders_2(sK0,X4,sK3(sK0,sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_orders_2(sK0,X4,sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),X4)) )
    | ~ spl9_1792 ),
    inference(avatar_component_clause,[],[f13194])).

fof(f13214,plain,
    ( ~ spl9_3
    | spl9_1795
    | ~ spl9_4
    | ~ spl9_1692 ),
    inference(avatar_split_clause,[],[f13208,f12489,f98,f13211,f94])).

fof(f12489,plain,
    ( spl9_1692
  <=> ! [X1,X3,X2] :
        ( ~ r2_hidden(X1,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X3)
        | ~ r1_orders_2(sK0,X3,sK7(sK0,sK1,X1))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,sK1,X1))
        | ~ m1_subset_1(sK7(sK0,sK1,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1692])])).

fof(f13208,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X3)
        | ~ r1_orders_2(sK0,X3,sK7(sK0,sK1,X4))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,sK7(sK0,sK1,X4))
        | ~ r2_hidden(X4,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_4
    | ~ spl9_1692 ),
    inference(duplicate_literal_removal,[],[f13206])).

fof(f13206,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X3)
        | ~ r1_orders_2(sK0,X3,sK7(sK0,sK1,X4))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,sK7(sK0,sK1,X4))
        | ~ r2_hidden(X4,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X4,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl9_4
    | ~ spl9_1692 ),
    inference(resolution,[],[f12490,f151])).

fof(f12490,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(sK7(sK0,sK1,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X3)
        | ~ r1_orders_2(sK0,X3,sK7(sK0,sK1,X1))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,sK1,X1))
        | ~ r2_hidden(X1,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_1692 ),
    inference(avatar_component_clause,[],[f12489])).

fof(f13196,plain,
    ( ~ spl9_19
    | spl9_1792
    | ~ spl9_9
    | ~ spl9_1773 ),
    inference(avatar_split_clause,[],[f13182,f13093,f129,f13194,f209])).

fof(f129,plain,
    ( spl9_9
  <=> r2_hidden(sK3(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f13093,plain,
    ( spl9_1773
  <=> ! [X1,X0] :
        ( r1_orders_2(sK0,X0,sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),X0))
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1773])])).

fof(f13182,plain,
    ( ! [X4] :
        ( r1_orders_2(sK0,X4,sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),X4))
        | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,sK3(sK0,sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl9_9
    | ~ spl9_1773 ),
    inference(resolution,[],[f13094,f130])).

fof(f130,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f129])).

fof(f13094,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK1)
        | r1_orders_2(sK0,X0,sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1773 ),
    inference(avatar_component_clause,[],[f13093])).

fof(f13095,plain,
    ( ~ spl9_3
    | spl9_1773
    | ~ spl9_4
    | ~ spl9_1772 ),
    inference(avatar_split_clause,[],[f13091,f13079,f98,f13093,f94])).

fof(f13079,plain,
    ( spl9_1772
  <=> ! [X0] :
        ( r1_orders_2(sK0,X0,sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),X0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1772])])).

fof(f13091,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl9_4
    | ~ spl9_1772 ),
    inference(duplicate_literal_removal,[],[f13082])).

fof(f13082,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl9_4
    | ~ spl9_1772 ),
    inference(resolution,[],[f13080,f152])).

fof(f152,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X2,k3_waybel_0(sK0,X1))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,X1) )
    | ~ spl9_4 ),
    inference(resolution,[],[f116,f99])).

fof(f116,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X7,X1)
      | ~ r1_orders_2(X0,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X6,k3_waybel_0(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f79,f74])).

fof(f79,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r1_orders_2(X0,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f13080,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | r1_orders_2(sK0,X0,sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1772 ),
    inference(avatar_component_clause,[],[f13079])).

fof(f13081,plain,
    ( spl9_7
    | ~ spl9_6
    | ~ spl9_4
    | spl9_23
    | ~ spl9_57
    | spl9_1772
    | ~ spl9_1769 ),
    inference(avatar_split_clause,[],[f13077,f13059,f13079,f493,f237,f98,f106,f110])).

fof(f13059,plain,
    ( spl9_1769
  <=> ! [X3,X4] :
        ( r1_orders_2(sK0,X3,sK4(sK0,k3_waybel_0(sK0,sK1),X4,X3))
        | ~ r3_orders_2(sK0,X4,sK2(sK0,sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,k3_waybel_0(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1769])])).

fof(f13077,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),X0))
        | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_1769 ),
    inference(duplicate_literal_removal,[],[f13074])).

fof(f13074,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,sK4(sK0,k3_waybel_0(sK0,sK1),sK2(sK0,sK1),X0))
        | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_1769 ),
    inference(resolution,[],[f13060,f75])).

fof(f13060,plain,
    ( ! [X4,X3] :
        ( ~ r3_orders_2(sK0,X4,sK2(sK0,sK1))
        | r1_orders_2(sK0,X3,sK4(sK0,k3_waybel_0(sK0,sK1),X4,X3))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,k3_waybel_0(sK0,sK1)) )
    | ~ spl9_1769 ),
    inference(avatar_component_clause,[],[f13059])).

fof(f13061,plain,
    ( spl9_7
    | ~ spl9_6
    | ~ spl9_4
    | ~ spl9_57
    | spl9_1769
    | ~ spl9_1764 ),
    inference(avatar_split_clause,[],[f13052,f13035,f13059,f493,f98,f106,f110])).

fof(f13035,plain,
    ( spl9_1764
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK4(sK0,k3_waybel_0(sK0,sK1),X1,X0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,X1,sK2(sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1764])])).

fof(f13052,plain,
    ( ! [X4,X3] :
        ( r1_orders_2(sK0,X3,sK4(sK0,k3_waybel_0(sK0,sK1),X4,X3))
        | ~ r2_hidden(X3,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,X4,sK2(sK0,sK1))
        | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_1764 ),
    inference(duplicate_literal_removal,[],[f13051])).

fof(f13051,plain,
    ( ! [X4,X3] :
        ( r1_orders_2(sK0,X3,sK4(sK0,k3_waybel_0(sK0,sK1),X4,X3))
        | ~ r2_hidden(X3,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,X4,sK2(sK0,sK1))
        | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_1764 ),
    inference(resolution,[],[f13036,f76])).

fof(f13036,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X1,sK2(sK0,sK1))
        | r1_orders_2(sK0,X0,sK4(sK0,k3_waybel_0(sK0,sK1),X1,X0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_1764 ),
    inference(avatar_component_clause,[],[f13035])).

fof(f13037,plain,
    ( ~ spl9_57
    | spl9_1764
    | ~ spl9_8
    | ~ spl9_1579 ),
    inference(avatar_split_clause,[],[f13025,f11858,f121,f13035,f493])).

fof(f121,plain,
    ( spl9_8
  <=> r2_hidden(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f11858,plain,
    ( spl9_1579
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | r1_orders_2(sK0,X0,sK4(sK0,k3_waybel_0(sK0,sK1),X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1579])])).

fof(f13025,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK2(sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | r1_orders_2(sK0,X0,sK4(sK0,k3_waybel_0(sK0,sK1),X1,X0)) )
    | ~ spl9_8
    | ~ spl9_1579 ),
    inference(resolution,[],[f11859,f122])).

fof(f122,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f11859,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | r1_orders_2(sK0,X0,sK4(sK0,k3_waybel_0(sK0,sK1),X1,X0)) )
    | ~ spl9_1579 ),
    inference(avatar_component_clause,[],[f11858])).

fof(f12516,plain,
    ( ~ spl9_57
    | ~ spl9_1544
    | ~ spl9_8
    | ~ spl9_1694 ),
    inference(avatar_split_clause,[],[f12507,f12504,f121,f11587,f493])).

fof(f12504,plain,
    ( spl9_1694
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,sK2(sK0,sK1),X0)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1694])])).

fof(f12507,plain,
    ( ~ r1_orders_2(sK0,sK2(sK0,sK1),sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl9_8
    | ~ spl9_1694 ),
    inference(resolution,[],[f12505,f122])).

fof(f12505,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1694 ),
    inference(avatar_component_clause,[],[f12504])).

fof(f12506,plain,
    ( ~ spl9_3
    | ~ spl9_57
    | spl9_1694
    | ~ spl9_4
    | spl9_1691 ),
    inference(avatar_split_clause,[],[f12502,f12485,f98,f12504,f493,f94])).

fof(f12502,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl9_4
    | spl9_1691 ),
    inference(resolution,[],[f12486,f152])).

fof(f12486,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k3_waybel_0(sK0,sK1))
    | spl9_1691 ),
    inference(avatar_component_clause,[],[f12485])).

fof(f12491,plain,
    ( ~ spl9_5
    | ~ spl9_4
    | ~ spl9_57
    | spl9_1692
    | ~ spl9_1547 ),
    inference(avatar_split_clause,[],[f12476,f11598,f12489,f493,f98,f102])).

fof(f11598,plain,
    ( spl9_1547
  <=> ! [X18,X19] :
        ( ~ m1_subset_1(X18,u1_struct_0(sK0))
        | ~ r2_hidden(X19,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,X19),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),sK7(sK0,sK1,X19))
        | ~ r1_orders_2(sK0,X18,sK7(sK0,sK1,X19))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X18) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1547])])).

fof(f12476,plain,
    ( ! [X2,X3,X1] :
        ( ~ r2_hidden(X1,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,sK1,X1))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X2)
        | ~ r1_orders_2(sK0,X3,sK7(sK0,sK1,X1))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0) )
    | ~ spl9_1547 ),
    inference(duplicate_literal_removal,[],[f12473])).

fof(f12473,plain,
    ( ! [X2,X3,X1] :
        ( ~ r2_hidden(X1,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK7(sK0,sK1,X1))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X2)
        | ~ r1_orders_2(sK0,X3,sK7(sK0,sK1,X1))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X3)
        | ~ m1_subset_1(sK7(sK0,sK1,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0) )
    | ~ spl9_1547 ),
    inference(resolution,[],[f11599,f72])).

fof(f11599,plain,
    ( ! [X19,X18] :
        ( ~ r1_orders_2(sK0,sK2(sK0,sK1),sK7(sK0,sK1,X19))
        | ~ r2_hidden(X19,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,X19),u1_struct_0(sK0))
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X18,sK7(sK0,sK1,X19))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X18) )
    | ~ spl9_1547 ),
    inference(avatar_component_clause,[],[f11598])).

fof(f11860,plain,
    ( ~ spl9_3
    | spl9_1579
    | ~ spl9_4
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f11856,f678,f98,f11858,f94])).

fof(f678,plain,
    ( spl9_86
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X3,k3_waybel_0(sK0,sK1))
        | r1_orders_2(sK0,X2,sK4(sK0,k3_waybel_0(sK0,sK1),X3,X2))
        | ~ r2_hidden(X2,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_86])])).

fof(f11856,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK4(sK0,k3_waybel_0(sK0,sK1),X1,X0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl9_4
    | ~ spl9_86 ),
    inference(duplicate_literal_removal,[],[f11846])).

fof(f11846,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK4(sK0,k3_waybel_0(sK0,sK1),X1,X0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl9_4
    | ~ spl9_86 ),
    inference(resolution,[],[f679,f152])).

fof(f679,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK4(sK0,k3_waybel_0(sK0,sK1),X3,X2))
        | ~ r2_hidden(X2,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl9_86 ),
    inference(avatar_component_clause,[],[f678])).

fof(f11752,plain,
    ( spl9_7
    | ~ spl9_6
    | ~ spl9_4
    | ~ spl9_19
    | spl9_23
    | spl9_1568 ),
    inference(avatar_split_clause,[],[f11749,f11746,f237,f209,f98,f106,f110])).

fof(f11746,plain,
    ( spl9_1568
  <=> r3_orders_2(sK0,sK3(sK0,sK1),sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1568])])).

fof(f11749,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl9_1568 ),
    inference(resolution,[],[f11747,f75])).

fof(f11747,plain,
    ( ~ r3_orders_2(sK0,sK3(sK0,sK1),sK3(sK0,sK1))
    | spl9_1568 ),
    inference(avatar_component_clause,[],[f11746])).

fof(f11748,plain,
    ( spl9_7
    | ~ spl9_6
    | ~ spl9_4
    | ~ spl9_19
    | ~ spl9_1568
    | spl9_1555 ),
    inference(avatar_split_clause,[],[f11739,f11650,f11746,f209,f98,f106,f110])).

fof(f11650,plain,
    ( spl9_1555
  <=> r1_orders_2(sK0,sK3(sK0,sK1),sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1555])])).

fof(f11739,plain,
    ( ~ r3_orders_2(sK0,sK3(sK0,sK1),sK3(sK0,sK1))
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl9_1555 ),
    inference(duplicate_literal_removal,[],[f11738])).

fof(f11738,plain,
    ( ~ r3_orders_2(sK0,sK3(sK0,sK1),sK3(sK0,sK1))
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl9_1555 ),
    inference(resolution,[],[f11651,f76])).

fof(f11651,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,sK1),sK3(sK0,sK1))
    | spl9_1555 ),
    inference(avatar_component_clause,[],[f11650])).

fof(f11691,plain,
    ( spl9_7
    | ~ spl9_6
    | ~ spl9_4
    | ~ spl9_57
    | spl9_23
    | spl9_1549 ),
    inference(avatar_split_clause,[],[f11688,f11610,f237,f493,f98,f106,f110])).

fof(f11610,plain,
    ( spl9_1549
  <=> r3_orders_2(sK0,sK2(sK0,sK1),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1549])])).

fof(f11688,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl9_1549 ),
    inference(resolution,[],[f11611,f75])).

fof(f11611,plain,
    ( ~ r3_orders_2(sK0,sK2(sK0,sK1),sK2(sK0,sK1))
    | spl9_1549 ),
    inference(avatar_component_clause,[],[f11610])).

fof(f11652,plain,
    ( ~ spl9_19
    | ~ spl9_1555
    | ~ spl9_9
    | ~ spl9_1553 ),
    inference(avatar_split_clause,[],[f11638,f11633,f129,f11650,f209])).

fof(f11633,plain,
    ( spl9_1553
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,sK3(sK0,sK1),X0)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1553])])).

fof(f11638,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,sK1),sK3(sK0,sK1))
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl9_9
    | ~ spl9_1553 ),
    inference(resolution,[],[f11634,f130])).

fof(f11634,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1553 ),
    inference(avatar_component_clause,[],[f11633])).

fof(f11635,plain,
    ( ~ spl9_3
    | ~ spl9_19
    | spl9_1553
    | ~ spl9_4
    | spl9_1552 ),
    inference(avatar_split_clause,[],[f11631,f11622,f98,f11633,f209,f94])).

fof(f11631,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK3(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl9_4
    | spl9_1552 ),
    inference(resolution,[],[f11623,f152])).

fof(f11623,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),k3_waybel_0(sK0,sK1))
    | spl9_1552 ),
    inference(avatar_component_clause,[],[f11622])).

fof(f11612,plain,
    ( spl9_7
    | ~ spl9_6
    | ~ spl9_4
    | ~ spl9_57
    | ~ spl9_1549
    | spl9_1544 ),
    inference(avatar_split_clause,[],[f11603,f11587,f11610,f493,f98,f106,f110])).

fof(f11603,plain,
    ( ~ r3_orders_2(sK0,sK2(sK0,sK1),sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl9_1544 ),
    inference(duplicate_literal_removal,[],[f11602])).

fof(f11602,plain,
    ( ~ r3_orders_2(sK0,sK2(sK0,sK1),sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl9_1544 ),
    inference(resolution,[],[f11588,f76])).

fof(f11588,plain,
    ( ~ r1_orders_2(sK0,sK2(sK0,sK1),sK2(sK0,sK1))
    | spl9_1544 ),
    inference(avatar_component_clause,[],[f11587])).

fof(f11600,plain,
    ( ~ spl9_3
    | spl9_1547
    | ~ spl9_4
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f11585,f212,f98,f11598,f94])).

fof(f212,plain,
    ( spl9_20
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK0,sK2(sK0,sK1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f11585,plain,
    ( ! [X19,X18] :
        ( ~ m1_subset_1(X18,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X18)
        | ~ r1_orders_2(sK0,X18,sK7(sK0,sK1,X19))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),sK7(sK0,sK1,X19))
        | ~ m1_subset_1(sK7(sK0,sK1,X19),u1_struct_0(sK0))
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X19,k3_waybel_0(sK0,sK1)) )
    | ~ spl9_4
    | ~ spl9_20 ),
    inference(resolution,[],[f213,f150])).

fof(f213,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f212])).

fof(f11207,plain,
    ( ~ spl9_11
    | spl9_86
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f11202,f98,f87,f678,f138])).

fof(f11202,plain,
    ( ! [X12,X11] :
        ( ~ r2_hidden(X11,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r2_hidden(X12,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_orders_2(sK0,X12,sK4(sK0,k3_waybel_0(sK0,sK1),X11,X12)) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(resolution,[],[f91,f476])).

fof(f476,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_waybel_0(X1,sK0)
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_orders_2(sK0,X0,sK4(sK0,X1,X2,X0)) )
    | ~ spl9_4 ),
    inference(resolution,[],[f57,f99])).

fof(f57,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_orders_2(X0,X6,sK4(X0,X1,X5,X6)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,
    ( v1_waybel_0(k3_waybel_0(sK0,sK1),sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f11135,plain,
    ( ~ spl9_25
    | ~ spl9_12
    | ~ spl9_3
    | ~ spl9_4
    | spl9_1463 ),
    inference(avatar_split_clause,[],[f11133,f11119,f98,f94,f142,f247])).

fof(f247,plain,
    ( spl9_25
  <=> m1_subset_1(sK2(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f142,plain,
    ( spl9_12
  <=> r2_hidden(sK2(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f11119,plain,
    ( spl9_1463
  <=> m1_subset_1(sK7(sK0,sK1,sK2(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1463])])).

fof(f11133,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl9_4
    | spl9_1463 ),
    inference(duplicate_literal_removal,[],[f11131])).

fof(f11131,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl9_4
    | spl9_1463 ),
    inference(resolution,[],[f11120,f151])).

fof(f11120,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0))
    | spl9_1463 ),
    inference(avatar_component_clause,[],[f11119])).

fof(f11121,plain,
    ( ~ spl9_4
    | ~ spl9_3
    | ~ spl9_1463
    | ~ spl9_25
    | ~ spl9_12
    | ~ spl9_1462 ),
    inference(avatar_split_clause,[],[f11117,f11109,f142,f247,f11119,f94,f98])).

fof(f11109,plain,
    ( spl9_1462
  <=> ! [X10] :
        ( ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),sK7(sK0,sK1,X10))
        | ~ r2_hidden(X10,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,X10),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1462])])).

fof(f11117,plain,
    ( ~ r2_hidden(sK2(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK1,sK2(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1462 ),
    inference(duplicate_literal_removal,[],[f11112])).

fof(f11112,plain,
    ( ~ r2_hidden(sK2(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK1,sK2(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ r2_hidden(sK2(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1462 ),
    inference(resolution,[],[f11110,f114])).

fof(f11110,plain,
    ( ! [X10] :
        ( ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),sK7(sK0,sK1,X10))
        | ~ r2_hidden(X10,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,X10),u1_struct_0(sK0)) )
    | ~ spl9_1462 ),
    inference(avatar_component_clause,[],[f11109])).

fof(f11111,plain,
    ( ~ spl9_3
    | spl9_1462
    | ~ spl9_4
    | ~ spl9_1459 ),
    inference(avatar_split_clause,[],[f11099,f11089,f98,f11109,f94])).

fof(f11089,plain,
    ( spl9_1459
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1459])])).

fof(f11099,plain,
    ( ! [X10] :
        ( ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),sK7(sK0,sK1,X10))
        | ~ m1_subset_1(sK7(sK0,sK1,X10),u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X10,k3_waybel_0(sK0,sK1)) )
    | ~ spl9_4
    | ~ spl9_1459 ),
    inference(resolution,[],[f11090,f150])).

fof(f11090,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1459 ),
    inference(avatar_component_clause,[],[f11089])).

fof(f11092,plain,
    ( ~ spl9_90
    | ~ spl9_3
    | ~ spl9_1
    | ~ spl9_85
    | spl9_1459
    | ~ spl9_4
    | ~ spl9_1458 ),
    inference(avatar_split_clause,[],[f11086,f11080,f98,f11089,f674,f84,f94,f711])).

fof(f711,plain,
    ( spl9_90
  <=> r2_hidden(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_90])])).

fof(f84,plain,
    ( spl9_1
  <=> v1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f674,plain,
    ( spl9_85
  <=> m1_subset_1(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_85])])).

fof(f11080,plain,
    ( spl9_1458
  <=> ! [X0] :
        ( ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1458])])).

fof(f11086,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X1)
        | ~ m1_subset_1(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0))
        | ~ v1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),sK1) )
    | ~ spl9_4
    | ~ spl9_1458 ),
    inference(duplicate_literal_removal,[],[f11084])).

fof(f11084,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0))
        | ~ v1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),sK1) )
    | ~ spl9_4
    | ~ spl9_1458 ),
    inference(resolution,[],[f11081,f329])).

fof(f329,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(sK4(sK0,X1,X0,X2),X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_waybel_0(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
        | ~ r2_hidden(X0,X1) )
    | ~ spl9_4 ),
    inference(resolution,[],[f312,f78])).

fof(f11081,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0) )
    | ~ spl9_1458 ),
    inference(avatar_component_clause,[],[f11080])).

fof(f11082,plain,
    ( ~ spl9_3
    | ~ spl9_1
    | ~ spl9_85
    | ~ spl9_90
    | spl9_1458
    | ~ spl9_4
    | ~ spl9_1455 ),
    inference(avatar_split_clause,[],[f11078,f11065,f98,f11080,f711,f674,f84,f94])).

fof(f11065,plain,
    ( spl9_1455
  <=> ! [X0] :
        ( ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),sK1)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1455])])).

fof(f11078,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),sK1)
        | ~ m1_subset_1(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0))
        | ~ v1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_4
    | ~ spl9_1455 ),
    inference(duplicate_literal_removal,[],[f11077])).

fof(f11077,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0))
        | ~ v1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl9_4
    | ~ spl9_1455 ),
    inference(resolution,[],[f11066,f312])).

fof(f11066,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),sK1)
        | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl9_1455 ),
    inference(avatar_component_clause,[],[f11065])).

fof(f11067,plain,
    ( spl9_1180
    | spl9_1455
    | ~ spl9_69
    | ~ spl9_1454 ),
    inference(avatar_split_clause,[],[f11063,f11054,f561,f11065,f8850])).

fof(f8850,plain,
    ( spl9_1180
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1180])])).

fof(f561,plain,
    ( spl9_69
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | r1_orders_2(sK0,X1,sK4(sK0,sK1,sK7(sK0,sK1,X0),X1))
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).

fof(f11054,plain,
    ( spl9_1454
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X2),sK4(sK0,sK1,sK7(sK0,sK1,X0),X1))
        | ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X2)
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1454])])).

fof(f11063,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),u1_struct_0(sK0))
        | ~ r2_hidden(X1,k3_waybel_0(sK0,sK1))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ r2_hidden(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_69
    | ~ spl9_1454 ),
    inference(duplicate_literal_removal,[],[f11058])).

fof(f11058,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),u1_struct_0(sK0))
        | ~ r2_hidden(X1,k3_waybel_0(sK0,sK1))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ r2_hidden(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k3_waybel_0(sK0,sK1))
        | ~ r2_hidden(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),sK1)
        | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_69
    | ~ spl9_1454 ),
    inference(resolution,[],[f11055,f562])).

fof(f562,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X1,sK4(sK0,sK1,sK7(sK0,sK1,X0),X1))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_69 ),
    inference(avatar_component_clause,[],[f561])).

fof(f11055,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X2),sK4(sK0,sK1,sK7(sK0,sK1,X0),X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X2)
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1454 ),
    inference(avatar_component_clause,[],[f11054])).

fof(f11057,plain,
    ( ~ spl9_3
    | spl9_1454
    | ~ spl9_4
    | ~ spl9_1451 ),
    inference(avatar_split_clause,[],[f11051,f11032,f98,f11054,f94])).

fof(f11032,plain,
    ( spl9_1451
  <=> ! [X22,X23,X24] :
        ( ~ m1_subset_1(X22,u1_struct_0(sK0))
        | ~ r2_hidden(X23,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X23,u1_struct_0(sK0))
        | ~ r2_hidden(X22,sK1)
        | ~ r2_hidden(X24,sK1)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X24)
        | ~ m1_subset_1(X24,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X24),sK4(sK0,sK1,sK7(sK0,sK1,X23),X22))
        | ~ m1_subset_1(sK7(sK0,sK1,X23),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1451])])).

fof(f11051,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(X3,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,sK1)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X5),sK4(sK0,sK1,sK7(sK0,sK1,X3),X4))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_4
    | ~ spl9_1451 ),
    inference(duplicate_literal_removal,[],[f11049])).

fof(f11049,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(X3,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,sK1)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X5),sK4(sK0,sK1,sK7(sK0,sK1,X3),X4))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X3,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl9_4
    | ~ spl9_1451 ),
    inference(resolution,[],[f11033,f151])).

fof(f11033,plain,
    ( ! [X24,X23,X22] :
        ( ~ m1_subset_1(sK7(sK0,sK1,X23),u1_struct_0(sK0))
        | ~ r2_hidden(X23,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X23,u1_struct_0(sK0))
        | ~ r2_hidden(X22,sK1)
        | ~ r2_hidden(X24,sK1)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X24)
        | ~ m1_subset_1(X24,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X24),sK4(sK0,sK1,sK7(sK0,sK1,X23),X22))
        | ~ m1_subset_1(X22,u1_struct_0(sK0)) )
    | ~ spl9_1451 ),
    inference(avatar_component_clause,[],[f11032])).

fof(f11034,plain,
    ( ~ spl9_3
    | spl9_1451
    | ~ spl9_4
    | ~ spl9_1448 ),
    inference(avatar_split_clause,[],[f11022,f11012,f98,f11032,f94])).

fof(f11012,plain,
    ( spl9_1448
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X2),sK4(sK0,sK1,X1,X0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X2)
        | ~ r2_hidden(X2,sK1)
        | ~ r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1448])])).

fof(f11022,plain,
    ( ! [X24,X23,X22] :
        ( ~ m1_subset_1(X22,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,X23),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X24),sK4(sK0,sK1,sK7(sK0,sK1,X23),X22))
        | ~ m1_subset_1(X24,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X24)
        | ~ r2_hidden(X24,sK1)
        | ~ r2_hidden(X22,sK1)
        | ~ m1_subset_1(X23,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X23,k3_waybel_0(sK0,sK1)) )
    | ~ spl9_4
    | ~ spl9_1448 ),
    inference(resolution,[],[f11013,f150])).

fof(f11013,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X2),sK4(sK0,sK1,X1,X0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X2)
        | ~ r2_hidden(X2,sK1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl9_1448 ),
    inference(avatar_component_clause,[],[f11012])).

fof(f11015,plain,
    ( ~ spl9_3
    | ~ spl9_1
    | spl9_1448
    | ~ spl9_4
    | ~ spl9_1441 ),
    inference(avatar_split_clause,[],[f11009,f10967,f98,f11012,f84,f94])).

fof(f10967,plain,
    ( spl9_1441
  <=> ! [X7,X8,X6] :
        ( ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X6),sK4(sK0,sK1,X7,X8))
        | ~ r2_hidden(X8,sK1)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r2_hidden(X7,sK1)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,sK1)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X6)
        | ~ m1_subset_1(sK4(sK0,sK1,X7,X8),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1441])])).

fof(f11009,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X5,sK1)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X5)
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X5),sK4(sK0,sK1,X4,X3))
        | ~ v1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_4
    | ~ spl9_1441 ),
    inference(duplicate_literal_removal,[],[f11007])).

fof(f11007,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X5,sK1)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X5)
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X5),sK4(sK0,sK1,X4,X3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ v1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl9_4
    | ~ spl9_1441 ),
    inference(resolution,[],[f10968,f329])).

fof(f10968,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(sK4(sK0,sK1,X7,X8),u1_struct_0(sK0))
        | ~ r2_hidden(X8,sK1)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r2_hidden(X7,sK1)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,sK1)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X6)
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X6),sK4(sK0,sK1,X7,X8)) )
    | ~ spl9_1441 ),
    inference(avatar_component_clause,[],[f10967])).

fof(f10969,plain,
    ( ~ spl9_3
    | ~ spl9_1
    | spl9_1441
    | ~ spl9_4
    | ~ spl9_1438 ),
    inference(avatar_split_clause,[],[f10961,f10947,f98,f10967,f84,f94])).

fof(f10947,plain,
    ( spl9_1438
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),X1)
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1438])])).

fof(f10961,plain,
    ( ! [X6,X8,X7] :
        ( ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X6),sK4(sK0,sK1,X7,X8))
        | ~ m1_subset_1(sK4(sK0,sK1,X7,X8),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X6)
        | ~ r2_hidden(X6,sK1)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X7,sK1)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ v1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X8,sK1) )
    | ~ spl9_4
    | ~ spl9_1438 ),
    inference(resolution,[],[f10948,f312])).

fof(f10948,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1438 ),
    inference(avatar_component_clause,[],[f10947])).

fof(f10949,plain,
    ( ~ spl9_15
    | ~ spl9_10
    | spl9_1438
    | ~ spl9_69
    | ~ spl9_1437 ),
    inference(avatar_split_clause,[],[f10945,f10932,f561,f10947,f135,f179])).

fof(f179,plain,
    ( spl9_15
  <=> m1_subset_1(sK3(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f135,plain,
    ( spl9_10
  <=> r2_hidden(sK3(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f10932,plain,
    ( spl9_1437
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X2),X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1)
        | ~ r1_orders_2(sK0,X0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X2))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1437])])).

fof(f10945,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(sK3(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(sK3(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0)) )
    | ~ spl9_69
    | ~ spl9_1437 ),
    inference(duplicate_literal_removal,[],[f10936])).

fof(f10936,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(sK3(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0)) )
    | ~ spl9_69
    | ~ spl9_1437 ),
    inference(resolution,[],[f10933,f562])).

fof(f10933,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X2))
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X2),X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl9_1437 ),
    inference(avatar_component_clause,[],[f10932])).

fof(f10935,plain,
    ( ~ spl9_90
    | ~ spl9_3
    | ~ spl9_1
    | ~ spl9_85
    | spl9_1437
    | ~ spl9_4
    | ~ spl9_1151 ),
    inference(avatar_split_clause,[],[f10929,f8552,f98,f10932,f674,f84,f94,f711])).

fof(f8552,plain,
    ( spl9_1151
  <=> ! [X3,X5,X4] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X4),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X5)
        | ~ r1_orders_2(sK0,X5,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X4))
        | ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK1)
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X4),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1151])])).

fof(f10929,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X3)
        | ~ r1_orders_2(sK0,X3,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X5))
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1)
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X5),X4)
        | ~ m1_subset_1(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0))
        | ~ v1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),sK1) )
    | ~ spl9_4
    | ~ spl9_1151 ),
    inference(duplicate_literal_removal,[],[f10927])).

fof(f10927,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X3)
        | ~ r1_orders_2(sK0,X3,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X5))
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1)
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X5),X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0))
        | ~ v1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),sK1) )
    | ~ spl9_4
    | ~ spl9_1151 ),
    inference(resolution,[],[f8553,f329])).

fof(f8553,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X4),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X5)
        | ~ r1_orders_2(sK0,X5,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X4))
        | ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK1)
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X4),X3) )
    | ~ spl9_1151 ),
    inference(avatar_component_clause,[],[f8552])).

fof(f8869,plain,
    ( ~ spl9_25
    | ~ spl9_12
    | ~ spl9_1180 ),
    inference(avatar_split_clause,[],[f8855,f8850,f142,f247])).

fof(f8855,plain,
    ( ~ m1_subset_1(sK2(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl9_12
    | ~ spl9_1180 ),
    inference(resolution,[],[f8851,f143])).

fof(f143,plain,
    ( r2_hidden(sK2(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f8851,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1180 ),
    inference(avatar_component_clause,[],[f8850])).

fof(f8554,plain,
    ( ~ spl9_5
    | ~ spl9_4
    | ~ spl9_25
    | spl9_1151
    | ~ spl9_1150 ),
    inference(avatar_split_clause,[],[f8547,f8541,f8552,f247,f98,f102])).

fof(f8541,plain,
    ( spl9_1150
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),X1)
        | ~ r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1150])])).

fof(f8547,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X4),X3)
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1)
        | ~ r1_orders_2(sK0,X5,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X4))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X5)
        | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X4),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0) )
    | ~ spl9_1150 ),
    inference(resolution,[],[f8542,f72])).

fof(f8542,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0),X1)
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl9_1150 ),
    inference(avatar_component_clause,[],[f8541])).

fof(f8544,plain,
    ( ~ spl9_90
    | ~ spl9_3
    | ~ spl9_1
    | ~ spl9_85
    | spl9_1150
    | ~ spl9_4
    | ~ spl9_1148 ),
    inference(avatar_split_clause,[],[f8538,f8528,f98,f8541,f674,f84,f94,f711])).

fof(f8528,plain,
    ( spl9_1148
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1))
        | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1148])])).

fof(f8538,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X2))
        | ~ r2_hidden(X3,sK1)
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X2),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0))
        | ~ v1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),sK1) )
    | ~ spl9_4
    | ~ spl9_1148 ),
    inference(duplicate_literal_removal,[],[f8536])).

fof(f8536,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X2))
        | ~ r2_hidden(X3,sK1)
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X2),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0))
        | ~ v1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),sK1) )
    | ~ spl9_4
    | ~ spl9_1148 ),
    inference(resolution,[],[f8529,f329])).

fof(f8529,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1))
        | ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1148 ),
    inference(avatar_component_clause,[],[f8528])).

fof(f8530,plain,
    ( ~ spl9_10
    | ~ spl9_15
    | ~ spl9_3
    | ~ spl9_1
    | spl9_1148
    | ~ spl9_4
    | ~ spl9_770 ),
    inference(avatar_split_clause,[],[f8526,f5756,f98,f8528,f84,f94,f179,f135])).

fof(f5756,plain,
    ( spl9_770
  <=> ! [X1,X3,X2] :
        ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,X2,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),X3)
        | ~ m1_subset_1(sK4(sK0,X2,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),sK4(sK0,X2,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1))
        | ~ r2_hidden(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v1_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_770])])).

fof(f8526,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),X0)
        | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1))
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK3(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(sK3(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1)) )
    | ~ spl9_4
    | ~ spl9_770 ),
    inference(duplicate_literal_removal,[],[f8524])).

fof(f8524,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),X0)
        | ~ m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1))
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK3(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK3(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1)) )
    | ~ spl9_4
    | ~ spl9_770 ),
    inference(resolution,[],[f5757,f150])).

fof(f5757,plain,
    ( ! [X2,X3,X1] :
        ( ~ r2_hidden(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X2)
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,X2,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),X3)
        | ~ m1_subset_1(sK4(sK0,X2,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),sK4(sK0,X2,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1))
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v1_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_770 ),
    inference(avatar_component_clause,[],[f5756])).

fof(f5758,plain,
    ( ~ spl9_3
    | spl9_770
    | ~ spl9_4
    | ~ spl9_88 ),
    inference(avatar_split_clause,[],[f5753,f703,f98,f5756,f94])).

fof(f703,plain,
    ( spl9_88
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),sK4(sK0,X0,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1))
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0)
        | ~ r2_hidden(sK4(sK0,X0,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(sK4(sK0,X0,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f5753,plain,
    ( ! [X2,X3,X1] :
        ( ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X2,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X2)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),sK4(sK0,X2,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1))
        | ~ m1_subset_1(sK4(sK0,X2,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,X2,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl9_4
    | ~ spl9_88 ),
    inference(duplicate_literal_removal,[],[f5752])).

fof(f5752,plain,
    ( ! [X2,X3,X1] :
        ( ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X2,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X2)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),sK4(sK0,X2,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1))
        | ~ m1_subset_1(sK4(sK0,X2,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK4(sK0,X2,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,X2,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl9_4
    | ~ spl9_88 ),
    inference(resolution,[],[f704,f152])).

fof(f704,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(sK0,X0,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),k3_waybel_0(sK0,sK1))
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),sK4(sK0,X0,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1))
        | ~ m1_subset_1(sK4(sK0,X0,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),u1_struct_0(sK0)) )
    | ~ spl9_88 ),
    inference(avatar_component_clause,[],[f703])).

fof(f754,plain,
    ( ~ spl9_10
    | ~ spl9_3
    | ~ spl9_15
    | ~ spl9_4
    | spl9_90 ),
    inference(avatar_split_clause,[],[f753,f711,f98,f179,f94,f135])).

fof(f753,plain,
    ( ~ m1_subset_1(sK3(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1))
    | ~ spl9_4
    | spl9_90 ),
    inference(resolution,[],[f712,f150])).

fof(f712,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),sK1)
    | spl9_90 ),
    inference(avatar_component_clause,[],[f711])).

fof(f705,plain,
    ( ~ spl9_85
    | spl9_88
    | ~ spl9_4
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f691,f671,f98,f703,f674])).

fof(f671,plain,
    ( spl9_84
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0)
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).

fof(f691,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),sK4(sK0,X0,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1))
        | ~ m1_subset_1(sK4(sK0,X0,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),u1_struct_0(sK0))
        | ~ r2_hidden(sK4(sK0,X0,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X1),k3_waybel_0(sK0,sK1))
        | ~ r2_hidden(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0))
        | ~ v1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,X0) )
    | ~ spl9_4
    | ~ spl9_84 ),
    inference(resolution,[],[f672,f384])).

fof(f672,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1)) )
    | ~ spl9_84 ),
    inference(avatar_component_clause,[],[f671])).

fof(f690,plain,
    ( ~ spl9_15
    | ~ spl9_10
    | ~ spl9_3
    | ~ spl9_4
    | spl9_85 ),
    inference(avatar_split_clause,[],[f688,f674,f98,f94,f135,f179])).

fof(f688,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK3(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl9_4
    | spl9_85 ),
    inference(duplicate_literal_removal,[],[f686])).

fof(f686,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl9_4
    | spl9_85 ),
    inference(resolution,[],[f675,f151])).

fof(f675,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0))
    | spl9_85 ),
    inference(avatar_component_clause,[],[f674])).

fof(f676,plain,
    ( spl9_84
    | ~ spl9_85
    | ~ spl9_3
    | ~ spl9_10
    | ~ spl9_37 ),
    inference(avatar_split_clause,[],[f666,f344,f135,f94,f674,f671])).

fof(f344,plain,
    ( spl9_37
  <=> ! [X5,X6] :
        ( ~ m1_subset_1(sK7(sK0,X5,sK3(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK3(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,X5))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,k3_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,sK7(sK0,X5,sK3(sK0,k3_waybel_0(sK0,sK1))),X6)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f666,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK3(sK0,k3_waybel_0(sK0,sK1))),X0)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0) )
    | ~ spl9_10
    | ~ spl9_37 ),
    inference(resolution,[],[f345,f136])).

fof(f136,plain,
    ( r2_hidden(sK3(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f135])).

fof(f345,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(sK3(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,X5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK7(sK0,X5,sK3(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,k3_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,sK7(sK0,X5,sK3(sK0,k3_waybel_0(sK0,sK1))),X6)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X6) )
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f344])).

fof(f564,plain,
    ( ~ spl9_3
    | spl9_69
    | ~ spl9_4
    | ~ spl9_61 ),
    inference(avatar_split_clause,[],[f558,f508,f98,f561,f94])).

fof(f508,plain,
    ( spl9_61
  <=> ! [X7,X6] :
        ( r1_orders_2(sK0,X6,sK4(sK0,sK1,sK7(sK0,sK1,X7),X6))
        | ~ r2_hidden(X7,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r2_hidden(X6,sK1)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,X7),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).

fof(f558,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X3,sK4(sK0,sK1,sK7(sK0,sK1,X2),X3))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_4
    | ~ spl9_61 ),
    inference(duplicate_literal_removal,[],[f556])).

fof(f556,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X3,sK4(sK0,sK1,sK7(sK0,sK1,X2),X3))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl9_4
    | ~ spl9_61 ),
    inference(resolution,[],[f509,f151])).

fof(f509,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(sK7(sK0,sK1,X7),u1_struct_0(sK0))
        | ~ r2_hidden(X7,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r2_hidden(X6,sK1)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r1_orders_2(sK0,X6,sK4(sK0,sK1,sK7(sK0,sK1,X7),X6)) )
    | ~ spl9_61 ),
    inference(avatar_component_clause,[],[f508])).

fof(f514,plain,
    ( ~ spl9_3
    | ~ spl9_8
    | spl9_57 ),
    inference(avatar_split_clause,[],[f512,f493,f121,f94])).

fof(f512,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_8
    | spl9_57 ),
    inference(resolution,[],[f494,f126])).

fof(f126,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl9_8 ),
    inference(resolution,[],[f122,f78])).

fof(f494,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | spl9_57 ),
    inference(avatar_component_clause,[],[f493])).

fof(f510,plain,
    ( ~ spl9_3
    | spl9_61
    | ~ spl9_4
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f491,f485,f98,f508,f94])).

fof(f485,plain,
    ( spl9_56
  <=> ! [X11,X10] :
        ( ~ r2_hidden(X10,sK1)
        | r1_orders_2(sK0,X11,sK4(sK0,sK1,X10,X11))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r2_hidden(X11,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f491,plain,
    ( ! [X6,X7] :
        ( r1_orders_2(sK0,X6,sK4(sK0,sK1,sK7(sK0,sK1,X7),X6))
        | ~ m1_subset_1(sK7(sK0,sK1,X7),u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(X6,sK1)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X7,k3_waybel_0(sK0,sK1)) )
    | ~ spl9_4
    | ~ spl9_56 ),
    inference(resolution,[],[f486,f150])).

fof(f486,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(X10,sK1)
        | r1_orders_2(sK0,X11,sK4(sK0,sK1,X10,X11))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r2_hidden(X11,sK1) )
    | ~ spl9_56 ),
    inference(avatar_component_clause,[],[f485])).

fof(f487,plain,
    ( ~ spl9_3
    | spl9_56
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f480,f98,f84,f485,f94])).

fof(f480,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(X10,sK1)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r2_hidden(X11,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_orders_2(sK0,X11,sK4(sK0,sK1,X10,X11)) )
    | ~ spl9_1
    | ~ spl9_4 ),
    inference(resolution,[],[f476,f90])).

fof(f90,plain,
    ( v1_waybel_0(sK1,sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f346,plain,
    ( ~ spl9_4
    | ~ spl9_15
    | spl9_37
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f332,f182,f344,f179,f98])).

fof(f182,plain,
    ( spl9_16
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3(sK0,k3_waybel_0(sK0,sK1)),X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f332,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(sK7(sK0,X5,sK3(sK0,k3_waybel_0(sK0,sK1))),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X6)
        | ~ r1_orders_2(sK0,sK7(sK0,X5,sK3(sK0,k3_waybel_0(sK0,sK1))),X6)
        | ~ r2_hidden(X6,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_hidden(sK3(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,X5))
        | ~ m1_subset_1(sK3(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_16 ),
    inference(resolution,[],[f183,f114])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK3(sK0,k3_waybel_0(sK0,sK1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f182])).

fof(f274,plain,(
    ~ spl9_23 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | ~ spl9_23 ),
    inference(resolution,[],[f238,f73])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(sK8(X0),X0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK8(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f4,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f238,plain,
    ( ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f237])).

fof(f260,plain,
    ( ~ spl9_4
    | ~ spl9_11
    | spl9_2
    | spl9_25 ),
    inference(avatar_split_clause,[],[f257,f247,f87,f138,f98])).

fof(f257,plain,
    ( v1_waybel_0(k3_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl9_25 ),
    inference(resolution,[],[f248,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f248,plain,
    ( ~ m1_subset_1(sK2(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | spl9_25 ),
    inference(avatar_component_clause,[],[f247])).

fof(f226,plain,
    ( ~ spl9_4
    | ~ spl9_3
    | spl9_1
    | spl9_19 ),
    inference(avatar_split_clause,[],[f223,f209,f84,f94,f98])).

fof(f223,plain,
    ( v1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl9_19 ),
    inference(resolution,[],[f210,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f210,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | spl9_19 ),
    inference(avatar_component_clause,[],[f209])).

fof(f214,plain,
    ( ~ spl9_5
    | ~ spl9_4
    | ~ spl9_19
    | spl9_20
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f207,f164,f212,f209,f98,f102])).

fof(f164,plain,
    ( spl9_14
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,sK2(sK0,sK1),X0)
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK2(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0) )
    | ~ spl9_14 ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK2(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0) )
    | ~ spl9_14 ),
    inference(resolution,[],[f165,f72])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK3(sK0,sK1),X0)
        | ~ r1_orders_2(sK0,sK2(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f164])).

fof(f198,plain,
    ( ~ spl9_4
    | ~ spl9_11
    | spl9_2
    | spl9_15 ),
    inference(avatar_split_clause,[],[f195,f179,f87,f138,f98])).

fof(f195,plain,
    ( v1_waybel_0(k3_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl9_15 ),
    inference(resolution,[],[f180,f59])).

fof(f180,plain,
    ( ~ m1_subset_1(sK3(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | spl9_15 ),
    inference(avatar_component_clause,[],[f179])).

fof(f184,plain,
    ( ~ spl9_5
    | ~ spl9_4
    | ~ spl9_15
    | spl9_16
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f176,f157,f182,f179,f98,f102])).

fof(f157,plain,
    ( spl9_13
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ r1_orders_2(sK0,sK3(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f176,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,sK3(sK0,k3_waybel_0(sK0,sK1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0) )
    | ~ spl9_13 ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,sK3(sK0,k3_waybel_0(sK0,sK1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,k3_waybel_0(sK0,sK1)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0) )
    | ~ spl9_13 ),
    inference(resolution,[],[f158,f72])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK3(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1)) )
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f157])).

fof(f166,plain,
    ( ~ spl9_3
    | spl9_14
    | spl9_1
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f160,f98,f84,f164,f94])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2(sK0,sK1),X0)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1),X0) )
    | spl9_1
    | ~ spl9_4 ),
    inference(resolution,[],[f85,f154])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( v1_waybel_0(X0,sK0)
        | ~ r1_orders_2(sK0,sK2(sK0,X0),X1)
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_orders_2(sK0,sK3(sK0,X0),X1) )
    | ~ spl9_4 ),
    inference(resolution,[],[f62,f99])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,sK3(X0,X1),X4)
      | ~ r1_orders_2(X0,sK2(X0,X1),X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f159,plain,
    ( ~ spl9_11
    | spl9_13
    | spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f155,f98,f87,f157,f138])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2(sK0,k3_waybel_0(sK0,sK1)),X0)
        | ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_orders_2(sK0,sK3(sK0,k3_waybel_0(sK0,sK1)),X0) )
    | spl9_2
    | ~ spl9_4 ),
    inference(resolution,[],[f154,f88])).

fof(f88,plain,
    ( ~ v1_waybel_0(k3_waybel_0(sK0,sK1),sK0)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f147,plain,
    ( ~ spl9_4
    | ~ spl9_3
    | spl9_11 ),
    inference(avatar_split_clause,[],[f145,f138,f94,f98])).

fof(f145,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl9_11 ),
    inference(resolution,[],[f139,f74])).

fof(f139,plain,
    ( ~ m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl9_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f144,plain,
    ( spl9_12
    | ~ spl9_11
    | spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f133,f98,f87,f138,f142])).

fof(f133,plain,
    ( ~ m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1))
    | spl9_2
    | ~ spl9_4 ),
    inference(resolution,[],[f88,f118])).

fof(f118,plain,
    ( ! [X0] :
        ( v1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2(sK0,X0),X0) )
    | ~ spl9_4 ),
    inference(resolution,[],[f60,f99])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f140,plain,
    ( spl9_10
    | ~ spl9_11
    | spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f132,f98,f87,f138,f135])).

fof(f132,plain,
    ( ~ m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3(sK0,k3_waybel_0(sK0,sK1)),k3_waybel_0(sK0,sK1))
    | spl9_2
    | ~ spl9_4 ),
    inference(resolution,[],[f88,f125])).

fof(f125,plain,
    ( ! [X0] :
        ( v1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK3(sK0,X0),X0) )
    | ~ spl9_4 ),
    inference(resolution,[],[f61,f99])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f131,plain,
    ( spl9_9
    | ~ spl9_3
    | spl9_1
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f127,f98,f84,f94,f129])).

fof(f127,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3(sK0,sK1),sK1)
    | spl9_1
    | ~ spl9_4 ),
    inference(resolution,[],[f125,f85])).

fof(f124,plain,
    ( spl9_8
    | ~ spl9_3
    | spl9_1
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f119,f98,f84,f94,f121])).

fof(f119,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2(sK0,sK1),sK1)
    | spl9_1
    | ~ spl9_4 ),
    inference(resolution,[],[f118,f85])).

fof(f112,plain,(
    ~ spl9_7 ),
    inference(avatar_split_clause,[],[f47,f110])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ v1_waybel_0(k3_waybel_0(sK0,sK1),sK0)
      | ~ v1_waybel_0(sK1,sK0) )
    & ( v1_waybel_0(k3_waybel_0(sK0,sK1),sK0)
      | v1_waybel_0(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_waybel_0(k3_waybel_0(X0,X1),X0)
              | ~ v1_waybel_0(X1,X0) )
            & ( v1_waybel_0(k3_waybel_0(X0,X1),X0)
              | v1_waybel_0(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_waybel_0(k3_waybel_0(sK0,X1),sK0)
            | ~ v1_waybel_0(X1,sK0) )
          & ( v1_waybel_0(k3_waybel_0(sK0,X1),sK0)
            | v1_waybel_0(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ( ~ v1_waybel_0(k3_waybel_0(sK0,X1),sK0)
          | ~ v1_waybel_0(X1,sK0) )
        & ( v1_waybel_0(k3_waybel_0(sK0,X1),sK0)
          | v1_waybel_0(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v1_waybel_0(k3_waybel_0(sK0,sK1),sK0)
        | ~ v1_waybel_0(sK1,sK0) )
      & ( v1_waybel_0(k3_waybel_0(sK0,sK1),sK0)
        | v1_waybel_0(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_waybel_0(k3_waybel_0(X0,X1),X0)
            | ~ v1_waybel_0(X1,X0) )
          & ( v1_waybel_0(k3_waybel_0(X0,X1),X0)
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_waybel_0(k3_waybel_0(X0,X1),X0)
            | ~ v1_waybel_0(X1,X0) )
          & ( v1_waybel_0(k3_waybel_0(X0,X1),X0)
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_0(X1,X0)
          <~> v1_waybel_0(k3_waybel_0(X0,X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_0(X1,X0)
          <~> v1_waybel_0(k3_waybel_0(X0,X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v1_waybel_0(X1,X0)
            <=> v1_waybel_0(k3_waybel_0(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_waybel_0(X1,X0)
          <=> v1_waybel_0(k3_waybel_0(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_waybel_0)).

fof(f108,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f48,f106])).

fof(f48,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f104,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f49,f102])).

fof(f49,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f100,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f50,f98])).

fof(f50,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f96,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f51,f94])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f52,f87,f84])).

fof(f52,plain,
    ( v1_waybel_0(k3_waybel_0(sK0,sK1),sK0)
    | v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f89,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f53,f87,f84])).

fof(f53,plain,
    ( ~ v1_waybel_0(k3_waybel_0(sK0,sK1),sK0)
    | ~ v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

%------------------------------------------------------------------------------
