%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 404 expanded)
%              Number of leaves         :   32 ( 156 expanded)
%              Depth                    :   21
%              Number of atoms          :  793 (1753 expanded)
%              Number of equality atoms :   64 ( 201 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f430,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f96,f101,f109,f135,f141,f148,f153,f173,f246,f257,f262,f423,f427])).

fof(f427,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_16
    | spl4_28 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_16
    | spl4_28 ),
    inference(subsumption_resolution,[],[f424,f422])).

fof(f422,plain,
    ( ~ r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f420])).

fof(f420,plain,
    ( spl4_28
  <=> r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f424,plain,
    ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f261,f296])).

% (22597)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f296,plain,
    ( ! [X0] :
        ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0)
        | ~ r2_hidden(X0,k2_struct_0(sK0)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f295,f147])).

fof(f147,plain,
    ( r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl4_10
  <=> r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f295,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
        | r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0)
        | ~ r2_hidden(X0,k2_struct_0(sK0)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f294,f140])).

fof(f140,plain,
    ( k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl4_9
  <=> k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f294,plain,
    ( ! [X0] :
        ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0)
        | ~ r2_hidden(X0,k2_struct_0(sK0))
        | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0))) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f293,f71])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f49,f48])).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f293,plain,
    ( ! [X0] :
        ( r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0)
        | ~ r2_hidden(X0,k2_struct_0(sK0))
        | ~ r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0)))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(superposition,[],[f192,f256])).

fof(f256,plain,
    ( sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl4_15
  <=> sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f192,plain,
    ( ! [X10,X11,X9] :
        ( r2_orders_2(sK0,sK3(X11,sK0,X10),X9)
        | ~ r2_hidden(X9,X10)
        | ~ r2_hidden(X11,a_2_1_orders_2(sK0,X10))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f191,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f191,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_subset_1(X9,k2_struct_0(sK0))
        | ~ r2_hidden(X9,X10)
        | r2_orders_2(sK0,sK3(X11,sK0,X10),X9)
        | ~ r2_hidden(X11,a_2_1_orders_2(sK0,X10))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f190,f75])).

fof(f75,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f190,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_subset_1(X9,k2_struct_0(sK0))
        | ~ r2_hidden(X9,X10)
        | r2_orders_2(sK0,sK3(X11,sK0,X10),X9)
        | ~ r2_hidden(X11,a_2_1_orders_2(sK0,X10))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f189,f80])).

fof(f80,plain,
    ( v3_orders_2(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f189,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_subset_1(X9,k2_struct_0(sK0))
        | ~ r2_hidden(X9,X10)
        | r2_orders_2(sK0,sK3(X11,sK0,X10),X9)
        | ~ r2_hidden(X11,a_2_1_orders_2(sK0,X10))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f188,f85])).

fof(f85,plain,
    ( v4_orders_2(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f188,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_subset_1(X9,k2_struct_0(sK0))
        | ~ r2_hidden(X9,X10)
        | r2_orders_2(sK0,sK3(X11,sK0,X10),X9)
        | ~ r2_hidden(X11,a_2_1_orders_2(sK0,X10))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f187,f90])).

fof(f90,plain,
    ( v5_orders_2(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f187,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_subset_1(X9,k2_struct_0(sK0))
        | ~ r2_hidden(X9,X10)
        | r2_orders_2(sK0,sK3(X11,sK0,X10),X9)
        | ~ r2_hidden(X11,a_2_1_orders_2(sK0,X10))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f180,f95])).

fof(f95,plain,
    ( l1_orders_2(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f180,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_subset_1(X9,k2_struct_0(sK0))
        | ~ r2_hidden(X9,X10)
        | r2_orders_2(sK0,sK3(X11,sK0,X10),X9)
        | ~ r2_hidden(X11,a_2_1_orders_2(sK0,X10))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_12 ),
    inference(superposition,[],[f61,f172])).

fof(f172,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl4_12
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f61,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X6,X2)
      | r2_orders_2(X1,sK3(X0,X1,X2),X6)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK2(X1,X2,X3))
                & r2_hidden(sK2(X1,X2,X3),X2)
                & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK3(X0,X1,X2) = X0
            & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f40,f39])).

fof(f39,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK2(X1,X2,X3))
        & r2_hidden(sK2(X1,X2,X3),X2)
        & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK3(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X5,X6)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X3,X4)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f261,plain,
    ( r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl4_16
  <=> r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f423,plain,
    ( ~ spl4_28
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f247,f243,f170,f93,f420])).

fof(f243,plain,
    ( spl4_14
  <=> m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f247,plain,
    ( ~ r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f245,f208])).

fof(f208,plain,
    ( ! [X18] :
        ( ~ m1_subset_1(X18,k2_struct_0(sK0))
        | ~ r2_orders_2(sK0,X18,X18) )
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f184,f95])).

fof(f184,plain,
    ( ! [X18] :
        ( ~ m1_subset_1(X18,k2_struct_0(sK0))
        | ~ r2_orders_2(sK0,X18,X18)
        | ~ l1_orders_2(sK0) )
    | ~ spl4_12 ),
    inference(superposition,[],[f70,f172])).

% (22598)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f70,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X2,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f245,plain,
    ( m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f243])).

fof(f262,plain,
    ( spl4_16
    | spl4_11
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f248,f243,f150,f259])).

fof(f150,plain,
    ( spl4_11
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f248,plain,
    ( r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | spl4_11
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f152,f245,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f152,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f257,plain,
    ( spl4_15
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f235,f145,f138,f106,f93,f88,f83,f78,f73,f254])).

fof(f106,plain,
    ( spl4_7
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f235,plain,
    ( sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f147,f164])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | sK3(X0,sK0,k2_struct_0(sK0)) = X0 )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f163,f128])).

fof(f128,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f108,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f108,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | sK3(X0,sK0,u1_struct_0(sK0)) = X0 )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f162,f140])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
        | sK3(X0,sK0,u1_struct_0(sK0)) = X0 )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f161,f128])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0)))
        | sK3(X0,sK0,u1_struct_0(sK0)) = X0 )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f121,f71])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | sK3(X0,sK0,X1) = X0 )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f120,f75])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK3(X0,sK0,X1) = X0
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f119,f80])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK3(X0,sK0,X1) = X0
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f118,f85])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK3(X0,sK0,X1) = X0
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f117,f95])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | sK3(X0,sK0,X1) = X0
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f60,f90])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | sK3(X0,X1,X2) = X0
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f246,plain,
    ( spl4_14
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f241,f145,f138,f106,f93,f88,f83,f78,f73,f243])).

fof(f241,plain,
    ( m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f239,f235])).

fof(f239,plain,
    ( m1_subset_1(sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f147,f168])).

fof(f168,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
        | ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f167,f128])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))
        | m1_subset_1(sK3(X0,sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f166,f140])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0)))
        | m1_subset_1(sK3(X0,sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f165,f128])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0)))
        | m1_subset_1(sK3(X0,sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f126,f71])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f125,f75])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f124,f80])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f123,f85])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f122,f95])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f59,f90])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f173,plain,
    ( spl4_12
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f128,f106,f170])).

fof(f153,plain,
    ( ~ spl4_11
    | spl4_1
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f130,f106,f73,f150])).

fof(f130,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl4_1
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f127,f128])).

fof(f127,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f75,f108,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f148,plain,
    ( spl4_10
    | spl4_6 ),
    inference(avatar_split_clause,[],[f104,f98,f145])).

fof(f98,plain,
    ( spl4_6
  <=> k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f104,plain,
    ( r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f100,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2] :
                  ( r2_hidden(X2,X1)
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_mcart_1)).

fof(f100,plain,
    ( k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f141,plain,
    ( spl4_9
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f136,f132,f106,f138])).

fof(f132,plain,
    ( spl4_8
  <=> k2_orders_2(sK0,u1_struct_0(sK0)) = a_2_1_orders_2(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f136,plain,
    ( k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0))
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f134,f128])).

fof(f134,plain,
    ( k2_orders_2(sK0,u1_struct_0(sK0)) = a_2_1_orders_2(sK0,u1_struct_0(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f132])).

fof(f135,plain,
    ( spl4_8
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f111,f93,f88,f83,f78,f73,f132])).

fof(f111,plain,
    ( k2_orders_2(sK0,u1_struct_0(sK0)) = a_2_1_orders_2(sK0,u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f75,f80,f85,f90,f95,f71,f55])).

% (22607)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

fof(f109,plain,
    ( spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f102,f93,f106])).

fof(f102,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f95,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f101,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f47,f98])).

fof(f47,plain,(
    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

fof(f96,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f46,f93])).

fof(f46,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f45,f88])).

fof(f45,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f44,f83])).

fof(f44,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f81,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f43,f78])).

fof(f43,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f42,f73])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:40:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (22617)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.49  % (22609)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.50  % (22600)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (22599)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (22613)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (22615)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (22617)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f430,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f96,f101,f109,f135,f141,f148,f153,f173,f246,f257,f262,f423,f427])).
% 0.22/0.51  fof(f427,plain,(
% 0.22/0.51    spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_16 | spl4_28),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f426])).
% 0.22/0.51  fof(f426,plain,(
% 0.22/0.51    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_16 | spl4_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f424,f422])).
% 0.22/0.51  fof(f422,plain,(
% 0.22/0.51    ~r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | spl4_28),
% 0.22/0.51    inference(avatar_component_clause,[],[f420])).
% 0.22/0.51  fof(f420,plain,(
% 0.22/0.51    spl4_28 <=> r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.51  fof(f424,plain,(
% 0.22/0.51    r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_16)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f261,f296])).
% 0.22/0.51  % (22597)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  fof(f296,plain,(
% 0.22/0.51    ( ! [X0] : (r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0) | ~r2_hidden(X0,k2_struct_0(sK0))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f295,f147])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | ~spl4_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f145])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    spl4_10 <=> r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.51  fof(f295,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0) | ~r2_hidden(X0,k2_struct_0(sK0))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_12 | ~spl4_15)),
% 0.22/0.51    inference(forward_demodulation,[],[f294,f140])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0)) | ~spl4_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f138])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    spl4_9 <=> k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.51  fof(f294,plain,(
% 0.22/0.51    ( ! [X0] : (r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0) | ~r2_hidden(X0,k2_struct_0(sK0)) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0)))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_12 | ~spl4_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f293,f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f49,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.51  fof(f293,plain,(
% 0.22/0.51    ( ! [X0] : (r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),X0) | ~r2_hidden(X0,k2_struct_0(sK0)) | ~r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),a_2_1_orders_2(sK0,k2_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_12 | ~spl4_15)),
% 0.22/0.51    inference(superposition,[],[f192,f256])).
% 0.22/0.51  fof(f256,plain,(
% 0.22/0.51    sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) | ~spl4_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f254])).
% 0.22/0.51  fof(f254,plain,(
% 0.22/0.51    spl4_15 <=> sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.51  fof(f192,plain,(
% 0.22/0.51    ( ! [X10,X11,X9] : (r2_orders_2(sK0,sK3(X11,sK0,X10),X9) | ~r2_hidden(X9,X10) | ~r2_hidden(X11,a_2_1_orders_2(sK0,X10)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f191,f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    ( ! [X10,X11,X9] : (~m1_subset_1(X9,k2_struct_0(sK0)) | ~r2_hidden(X9,X10) | r2_orders_2(sK0,sK3(X11,sK0,X10),X9) | ~r2_hidden(X11,a_2_1_orders_2(sK0,X10)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f190,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ~v2_struct_0(sK0) | spl4_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f73])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    spl4_1 <=> v2_struct_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.51  fof(f190,plain,(
% 0.22/0.51    ( ! [X10,X11,X9] : (~m1_subset_1(X9,k2_struct_0(sK0)) | ~r2_hidden(X9,X10) | r2_orders_2(sK0,sK3(X11,sK0,X10),X9) | ~r2_hidden(X11,a_2_1_orders_2(sK0,X10)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f189,f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    v3_orders_2(sK0) | ~spl4_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    spl4_2 <=> v3_orders_2(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    ( ! [X10,X11,X9] : (~m1_subset_1(X9,k2_struct_0(sK0)) | ~r2_hidden(X9,X10) | r2_orders_2(sK0,sK3(X11,sK0,X10),X9) | ~r2_hidden(X11,a_2_1_orders_2(sK0,X10)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f188,f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    v4_orders_2(sK0) | ~spl4_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f83])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    spl4_3 <=> v4_orders_2(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    ( ! [X10,X11,X9] : (~m1_subset_1(X9,k2_struct_0(sK0)) | ~r2_hidden(X9,X10) | r2_orders_2(sK0,sK3(X11,sK0,X10),X9) | ~r2_hidden(X11,a_2_1_orders_2(sK0,X10)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | ~spl4_5 | ~spl4_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f187,f90])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    v5_orders_2(sK0) | ~spl4_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f88])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    spl4_4 <=> v5_orders_2(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    ( ! [X10,X11,X9] : (~m1_subset_1(X9,k2_struct_0(sK0)) | ~r2_hidden(X9,X10) | r2_orders_2(sK0,sK3(X11,sK0,X10),X9) | ~r2_hidden(X11,a_2_1_orders_2(sK0,X10)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | ~spl4_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f180,f95])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    l1_orders_2(sK0) | ~spl4_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f93])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    spl4_5 <=> l1_orders_2(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    ( ! [X10,X11,X9] : (~m1_subset_1(X9,k2_struct_0(sK0)) | ~r2_hidden(X9,X10) | r2_orders_2(sK0,sK3(X11,sK0,X10),X9) | ~r2_hidden(X11,a_2_1_orders_2(sK0,X10)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_12),
% 0.22/0.51    inference(superposition,[],[f61,f172])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl4_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f170])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    spl4_12 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X6,X2,X0,X1] : (~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X6,X2) | r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f40,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK2(X1,X2,X3)) & r2_hidden(sK2(X1,X2,X3),X2) & m1_subset_1(sK2(X1,X2,X3),u1_struct_0(X1))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK3(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK3(X0,X1,X2) = X0 & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.51    inference(rectify,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.22/0.51  fof(f261,plain,(
% 0.22/0.51    r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~spl4_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f259])).
% 0.22/0.51  fof(f259,plain,(
% 0.22/0.51    spl4_16 <=> r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.51  fof(f423,plain,(
% 0.22/0.51    ~spl4_28 | ~spl4_5 | ~spl4_12 | ~spl4_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f247,f243,f170,f93,f420])).
% 0.22/0.52  fof(f243,plain,(
% 0.22/0.52    spl4_14 <=> m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.52  fof(f247,plain,(
% 0.22/0.52    ~r2_orders_2(sK0,sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK1(k2_orders_2(sK0,k2_struct_0(sK0)))) | (~spl4_5 | ~spl4_12 | ~spl4_14)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f245,f208])).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    ( ! [X18] : (~m1_subset_1(X18,k2_struct_0(sK0)) | ~r2_orders_2(sK0,X18,X18)) ) | (~spl4_5 | ~spl4_12)),
% 0.22/0.52    inference(subsumption_resolution,[],[f184,f95])).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    ( ! [X18] : (~m1_subset_1(X18,k2_struct_0(sK0)) | ~r2_orders_2(sK0,X18,X18) | ~l1_orders_2(sK0)) ) | ~spl4_12),
% 0.22/0.52    inference(superposition,[],[f70,f172])).
% 0.22/0.52  % (22598)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X2,X0] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2) | ~l1_orders_2(X0)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(flattening,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 0.22/0.52  fof(f245,plain,(
% 0.22/0.52    m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | ~spl4_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f243])).
% 0.22/0.52  fof(f262,plain,(
% 0.22/0.52    spl4_16 | spl4_11 | ~spl4_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f248,f243,f150,f259])).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    spl4_11 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.52  fof(f248,plain,(
% 0.22/0.52    r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | (spl4_11 | ~spl4_14)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f152,f245,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    ~v1_xboole_0(k2_struct_0(sK0)) | spl4_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f150])).
% 0.22/0.52  fof(f257,plain,(
% 0.22/0.52    spl4_15 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_9 | ~spl4_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f235,f145,f138,f106,f93,f88,f83,f78,f73,f254])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    spl4_7 <=> l1_struct_0(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.52  fof(f235,plain,(
% 0.22/0.52    sK1(k2_orders_2(sK0,k2_struct_0(sK0))) = sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_9 | ~spl4_10)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f147,f164])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X0,sK0,k2_struct_0(sK0)) = X0) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_9)),
% 0.22/0.52    inference(forward_demodulation,[],[f163,f128])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl4_7),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f108,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    l1_struct_0(sK0) | ~spl4_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f106])).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | sK3(X0,sK0,u1_struct_0(sK0)) = X0) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_9)),
% 0.22/0.52    inference(forward_demodulation,[],[f162,f140])).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | sK3(X0,sK0,u1_struct_0(sK0)) = X0) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.22/0.52    inference(forward_demodulation,[],[f161,f128])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0))) | sK3(X0,sK0,u1_struct_0(sK0)) = X0) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.52    inference(resolution,[],[f121,f71])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | sK3(X0,sK0,X1) = X0) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f120,f75])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X0,sK0,X1) = X0 | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f119,f80])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X0,sK0,X1) = X0 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f118,f85])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X0,sK0,X1) = X0 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | ~spl4_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f117,f95])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | sK3(X0,sK0,X1) = X0 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_4),
% 0.22/0.52    inference(resolution,[],[f60,f90])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | sK3(X0,X1,X2) = X0 | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f246,plain,(
% 0.22/0.52    spl4_14 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_9 | ~spl4_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f241,f145,f138,f106,f93,f88,f83,f78,f73,f243])).
% 0.22/0.52  fof(f241,plain,(
% 0.22/0.52    m1_subset_1(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_9 | ~spl4_10)),
% 0.22/0.52    inference(forward_demodulation,[],[f239,f235])).
% 0.22/0.52  fof(f239,plain,(
% 0.22/0.52    m1_subset_1(sK3(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_9 | ~spl4_10)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f147,f168])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(sK3(X0,sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | ~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0)))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_9)),
% 0.22/0.52    inference(forward_demodulation,[],[f167,f128])).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_struct_0(sK0))) | m1_subset_1(sK3(X0,sK0,u1_struct_0(sK0)),u1_struct_0(sK0))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_9)),
% 0.22/0.52    inference(forward_demodulation,[],[f166,f140])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,a_2_1_orders_2(sK0,k2_struct_0(sK0))) | m1_subset_1(sK3(X0,sK0,u1_struct_0(sK0)),u1_struct_0(sK0))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.22/0.52    inference(forward_demodulation,[],[f165,f128])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,a_2_1_orders_2(sK0,u1_struct_0(sK0))) | m1_subset_1(sK3(X0,sK0,u1_struct_0(sK0)),u1_struct_0(sK0))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.52    inference(resolution,[],[f126,f71])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f125,f75])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f124,f80])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f123,f85])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl4_4 | ~spl4_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f122,f95])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | m1_subset_1(sK3(X0,sK0,X1),u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_4),
% 0.22/0.52    inference(resolution,[],[f59,f90])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f173,plain,(
% 0.22/0.52    spl4_12 | ~spl4_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f128,f106,f170])).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    ~spl4_11 | spl4_1 | ~spl4_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f130,f106,f73,f150])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    ~v1_xboole_0(k2_struct_0(sK0)) | (spl4_1 | ~spl4_7)),
% 0.22/0.52    inference(forward_demodulation,[],[f127,f128])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    ~v1_xboole_0(u1_struct_0(sK0)) | (spl4_1 | ~spl4_7)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f75,f108,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    spl4_10 | spl4_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f104,f98,f145])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    spl4_6 <=> k1_xboole_0 = k2_orders_2(sK0,k2_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    r2_hidden(sK1(k2_orders_2(sK0,k2_struct_0(sK0))),k2_orders_2(sK0,k2_struct_0(sK0))) | spl4_6),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f100,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.52    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : ~(! [X1] : ~(! [X2] : (r2_hidden(X2,X1) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_mcart_1)).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) | spl4_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f98])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    spl4_9 | ~spl4_7 | ~spl4_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f136,f132,f106,f138])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    spl4_8 <=> k2_orders_2(sK0,u1_struct_0(sK0)) = a_2_1_orders_2(sK0,u1_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    k2_orders_2(sK0,k2_struct_0(sK0)) = a_2_1_orders_2(sK0,k2_struct_0(sK0)) | (~spl4_7 | ~spl4_8)),
% 0.22/0.52    inference(forward_demodulation,[],[f134,f128])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    k2_orders_2(sK0,u1_struct_0(sK0)) = a_2_1_orders_2(sK0,u1_struct_0(sK0)) | ~spl4_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f132])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    spl4_8 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f111,f93,f88,f83,f78,f73,f132])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    k2_orders_2(sK0,u1_struct_0(sK0)) = a_2_1_orders_2(sK0,u1_struct_0(sK0)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f75,f80,f85,f90,f95,f71,f55])).
% 0.22/0.52  % (22607)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    spl4_7 | ~spl4_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f102,f93,f106])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    l1_struct_0(sK0) | ~spl4_5),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f95,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    ~spl4_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f47,f98])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.22/0.52    inference(negated_conjecture,[],[f12])).
% 0.22/0.52  fof(f12,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    spl4_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f46,f93])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    l1_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    spl4_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f45,f88])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    v5_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    spl4_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f44,f83])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    v4_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f43,f78])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    v3_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ~spl4_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f42,f73])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ~v2_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (22617)------------------------------
% 0.22/0.52  % (22617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22617)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (22617)Memory used [KB]: 10874
% 0.22/0.52  % (22617)Time elapsed: 0.050 s
% 0.22/0.52  % (22617)------------------------------
% 0.22/0.52  % (22617)------------------------------
% 1.24/0.52  % (22593)Success in time 0.157 s
%------------------------------------------------------------------------------
