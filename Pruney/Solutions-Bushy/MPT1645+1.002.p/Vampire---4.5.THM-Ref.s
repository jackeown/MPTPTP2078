%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1645+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:14 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 389 expanded)
%              Number of leaves         :   16 ( 177 expanded)
%              Depth                    :   15
%              Number of atoms          :  339 (3746 expanded)
%              Number of equality atoms :   62 ( 720 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f102,f106,f107,f129,f173,f194,f199,f201,f203])).

fof(f203,plain,(
    spl10_18 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl10_18 ),
    inference(subsumption_resolution,[],[f88,f192])).

fof(f192,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl10_18 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl10_18
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f88,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f61,f63])).

fof(f63,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ( ~ v13_waybel_0(sK3,sK1)
        & v13_waybel_0(sK2,sK0) )
      | ( ~ v12_waybel_0(sK3,sK1)
        & v12_waybel_0(sK2,sK0) ) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f42,f41,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ v13_waybel_0(X3,X1)
                        & v13_waybel_0(X2,X0) )
                      | ( ~ v12_waybel_0(X3,X1)
                        & v12_waybel_0(X2,X0) ) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v13_waybel_0(X3,X1)
                      & v13_waybel_0(X2,sK0) )
                    | ( ~ v12_waybel_0(X3,X1)
                      & v12_waybel_0(X2,sK0) ) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ v13_waybel_0(X3,X1)
                    & v13_waybel_0(X2,sK0) )
                  | ( ~ v12_waybel_0(X3,X1)
                    & v12_waybel_0(X2,sK0) ) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        & l1_orders_2(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ v13_waybel_0(X3,sK1)
                  & v13_waybel_0(X2,sK0) )
                | ( ~ v12_waybel_0(X3,sK1)
                  & v12_waybel_0(X2,sK0) ) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ~ v13_waybel_0(X3,sK1)
                & v13_waybel_0(X2,sK0) )
              | ( ~ v12_waybel_0(X3,sK1)
                & v12_waybel_0(X2,sK0) ) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ( ~ v13_waybel_0(X3,sK1)
              & v13_waybel_0(sK2,sK0) )
            | ( ~ v12_waybel_0(X3,sK1)
              & v12_waybel_0(sK2,sK0) ) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X3] :
        ( ( ( ~ v13_waybel_0(X3,sK1)
            & v13_waybel_0(sK2,sK0) )
          | ( ~ v12_waybel_0(X3,sK1)
            & v12_waybel_0(sK2,sK0) ) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ( ~ v13_waybel_0(sK3,sK1)
          & v13_waybel_0(sK2,sK0) )
        | ( ~ v12_waybel_0(sK3,sK1)
          & v12_waybel_0(sK2,sK0) ) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v13_waybel_0(X3,X1)
                      & v13_waybel_0(X2,X0) )
                    | ( ~ v12_waybel_0(X3,X1)
                      & v12_waybel_0(X2,X0) ) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

% (5027)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v13_waybel_0(X3,X1)
                      & v13_waybel_0(X2,X0) )
                    | ( ~ v12_waybel_0(X3,X1)
                      & v12_waybel_0(X2,X0) ) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => ( ( v13_waybel_0(X2,X0)
                           => v13_waybel_0(X3,X1) )
                          & ( v12_waybel_0(X2,X0)
                           => v12_waybel_0(X3,X1) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( ( v13_waybel_0(X2,X0)
                         => v13_waybel_0(X3,X1) )
                        & ( v12_waybel_0(X2,X0)
                         => v12_waybel_0(X3,X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_waybel_0)).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f201,plain,(
    spl10_17 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | spl10_17 ),
    inference(subsumption_resolution,[],[f58,f189])).

fof(f189,plain,
    ( ~ l1_orders_2(sK0)
    | spl10_17 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl10_17
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f58,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f199,plain,
    ( spl10_2
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f196,f126,f96])).

fof(f96,plain,
    ( spl10_2
  <=> v13_waybel_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f126,plain,
    ( spl10_8
  <=> r1_tarski(k4_waybel_0(sK0,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f196,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK3),sK3)
    | v13_waybel_0(sK3,sK1) ),
    inference(global_subsumption,[],[f59,f62,f195])).

fof(f195,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK3),sK3)
    | v13_waybel_0(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1) ),
    inference(superposition,[],[f74,f177])).

fof(f177,plain,(
    k4_waybel_0(sK1,sK3) = k4_waybel_0(sK0,sK3) ),
    inference(global_subsumption,[],[f88,f174])).

% (5021)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f174,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_waybel_0(sK1,sK3) = k4_waybel_0(sK0,sK3) ),
    inference(resolution,[],[f165,f62])).

fof(f165,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_waybel_0(sK1,X0) = k4_waybel_0(sK0,X0) ) ),
    inference(global_subsumption,[],[f58,f164])).

fof(f164,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_waybel_0(sK1,X0) = k4_waybel_0(sK0,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(equality_resolution,[],[f140])).

fof(f140,plain,(
    ! [X4,X5] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | k4_waybel_0(sK1,X5) = k4_waybel_0(X4,X5)
      | ~ l1_orders_2(X4) ) ),
    inference(global_subsumption,[],[f59,f136])).

fof(f136,plain,(
    ! [X4,X5] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | k4_waybel_0(sK1,X5) = k4_waybel_0(X4,X5)
      | ~ l1_orders_2(sK1)
      | ~ l1_orders_2(X4) ) ),
    inference(superposition,[],[f90,f60])).

fof(f60,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | k4_waybel_0(X1,X3) = k4_waybel_0(X0,X3)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
                    & k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
                    & k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
                        & k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_0)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_waybel_0(X0,X1),X1)
      | v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ~ r1_tarski(k4_waybel_0(X0,X1),X1) )
            & ( r1_tarski(k4_waybel_0(X0,X1),X1)
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> r1_tarski(k4_waybel_0(X0,X1),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> r1_tarski(k4_waybel_0(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_waybel_0)).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f59,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f194,plain,
    ( ~ spl10_17
    | ~ spl10_18
    | ~ spl10_3
    | spl10_14 ),
    inference(avatar_split_clause,[],[f186,f171,f100,f191,f188])).

fof(f100,plain,
    ( spl10_3
  <=> v12_waybel_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f171,plain,
    ( spl10_14
  <=> r1_tarski(k3_waybel_0(sK0,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f186,plain,
    ( ~ v12_waybel_0(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl10_14 ),
    inference(resolution,[],[f172,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_waybel_0(X0,X1),X1)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ~ r1_tarski(k3_waybel_0(X0,X1),X1) )
            & ( r1_tarski(k3_waybel_0(X0,X1),X1)
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> r1_tarski(k3_waybel_0(X0,X1),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> r1_tarski(k3_waybel_0(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_0)).

fof(f172,plain,
    ( ~ r1_tarski(k3_waybel_0(sK0,sK3),sK3)
    | spl10_14 ),
    inference(avatar_component_clause,[],[f171])).

fof(f173,plain,
    ( spl10_1
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f168,f171,f93])).

fof(f93,plain,
    ( spl10_1
  <=> v12_waybel_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

% (5011)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f168,plain,
    ( ~ r1_tarski(k3_waybel_0(sK0,sK3),sK3)
    | v12_waybel_0(sK3,sK1) ),
    inference(global_subsumption,[],[f59,f62,f167])).

fof(f167,plain,
    ( ~ r1_tarski(k3_waybel_0(sK0,sK3),sK3)
    | v12_waybel_0(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1) ),
    inference(superposition,[],[f76,f148])).

fof(f148,plain,(
    k3_waybel_0(sK1,sK3) = k3_waybel_0(sK0,sK3) ),
    inference(global_subsumption,[],[f88,f145])).

fof(f145,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_waybel_0(sK1,sK3) = k3_waybel_0(sK0,sK3) ),
    inference(resolution,[],[f144,f62])).

fof(f144,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_waybel_0(sK1,X0) = k3_waybel_0(sK0,X0) ) ),
    inference(global_subsumption,[],[f58,f143])).

fof(f143,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_waybel_0(sK1,X0) = k3_waybel_0(sK0,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(equality_resolution,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k3_waybel_0(X0,X1) = k3_waybel_0(sK1,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(global_subsumption,[],[f59,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k3_waybel_0(X0,X1) = k3_waybel_0(sK1,X1)
      | ~ l1_orders_2(sK1)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f91,f60])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | k3_waybel_0(X1,X3) = k3_waybel_0(X0,X3)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_waybel_0(X0,X1),X1)
      | v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f129,plain,
    ( spl10_8
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f124,f104,f126])).

fof(f104,plain,
    ( spl10_4
  <=> v13_waybel_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f124,plain,
    ( ~ v13_waybel_0(sK3,sK0)
    | r1_tarski(k4_waybel_0(sK0,sK3),sK3) ),
    inference(global_subsumption,[],[f58,f122])).

fof(f122,plain,
    ( ~ v13_waybel_0(sK3,sK0)
    | r1_tarski(k4_waybel_0(sK0,sK3),sK3)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f88,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | r1_tarski(k4_waybel_0(X0,X1),X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f107,plain,
    ( spl10_3
    | spl10_4 ),
    inference(avatar_split_clause,[],[f87,f104,f100])).

fof(f87,plain,
    ( v13_waybel_0(sK3,sK0)
    | v12_waybel_0(sK3,sK0) ),
    inference(definition_unfolding,[],[f64,f63,f63])).

fof(f64,plain,
    ( v13_waybel_0(sK2,sK0)
    | v12_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f106,plain,
    ( ~ spl10_1
    | spl10_4 ),
    inference(avatar_split_clause,[],[f86,f104,f93])).

fof(f86,plain,
    ( v13_waybel_0(sK3,sK0)
    | ~ v12_waybel_0(sK3,sK1) ),
    inference(definition_unfolding,[],[f65,f63])).

fof(f65,plain,
    ( v13_waybel_0(sK2,sK0)
    | ~ v12_waybel_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f102,plain,
    ( spl10_3
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f85,f96,f100])).

fof(f85,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | v12_waybel_0(sK3,sK0) ),
    inference(definition_unfolding,[],[f66,f63])).

fof(f66,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | v12_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f98,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f67,f96,f93])).

fof(f67,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | ~ v12_waybel_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f43])).

%------------------------------------------------------------------------------
