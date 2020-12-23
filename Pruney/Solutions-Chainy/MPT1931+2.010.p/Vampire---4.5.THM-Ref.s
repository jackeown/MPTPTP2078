%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 226 expanded)
%              Number of leaves         :   13 (  63 expanded)
%              Depth                    :   21
%              Number of atoms          :  318 (1257 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f74,f80])).

fof(f80,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f78,f30])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK0,X1,u1_struct_0(sK0))
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ~ r1_waybel_0(sK0,X1,u1_struct_0(sK0))
        & l1_waybel_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
      & l1_waybel_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

fof(f78,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f77,f31])).

fof(f31,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f53,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f53,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl5_1
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f74,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | ~ spl5_2 ),
    inference(resolution,[],[f69,f41])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f1,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f69,plain,
    ( ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f68,f30])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f67,f31])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f66,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f65,f33])).

fof(f33,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f64,f34])).

fof(f34,plain,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f62,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK2(X0,X1,X2,X3))
                      & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK3(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f26,f25])).

fof(f25,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK2(X0,X1,X2,X3))
        & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK3(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

fof(f62,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,sK1,u1_struct_0(sK0),X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f61,f30])).

fof(f61,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2(sK0,sK1,u1_struct_0(sK0),X0),u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f60,f31])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2(sK0,sK1,u1_struct_0(sK0),X0),u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f59,f32])).

fof(f59,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2(sK0,sK1,u1_struct_0(sK0),X0),u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f58,f33])).

% (22006)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
fof(f58,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2(sK0,sK1,u1_struct_0(sK0),X0),u1_struct_0(sK1))
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f56,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_waybel_0)).

fof(f56,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK2(sK0,sK1,u1_struct_0(sK0),X0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl5_2
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK2(sK0,sK1,u1_struct_0(sK0),X0)),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f57,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f49,f55,f51])).

fof(f49,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK2(sK0,sK1,u1_struct_0(sK0),X0)),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f48,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f48,plain,(
    ! [X0] :
      ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK2(sK0,sK1,u1_struct_0(sK0),X0)),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f47,f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(sK0,sK1,X1)
      | ~ r2_hidden(k2_waybel_0(sK0,sK1,sK2(sK0,sK1,X1,X0)),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f46,f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_hidden(k2_waybel_0(sK0,sK1,sK2(sK0,sK1,X1,X0)),X1)
      | v2_struct_0(sK1)
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(resolution,[],[f45,f33])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(k2_waybel_0(sK0,X0,sK2(sK0,X0,X1,X2)),X1)
      | v2_struct_0(X0)
      | r1_waybel_0(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f44,f30])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_waybel_0(sK0,X0,sK2(sK0,X0,X1,X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X0,sK0)
      | v2_struct_0(X0)
      | r1_waybel_0(sK0,X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f40,f31])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r1_waybel_0(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:57:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (21993)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.20/0.45  % (21993)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f81,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f57,f74,f80])).
% 0.20/0.45  fof(f80,plain,(
% 0.20/0.45    ~spl5_1),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f79])).
% 0.20/0.45  fof(f79,plain,(
% 0.20/0.45    $false | ~spl5_1),
% 0.20/0.45    inference(subsumption_resolution,[],[f78,f30])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ~v2_struct_0(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f21,f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f7])).
% 0.20/0.45  fof(f7,negated_conjecture,(
% 0.20/0.45    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.20/0.45    inference(negated_conjecture,[],[f6])).
% 0.20/0.45  fof(f6,conjecture,(
% 0.20/0.45    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).
% 0.20/0.45  fof(f78,plain,(
% 0.20/0.45    v2_struct_0(sK0) | ~spl5_1),
% 0.20/0.45    inference(subsumption_resolution,[],[f77,f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    l1_struct_0(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.45  fof(f77,plain,(
% 0.20/0.45    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_1),
% 0.20/0.45    inference(resolution,[],[f53,f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f51])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    spl5_1 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.45  fof(f74,plain,(
% 0.20/0.45    ~spl5_2),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f73])).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    $false | ~spl5_2),
% 0.20/0.45    inference(resolution,[],[f69,f41])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ! [X0] : m1_subset_1(sK4(X0),X0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f1,f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK4(X0),X0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1))) ) | ~spl5_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f68,f30])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK0)) ) | ~spl5_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f67,f31])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) ) | ~spl5_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f66,f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ~v2_struct_0(sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) ) | ~spl5_2),
% 0.20/0.46    inference(subsumption_resolution,[],[f65,f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    l1_waybel_0(sK1,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) ) | ~spl5_2),
% 0.20/0.46    inference(subsumption_resolution,[],[f64,f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) ) | ~spl5_2),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f63])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) ) | ~spl5_2),
% 0.20/0.46    inference(resolution,[],[f62,f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1)) | r1_waybel_0(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : ((~r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK2(X0,X1,X2,X3)) & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK3(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f26,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ! [X3,X2,X1,X0] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK2(X0,X1,X2,X3)) & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK3(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(rectify,[],[f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : ((r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r1_orders_2(X1,X3,X4) => r2_hidden(k2_waybel_0(X0,X1,X4),X2))) & m1_subset_1(X3,u1_struct_0(X1))))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(sK2(sK0,sK1,u1_struct_0(sK0),X0),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | ~spl5_2),
% 0.20/0.46    inference(subsumption_resolution,[],[f61,f30])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(sK2(sK0,sK1,u1_struct_0(sK0),X0),u1_struct_0(sK1)) | v2_struct_0(sK0)) ) | ~spl5_2),
% 0.20/0.46    inference(subsumption_resolution,[],[f60,f31])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(sK2(sK0,sK1,u1_struct_0(sK0),X0),u1_struct_0(sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) ) | ~spl5_2),
% 0.20/0.46    inference(subsumption_resolution,[],[f59,f32])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(sK2(sK0,sK1,u1_struct_0(sK0),X0),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) ) | ~spl5_2),
% 0.20/0.46    inference(subsumption_resolution,[],[f58,f33])).
% 0.20/0.46  % (22006)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(sK2(sK0,sK1,u1_struct_0(sK0),X0),u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) ) | ~spl5_2),
% 0.20/0.46    inference(resolution,[],[f56,f43])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_waybel_0)).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(k2_waybel_0(sK0,sK1,sK2(sK0,sK1,u1_struct_0(sK0),X0)),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | ~spl5_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f55])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    spl5_2 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(k2_waybel_0(sK0,sK1,sK2(sK0,sK1,u1_struct_0(sK0),X0)),u1_struct_0(sK0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    spl5_1 | spl5_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f49,f55,f51])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(k2_waybel_0(sK0,sK1,sK2(sK0,sK1,u1_struct_0(sK0),X0)),u1_struct_0(sK0))) )),
% 0.20/0.46    inference(resolution,[],[f48,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.46    inference(flattening,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(k2_waybel_0(sK0,sK1,sK2(sK0,sK1,u1_struct_0(sK0),X0)),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.20/0.46    inference(resolution,[],[f47,f34])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_waybel_0(sK0,sK1,X1) | ~r2_hidden(k2_waybel_0(sK0,sK1,sK2(sK0,sK1,X1,X0)),X1) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f46,f32])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(k2_waybel_0(sK0,sK1,sK2(sK0,sK1,X1,X0)),X1) | v2_struct_0(sK1) | r1_waybel_0(sK0,sK1,X1)) )),
% 0.20/0.46    inference(resolution,[],[f45,f33])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~l1_waybel_0(X0,sK0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(k2_waybel_0(sK0,X0,sK2(sK0,X0,X1,X2)),X1) | v2_struct_0(X0) | r1_waybel_0(sK0,X0,X1)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f44,f30])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r2_hidden(k2_waybel_0(sK0,X0,sK2(sK0,X0,X1,X2)),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X0,sK0) | v2_struct_0(X0) | r1_waybel_0(sK0,X0,X1) | v2_struct_0(sK0)) )),
% 0.20/0.46    inference(resolution,[],[f40,f31])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~l1_struct_0(X0) | ~r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r1_waybel_0(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f27])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (21993)------------------------------
% 0.20/0.46  % (21993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (21993)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (21993)Memory used [KB]: 5373
% 0.20/0.46  % (21993)Time elapsed: 0.049 s
% 0.20/0.46  % (21993)------------------------------
% 0.20/0.46  % (21993)------------------------------
% 0.20/0.46  % (21992)Success in time 0.105 s
%------------------------------------------------------------------------------
