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
% DateTime   : Thu Dec  3 13:16:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 578 expanded)
%              Number of leaves         :   16 ( 180 expanded)
%              Depth                    :   43
%              Number of atoms          :  534 (3033 expanded)
%              Number of equality atoms :   33 ( 201 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(subsumption_resolution,[],[f146,f42])).

fof(f42,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ r1_tarski(sK1,sK2)
      | ~ r3_orders_2(k2_yellow_1(sK0),sK1,sK2) )
    & ( r1_tarski(sK1,sK2)
      | r3_orders_2(k2_yellow_1(sK0),sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) )
                & ( r1_tarski(X1,X2)
                  | r3_orders_2(k2_yellow_1(X0),X1,X2) )
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(X1,X2)
                | ~ r3_orders_2(k2_yellow_1(sK0),X1,X2) )
              & ( r1_tarski(X1,X2)
                | r3_orders_2(k2_yellow_1(sK0),X1,X2) )
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r3_orders_2(k2_yellow_1(sK0),X1,X2) )
            & ( r1_tarski(X1,X2)
              | r3_orders_2(k2_yellow_1(sK0),X1,X2) )
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
        & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,X2)
            | ~ r3_orders_2(k2_yellow_1(sK0),sK1,X2) )
          & ( r1_tarski(sK1,X2)
            | r3_orders_2(k2_yellow_1(sK0),sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,X2)
          | ~ r3_orders_2(k2_yellow_1(sK0),sK1,X2) )
        & ( r1_tarski(sK1,X2)
          | r3_orders_2(k2_yellow_1(sK0),sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ( ~ r1_tarski(sK1,sK2)
        | ~ r3_orders_2(k2_yellow_1(sK0),sK1,sK2) )
      & ( r1_tarski(sK1,sK2)
        | r3_orders_2(k2_yellow_1(sK0),sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(X1,X2)
                | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) )
              & ( r1_tarski(X1,X2)
                | r3_orders_2(k2_yellow_1(X0),X1,X2) )
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(X1,X2)
                | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) )
              & ( r1_tarski(X1,X2)
                | r3_orders_2(k2_yellow_1(X0),X1,X2) )
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <~> r1_tarski(X1,X2) )
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                <=> r1_tarski(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f146,plain,(
    v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f145,f60])).

fof(f60,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0))
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f145,plain,(
    v1_xboole_0(u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f144,f88])).

% (25264)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f88,plain,(
    ! [X0] : l1_struct_0(k2_yellow_1(X0)) ),
    inference(resolution,[],[f65,f62])).

fof(f62,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f144,plain,
    ( ~ l1_struct_0(k2_yellow_1(sK0))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0))) ),
    inference(resolution,[],[f143,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f143,plain,(
    v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f142,f83])).

fof(f83,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f43,f60])).

fof(f43,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f142,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f141,f42])).

fof(f141,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK1,sK0) ),
    inference(resolution,[],[f140,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f140,plain,
    ( ~ r2_hidden(sK1,sK0)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(global_subsumption,[],[f46,f133,f139])).

fof(f139,plain,
    ( r1_tarski(sK1,sK2)
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f138,f84])).

fof(f84,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f44,f60])).

fof(f44,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f138,plain,
    ( r1_tarski(sK1,sK2)
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ r2_hidden(sK1,sK0)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f137,f42])).

fof(f137,plain,
    ( r1_tarski(sK1,sK2)
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(resolution,[],[f122,f56])).

% (25265)Termination reason: Refutation not found, incomplete strategy
fof(f122,plain,
    ( ~ r2_hidden(sK2,sK0)
    | r1_tarski(sK1,sK2)
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f121,f86])).

% (25265)Memory used [KB]: 10618
fof(f86,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),u1_orders_2(k2_yellow_1(X0)))
      | r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0) ) ),
    inference(subsumption_resolution,[],[f81,f75])).

% (25265)Time elapsed: 0.101 s
% (25265)------------------------------
% (25265)------------------------------
% (25264)Refutation not found, incomplete strategy% (25264)------------------------------
% (25264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f75,plain,(
    ! [X0] : v1_relat_1(u1_orders_2(k2_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f64,f67])).

fof(f67,plain,(
    ! [X0] : k1_wellord2(X0) = u1_orders_2(k2_yellow_1(X0)) ),
    inference(definition_unfolding,[],[f63,f61])).

fof(f61,plain,(
    ! [X0] : k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X0] : k1_wellord2(X0) = k1_yellow_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_wellord2(X0) = k1_yellow_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_yellow_1)).

fof(f64,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f81,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),u1_orders_2(k2_yellow_1(X0)))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(u1_orders_2(k2_yellow_1(X0))) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | u1_orders_2(k2_yellow_1(X0)) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f48,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & r2_hidden(sK4(X0,X1),X0)
            & r2_hidden(sK3(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f121,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f120,f83])).

fof(f120,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f119,f42])).

fof(f119,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
    | v1_xboole_0(sK0)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,sK0) ),
    inference(resolution,[],[f117,f84])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,X0)
      | v2_struct_0(k2_yellow_1(sK0))
      | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
      | v1_xboole_0(X0)
      | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(X0)))
      | ~ m1_subset_1(sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(X0)))
      | v2_struct_0(k2_yellow_1(sK0))
      | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK2,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK1,X0) ) ),
    inference(resolution,[],[f115,f56])).

fof(f115,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,X0)
      | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(X0)))
      | v2_struct_0(k2_yellow_1(sK0))
      | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK2,X0) ) ),
    inference(resolution,[],[f107,f56])).

fof(f107,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,X0)
      | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
      | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(X0)))
      | v2_struct_0(k2_yellow_1(sK0))
      | ~ r2_hidden(sK1,X0) ) ),
    inference(resolution,[],[f105,f87])).

fof(f87,plain,(
    ! [X4,X0,X5] :
      ( ~ r1_tarski(X4,X5)
      | r2_hidden(k4_tarski(X4,X5),u1_orders_2(k2_yellow_1(X0)))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0) ) ),
    inference(subsumption_resolution,[],[f80,f75])).

fof(f80,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),u1_orders_2(k2_yellow_1(X0)))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(u1_orders_2(k2_yellow_1(X0))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | u1_orders_2(k2_yellow_1(X0)) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f49,f67])).

fof(f49,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f105,plain,
    ( r1_tarski(sK1,sK2)
    | v2_struct_0(k2_yellow_1(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f104,f83])).

fof(f104,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v2_struct_0(k2_yellow_1(sK0))
    | r1_tarski(sK1,sK2)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f103,f60])).

fof(f103,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | r1_tarski(sK1,sK2)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f102,f84])).

fof(f102,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | v2_struct_0(k2_yellow_1(sK0))
    | r1_tarski(sK1,sK2)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f101,f60])).

fof(f101,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | r1_tarski(sK1,sK2)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f100,f62])).

fof(f100,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | r1_tarski(sK1,sK2)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f99,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
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
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f99,plain,
    ( r1_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | v2_struct_0(k2_yellow_1(sK0))
    | r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f98,f83])).

fof(f98,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | v2_struct_0(k2_yellow_1(sK0))
    | r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f97,f84])).

fof(f97,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | v2_struct_0(k2_yellow_1(sK0))
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f96,f45])).

fof(f45,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f95,f60])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f94,f60])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f93,f62])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f54,f66])).

fof(f66,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f22])).

% (25260)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f133,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f132,f83])).

fof(f132,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK1,sK0)
    | r3_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f131,f84])).

fof(f131,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | r3_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | r3_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f128,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f111,f60])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f110,f60])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f109,f62])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f55,f66])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r3_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f128,plain,
    ( r1_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f127,f83])).

fof(f127,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v2_struct_0(k2_yellow_1(sK0))
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    inference(forward_demodulation,[],[f126,f60])).

fof(f126,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f125,f84])).

fof(f125,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | v2_struct_0(k2_yellow_1(sK0))
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f124,f60])).

fof(f124,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f123,f62])).

fof(f123,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f121,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f46,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r3_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (25281)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (25259)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (25265)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (25259)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (25269)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (25265)Refutation not found, incomplete strategy% (25265)------------------------------
% 0.21/0.52  % (25265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f146,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ~v1_xboole_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    (((~r1_tarski(sK1,sK2) | ~r3_orders_2(k2_yellow_1(sK0),sK1,sK2)) & (r1_tarski(sK1,sK2) | r3_orders_2(k2_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & ~v1_xboole_0(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33,f32,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) & (r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(sK0),X1,X2)) & (r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(sK0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & ~v1_xboole_0(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(sK0),X1,X2)) & (r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(sK0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) => (? [X2] : ((~r1_tarski(sK1,X2) | ~r3_orders_2(k2_yellow_1(sK0),sK1,X2)) & (r1_tarski(sK1,X2) | r3_orders_2(k2_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ? [X2] : ((~r1_tarski(sK1,X2) | ~r3_orders_2(k2_yellow_1(sK0),sK1,X2)) & (r1_tarski(sK1,X2) | r3_orders_2(k2_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) => ((~r1_tarski(sK1,sK2) | ~r3_orders_2(k2_yellow_1(sK0),sK1,sK2)) & (r1_tarski(sK1,sK2) | r3_orders_2(k2_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) & (r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & ~v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) & (r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2))) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & ~v1_xboole_0(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    v1_xboole_0(sK0)),
% 0.21/0.52    inference(forward_demodulation,[],[f145,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : (k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0)) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    v1_xboole_0(u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f144,f88])).
% 0.21/0.52  % (25264)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ( ! [X0] : (l1_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(resolution,[],[f65,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    ~l1_struct_0(k2_yellow_1(sK0)) | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.52    inference(resolution,[],[f143,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f142,f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    m1_subset_1(sK1,sK0)),
% 0.21/0.52    inference(backward_demodulation,[],[f43,f60])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f141,f42])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    v2_struct_0(k2_yellow_1(sK0)) | v1_xboole_0(sK0) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.52    inference(resolution,[],[f140,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    ~r2_hidden(sK1,sK0) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.52    inference(global_subsumption,[],[f46,f133,f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2) | v2_struct_0(k2_yellow_1(sK0)) | ~r2_hidden(sK1,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f138,f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    m1_subset_1(sK2,sK0)),
% 0.21/0.52    inference(backward_demodulation,[],[f44,f60])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2) | v2_struct_0(k2_yellow_1(sK0)) | ~r2_hidden(sK1,sK0) | ~m1_subset_1(sK2,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f137,f42])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2) | v2_struct_0(k2_yellow_1(sK0)) | ~r2_hidden(sK1,sK0) | v1_xboole_0(sK0) | ~m1_subset_1(sK2,sK0)),
% 0.21/0.52    inference(resolution,[],[f122,f56])).
% 0.21/0.52  % (25265)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    ~r2_hidden(sK2,sK0) | r1_tarski(sK1,sK2) | v2_struct_0(k2_yellow_1(sK0)) | ~r2_hidden(sK1,sK0)),
% 0.21/0.52    inference(resolution,[],[f121,f86])).
% 0.21/0.52  
% 0.21/0.52  % (25265)Memory used [KB]: 10618
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ( ! [X4,X0,X5] : (~r2_hidden(k4_tarski(X4,X5),u1_orders_2(k2_yellow_1(X0))) | r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f81,f75])).
% 0.21/0.52  % (25265)Time elapsed: 0.101 s
% 0.21/0.52  % (25265)------------------------------
% 0.21/0.52  % (25265)------------------------------
% 0.21/0.52  % (25264)Refutation not found, incomplete strategy% (25264)------------------------------
% 0.21/0.52  % (25264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(u1_orders_2(k2_yellow_1(X0)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f64,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0] : (k1_wellord2(X0) = u1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f63,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0] : (k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0] : (k1_wellord2(X0) = k1_yellow_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : k1_wellord2(X0) = k1_yellow_1(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_yellow_1)).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X4,X0,X5] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),u1_orders_2(k2_yellow_1(X0))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(u1_orders_2(k2_yellow_1(X0)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X4,X0,X5,X1] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | u1_orders_2(k2_yellow_1(X0)) != X1 | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f48,f67])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X4,X0,X5,X1] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(rectify,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f120,f83])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    v2_struct_0(k2_yellow_1(sK0)) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f119,f42])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    v2_struct_0(k2_yellow_1(sK0)) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | v1_xboole_0(sK0) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f118])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    v2_struct_0(k2_yellow_1(sK0)) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | v1_xboole_0(sK0) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.52    inference(resolution,[],[f117,f84])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK2,X0) | v2_struct_0(k2_yellow_1(sK0)) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | v1_xboole_0(X0) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(X0))) | ~m1_subset_1(sK1,X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f116])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(X0))) | v2_struct_0(k2_yellow_1(sK0)) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | v1_xboole_0(X0) | ~m1_subset_1(sK2,X0) | v1_xboole_0(X0) | ~m1_subset_1(sK1,X0)) )),
% 0.21/0.52    inference(resolution,[],[f115,f56])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK1,X0) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(X0))) | v2_struct_0(k2_yellow_1(sK0)) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | v1_xboole_0(X0) | ~m1_subset_1(sK2,X0)) )),
% 0.21/0.52    inference(resolution,[],[f107,f56])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK2,X0) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(X0))) | v2_struct_0(k2_yellow_1(sK0)) | ~r2_hidden(sK1,X0)) )),
% 0.21/0.52    inference(resolution,[],[f105,f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ( ! [X4,X0,X5] : (~r1_tarski(X4,X5) | r2_hidden(k4_tarski(X4,X5),u1_orders_2(k2_yellow_1(X0))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f80,f75])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),u1_orders_2(k2_yellow_1(X0))) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(u1_orders_2(k2_yellow_1(X0)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | u1_orders_2(k2_yellow_1(X0)) != X1 | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f49,f67])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2) | v2_struct_0(k2_yellow_1(sK0)) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f104,f83])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,sK0) | v2_struct_0(k2_yellow_1(sK0)) | r1_tarski(sK1,sK2) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))),
% 0.21/0.52    inference(forward_demodulation,[],[f103,f60])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    v2_struct_0(k2_yellow_1(sK0)) | r1_tarski(sK1,sK2) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f102,f84])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,sK0) | v2_struct_0(k2_yellow_1(sK0)) | r1_tarski(sK1,sK2) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.52    inference(forward_demodulation,[],[f101,f60])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    v2_struct_0(k2_yellow_1(sK0)) | r1_tarski(sK1,sK2) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f100,f62])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    v2_struct_0(k2_yellow_1(sK0)) | r1_tarski(sK1,sK2) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0))),
% 0.21/0.52    inference(resolution,[],[f99,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    r1_orders_2(k2_yellow_1(sK0),sK1,sK2) | v2_struct_0(k2_yellow_1(sK0)) | r1_tarski(sK1,sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f98,f83])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,sK0) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) | v2_struct_0(k2_yellow_1(sK0)) | r1_tarski(sK1,sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f97,f84])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) | v2_struct_0(k2_yellow_1(sK0)) | r1_tarski(sK1,sK2)),
% 0.21/0.52    inference(resolution,[],[f96,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    r3_orders_2(k2_yellow_1(sK0),sK1,sK2) | r1_tarski(sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f95,f60])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f94,f60])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f93,f62])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(resolution,[],[f54,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : v3_orders_2(k2_yellow_1(X0))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v3_orders_2(X0) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f22])).
% 0.21/0.52  % (25260)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    r3_orders_2(k2_yellow_1(sK0),sK1,sK2) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f132,f83])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(sK1,sK0) | r3_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f131,f84])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0) | r3_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f129])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0) | r3_orders_2(k2_yellow_1(sK0),sK1,sK2) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.52    inference(resolution,[],[f128,f112])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | r3_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f111,f60])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r3_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f110,f60])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r3_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f109,f62])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | r3_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(resolution,[],[f55,f66])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v3_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r3_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    r1_orders_2(k2_yellow_1(sK0),sK1,sK2) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f127,f83])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,sK0) | v2_struct_0(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.52    inference(forward_demodulation,[],[f126,f60])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    v2_struct_0(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f125,f84])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,sK0) | v2_struct_0(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.52    inference(forward_demodulation,[],[f124,f60])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    v2_struct_0(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f123,f62])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    v2_struct_0(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0))),
% 0.21/0.52    inference(resolution,[],[f121,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ~r1_tarski(sK1,sK2) | ~r3_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (25259)------------------------------
% 0.21/0.52  % (25259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (25259)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (25259)Memory used [KB]: 6268
% 0.21/0.52  % (25259)Time elapsed: 0.109 s
% 0.21/0.52  % (25259)------------------------------
% 0.21/0.52  % (25259)------------------------------
% 0.21/0.52  % (25253)Success in time 0.17 s
%------------------------------------------------------------------------------
