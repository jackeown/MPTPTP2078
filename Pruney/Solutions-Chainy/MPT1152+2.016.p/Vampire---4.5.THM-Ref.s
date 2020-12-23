%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 (1570 expanded)
%              Number of leaves         :   17 ( 431 expanded)
%              Depth                    :   23
%              Number of atoms          :  427 (8026 expanded)
%              Number of equality atoms :   74 (1359 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(global_subsumption,[],[f80,f170,f233])).

fof(f233,plain,
    ( v1_xboole_0(k2_struct_0(sK2))
    | ~ m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(resolution,[],[f231,f61])).

fof(f61,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f231,plain,(
    ~ r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(global_subsumption,[],[f164,f168,f230])).

fof(f230,plain,
    ( r2_orders_2(sK2,sK3(k2_orders_2(sK2,k2_struct_0(sK2))),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))
    | ~ r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | ~ sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(superposition,[],[f176,f166])).

fof(f166,plain,(
    sK3(k2_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(global_subsumption,[],[f48,f165])).

fof(f165,plain,
    ( sK3(k2_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f151,f149])).

fof(f149,plain,(
    k2_orders_2(sK2,k2_struct_0(sK2)) = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f148,f76])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f50,f49])).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f148,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) ) ),
    inference(global_subsumption,[],[f47,f45,f44,f43,f147])).

fof(f147,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(forward_demodulation,[],[f146,f78])).

fof(f78,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f51,f77])).

fof(f77,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f52,f47])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f146,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f56,f46])).

fof(f46,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2))
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f151,plain,
    ( k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2))
    | sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f118,f149])).

fof(f118,plain,
    ( sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f117,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK5(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ( ~ r2_orders_2(X0,X3,sK4(X0,X1,X3))
              & r2_hidden(sK4(X0,X1,X3),X1)
              & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ( ! [X6] :
              ( r2_orders_2(X0,sK5(X0,X1,X2),X6)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & sK5(X0,X1,X2) = X2
          & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f39,f41,f40])).

fof(f40,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_orders_2(X0,X3,X4)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,X3,sK4(X0,X1,X3))
        & r2_hidden(sK4(X0,X1,X3),X1)
        & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

% (13675)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X0,X5,X6)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & X2 = X5
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r2_orders_2(X0,sK5(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X1)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & sK5(X0,X1,X2) = X2
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_orders_2(X0,X3,X4)
                & r2_hidden(X4,X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ? [X5] :
            ( ! [X6] :
                ( r2_orders_2(X0,X5,X6)
                | ~ r2_hidden(X6,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            & X2 = X5
            & m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
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
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( ! [X4] :
              ( r2_orders_2(X1,X3,X4)
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f117,plain,
    ( sP0(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f85,f116])).

fof(f116,plain,(
    ! [X0] : sP1(X0,k2_struct_0(sK2),sK2) ),
    inference(resolution,[],[f115,f76])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | sP1(X1,X0,sK2) ) ),
    inference(global_subsumption,[],[f47,f45,f44,f43,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(forward_demodulation,[],[f113,f78])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f70,f46])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | sP1(X0,X2,X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f26,f28,f27])).

fof(f28,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ sP1(sK3(a_2_1_orders_2(X0,X1)),X1,X0)
      | sP0(X0,X1,sK3(a_2_1_orders_2(X0,X1)))
      | k1_xboole_0 = a_2_1_orders_2(X0,X1) ) ),
    inference(resolution,[],[f62,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(X2,X1))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X2,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X2,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f48,plain,(
    k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f176,plain,(
    ! [X2,X3] :
      ( r2_orders_2(sK2,sK5(sK2,X2,X3),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))
      | ~ r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),X2)
      | ~ sP0(sK2,X2,X3) ) ),
    inference(global_subsumption,[],[f48,f175])).

fof(f175,plain,(
    ! [X2,X3] :
      ( r2_orders_2(sK2,sK5(sK2,X2,X3),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))
      | ~ r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),X2)
      | k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2))
      | ~ sP0(sK2,X2,X3) ) ),
    inference(forward_demodulation,[],[f174,f149])).

fof(f174,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),X2)
      | k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2))
      | r2_orders_2(sK2,sK5(sK2,X2,X3),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))))
      | ~ sP0(sK2,X2,X3) ) ),
    inference(forward_demodulation,[],[f155,f149])).

fof(f155,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2))
      | ~ r2_hidden(sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))),X2)
      | r2_orders_2(sK2,sK5(sK2,X2,X3),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))))
      | ~ sP0(sK2,X2,X3) ) ),
    inference(backward_demodulation,[],[f126,f149])).

fof(f126,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))
      | ~ r2_hidden(sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))),X2)
      | r2_orders_2(sK2,sK5(sK2,X2,X3),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))))
      | ~ sP0(sK2,X2,X3) ) ),
    inference(resolution,[],[f123,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK2))
      | ~ r2_hidden(X0,X1)
      | r2_orders_2(sK2,sK5(sK2,X1,X2),X0)
      | ~ sP0(sK2,X1,X2) ) ),
    inference(superposition,[],[f66,f78])).

fof(f66,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ r2_hidden(X6,X1)
      | r2_orders_2(X0,sK5(X0,X1,X2),X6)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f123,plain,
    ( m1_subset_1(sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(global_subsumption,[],[f117,f120])).

fof(f120,plain,
    ( m1_subset_1(sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | ~ sP0(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(superposition,[],[f83,f118])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(sK2,X0,X1),k2_struct_0(sK2))
      | ~ sP0(sK2,X0,X1) ) ),
    inference(superposition,[],[f64,f78])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f168,plain,(
    ~ r2_orders_2(sK2,sK3(k2_orders_2(sK2,k2_struct_0(sK2))),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(global_subsumption,[],[f48,f167])).

fof(f167,plain,
    ( ~ r2_orders_2(sK2,sK3(k2_orders_2(sK2,k2_struct_0(sK2))),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f152,f149])).

fof(f152,plain,
    ( k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2))
    | ~ r2_orders_2(sK2,sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f122,f149])).

fof(f122,plain,
    ( ~ r2_orders_2(sK2,sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(global_subsumption,[],[f117,f119])).

% (13687)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f119,plain,
    ( ~ r2_orders_2(sK2,sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))))
    | ~ sP0(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(superposition,[],[f84,f118])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_orders_2(sK2,sK5(sK2,X0,X1),sK5(sK2,X0,X1))
      | ~ sP0(sK2,X0,X1) ) ),
    inference(resolution,[],[f83,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK2))
      | ~ r2_orders_2(sK2,X0,X0) ) ),
    inference(forward_demodulation,[],[f81,f78])).

fof(f81,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_orders_2(sK2,X0,X0) ) ),
    inference(resolution,[],[f75,f47])).

fof(f75,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X2,X2) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f164,plain,(
    sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(global_subsumption,[],[f48,f163])).

fof(f163,plain,
    ( k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2))
    | sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(forward_demodulation,[],[f150,f149])).

fof(f150,plain,
    ( sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f117,f149])).

fof(f170,plain,(
    m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(global_subsumption,[],[f48,f169])).

fof(f169,plain,
    ( m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f153,f149])).

fof(f153,plain,
    ( k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2))
    | m1_subset_1(sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f123,f149])).

fof(f80,plain,(
    ~ v1_xboole_0(k2_struct_0(sK2)) ),
    inference(global_subsumption,[],[f43,f77,f79])).

fof(f79,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f57,f78])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:19:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (13677)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.48  % (13677)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (13682)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.48  % (13669)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(global_subsumption,[],[f80,f170,f233])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    v1_xboole_0(k2_struct_0(sK2)) | ~m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 0.21/0.48    inference(resolution,[],[f231,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    ~r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 0.21/0.48    inference(global_subsumption,[],[f164,f168,f230])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    r2_orders_2(sK2,sK3(k2_orders_2(sK2,k2_struct_0(sK2))),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) | ~r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | ~sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.48    inference(superposition,[],[f176,f166])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    sK3(k2_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.48    inference(global_subsumption,[],[f48,f165])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    sK3(k2_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.48    inference(forward_demodulation,[],[f151,f149])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    k2_orders_2(sK2,k2_struct_0(sK2)) = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.48    inference(resolution,[],[f148,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f50,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)) )),
% 0.21/0.48    inference(global_subsumption,[],[f47,f45,f44,f43,f147])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_orders_2(sK2) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f146,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 0.21/0.48    inference(resolution,[],[f51,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    l1_struct_0(sK2)),
% 0.21/0.48    inference(resolution,[],[f52,f47])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(resolution,[],[f56,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    v5_orders_2(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2)) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2)) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.48    inference(negated_conjecture,[],[f11])).
% 0.21/0.48  fof(f11,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ~v2_struct_0(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    v3_orders_2(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    v4_orders_2(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    l1_orders_2(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2)) | sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.48    inference(backward_demodulation,[],[f118,f149])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.48    inference(resolution,[],[f117,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | sK5(X0,X1,X2) = X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,X3,sK4(X0,X1,X3)) & r2_hidden(sK4(X0,X1,X3),X1) & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,sK5(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK5(X0,X1,X2) = X2 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f39,f41,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,X3,sK4(X0,X1,X3)) & r2_hidden(sK4(X0,X1,X3),X1) & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  % (13675)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,sK5(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK5(X0,X1,X2) = X2 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.21/0.48    inference(rectify,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X1,X2,X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    sP0(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.48    inference(resolution,[],[f85,f116])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X0] : (sP1(X0,k2_struct_0(sK2),sK2)) )),
% 0.21/0.48    inference(resolution,[],[f115,f76])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | sP1(X1,X0,sK2)) )),
% 0.21/0.48    inference(global_subsumption,[],[f47,f45,f44,f43,f114])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_orders_2(sK2) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f113,f78])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(resolution,[],[f70,f46])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | sP1(X0,X2,X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.48    inference(definition_folding,[],[f26,f28,f27])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sP1(sK3(a_2_1_orders_2(X0,X1)),X1,X0) | sP0(X0,X1,sK3(a_2_1_orders_2(X0,X1))) | k1_xboole_0 = a_2_1_orders_2(X0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f62,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(X2,X1)) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X2,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,a_2_1_orders_2(X2,X1)))) | ~sP1(X0,X1,X2))),
% 0.21/0.48    inference(rectify,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~sP1(X0,X2,X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f28])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    ( ! [X2,X3] : (r2_orders_2(sK2,sK5(sK2,X2,X3),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) | ~r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),X2) | ~sP0(sK2,X2,X3)) )),
% 0.21/0.48    inference(global_subsumption,[],[f48,f175])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    ( ! [X2,X3] : (r2_orders_2(sK2,sK5(sK2,X2,X3),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) | ~r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),X2) | k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2)) | ~sP0(sK2,X2,X3)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f174,f149])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),X2) | k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2)) | r2_orders_2(sK2,sK5(sK2,X2,X3),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))) | ~sP0(sK2,X2,X3)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f155,f149])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2)) | ~r2_hidden(sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))),X2) | r2_orders_2(sK2,sK5(sK2,X2,X3),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))) | ~sP0(sK2,X2,X3)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f126,f149])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) | ~r2_hidden(sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))),X2) | r2_orders_2(sK2,sK5(sK2,X2,X3),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))) | ~sP0(sK2,X2,X3)) )),
% 0.21/0.48    inference(resolution,[],[f123,f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK2)) | ~r2_hidden(X0,X1) | r2_orders_2(sK2,sK5(sK2,X1,X2),X0) | ~sP0(sK2,X1,X2)) )),
% 0.21/0.48    inference(superposition,[],[f66,f78])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X6,X2,X0,X1] : (~m1_subset_1(X6,u1_struct_0(X0)) | ~r2_hidden(X6,X1) | r2_orders_2(X0,sK5(X0,X1,X2),X6) | ~sP0(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f42])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    m1_subset_1(sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.48    inference(global_subsumption,[],[f117,f120])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    m1_subset_1(sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | ~sP0(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.48    inference(superposition,[],[f83,f118])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(sK5(sK2,X0,X1),k2_struct_0(sK2)) | ~sP0(sK2,X0,X1)) )),
% 0.21/0.48    inference(superposition,[],[f64,f78])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f42])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    ~r2_orders_2(sK2,sK3(k2_orders_2(sK2,k2_struct_0(sK2))),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.48    inference(global_subsumption,[],[f48,f167])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    ~r2_orders_2(sK2,sK3(k2_orders_2(sK2,k2_struct_0(sK2))),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.48    inference(forward_demodulation,[],[f152,f149])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2)) | ~r2_orders_2(sK2,sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.48    inference(backward_demodulation,[],[f122,f149])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    ~r2_orders_2(sK2,sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.48    inference(global_subsumption,[],[f117,f119])).
% 0.21/0.49  % (13687)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ~r2_orders_2(sK2,sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))) | ~sP0(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.49    inference(superposition,[],[f84,f118])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_orders_2(sK2,sK5(sK2,X0,X1),sK5(sK2,X0,X1)) | ~sP0(sK2,X0,X1)) )),
% 0.21/0.49    inference(resolution,[],[f83,f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK2)) | ~r2_orders_2(sK2,X0,X0)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f81,f78])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~r2_orders_2(sK2,X0,X0)) )),
% 0.21/0.49    inference(resolution,[],[f75,f47])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(flattening,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.49    inference(global_subsumption,[],[f48,f163])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2)) | sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.49    inference(forward_demodulation,[],[f150,f149])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.49    inference(backward_demodulation,[],[f117,f149])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 0.21/0.49    inference(global_subsumption,[],[f48,f169])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.49    inference(forward_demodulation,[],[f153,f149])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2)) | m1_subset_1(sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 0.21/0.49    inference(backward_demodulation,[],[f123,f149])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ~v1_xboole_0(k2_struct_0(sK2))),
% 0.21/0.49    inference(global_subsumption,[],[f43,f77,f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ~v1_xboole_0(k2_struct_0(sK2)) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.21/0.49    inference(superposition,[],[f57,f78])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (13677)------------------------------
% 0.21/0.49  % (13677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13677)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (13677)Memory used [KB]: 6396
% 0.21/0.49  % (13677)Time elapsed: 0.077 s
% 0.21/0.49  % (13677)------------------------------
% 0.21/0.49  % (13677)------------------------------
% 0.21/0.49  % (13679)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (13664)Success in time 0.137 s
%------------------------------------------------------------------------------
