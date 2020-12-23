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
% DateTime   : Thu Dec  3 13:09:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 (2188 expanded)
%              Number of leaves         :   20 ( 574 expanded)
%              Depth                    :   30
%              Number of atoms          :  453 (10949 expanded)
%              Number of equality atoms :   75 (1858 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f206,plain,(
    $false ),
    inference(subsumption_resolution,[],[f205,f146])).

fof(f146,plain,(
    m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f145,f143])).

fof(f143,plain,(
    sK3(k1_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(resolution,[],[f139,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK5(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ( ~ r2_orders_2(X0,sK4(X0,X1,X3),X3)
              & r2_hidden(sK4(X0,X1,X3),X1)
              & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ( ! [X6] :
              ( r2_orders_2(X0,X6,sK5(X0,X1,X2))
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & sK5(X0,X1,X2) = X2
          & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f47,f46])).

fof(f46,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_orders_2(X0,X4,X3)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,sK4(X0,X1,X3),X3)
        & r2_hidden(sK4(X0,X1,X3),X1)
        & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X0,X6,X5)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & X2 = X5
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r2_orders_2(X0,X6,sK5(X0,X1,X2))
            | ~ r2_hidden(X6,X1)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & sK5(X0,X1,X2) = X2
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_orders_2(X0,X4,X3)
                & r2_hidden(X4,X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ? [X5] :
            ( ! [X6] :
                ( r2_orders_2(X0,X6,X5)
                | ~ r2_hidden(X6,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            & X2 = X5
            & m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_orders_2(X1,X4,X3)
                & r2_hidden(X4,X2)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( ! [X4] :
              ( r2_orders_2(X1,X4,X3)
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f139,plain,(
    sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(forward_demodulation,[],[f138,f128])).

fof(f128,plain,(
    k1_orders_2(sK2,k2_struct_0(sK2)) = a_2_0_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f125,f86])).

fof(f86,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f58,f56])).

fof(f56,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) ) ),
    inference(forward_demodulation,[],[f124,f89])).

fof(f89,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f60,f87])).

fof(f87,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f61,f53])).

fof(f53,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2))
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f60,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f124,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f123,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f122,f50])).

fof(f50,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f121,f51])).

fof(f51,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f120,f53])).

fof(f120,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f66,f52])).

fof(f52,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

% (12270)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
fof(f138,plain,(
    sP0(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f135,f54])).

fof(f54,plain,(
    k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f135,plain,
    ( k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2))
    | sP0(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f126,f128])).

fof(f126,plain,
    ( sP0(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = a_2_0_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f118,f67])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f118,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_0_orders_2(sK2,k2_struct_0(sK2)))
      | sP0(sK2,k2_struct_0(sK2),X1) ) ),
    inference(resolution,[],[f113,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X0,a_2_0_orders_2(X2,X1))
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X2,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_0_orders_2(X2,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f113,plain,(
    ! [X1] : sP1(X1,k2_struct_0(sK2),sK2) ),
    inference(resolution,[],[f111,f86])).

% (12254)Refutation not found, incomplete strategy% (12254)------------------------------
% (12254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12254)Termination reason: Refutation not found, incomplete strategy

% (12254)Memory used [KB]: 1663
% (12254)Time elapsed: 0.123 s
% (12254)------------------------------
% (12254)------------------------------
% (12265)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (12258)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (12272)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (12267)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | sP1(X1,X0,sK2) ) ),
    inference(forward_demodulation,[],[f110,f89])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f109,f49])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f108,f50])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f107,f51])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f106,f53])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f79,f52])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | sP1(X0,X2,X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f30,f34,f33])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X4,X3) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f145,plain,(
    m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f142,f89])).

fof(f142,plain,(
    m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))),u1_struct_0(sK2)) ),
    inference(resolution,[],[f139,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f205,plain,(
    ~ m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f204,f89])).

fof(f204,plain,(
    ~ m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f203,f53])).

fof(f203,plain,
    ( ~ m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f201,f85])).

fof(f85,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f201,plain,(
    r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2))),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f197,f146])).

fof(f197,plain,
    ( ~ m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2))),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(resolution,[],[f189,f147])).

fof(f147,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_struct_0(sK2))
      | ~ m1_subset_1(X0,k2_struct_0(sK2))
      | r2_orders_2(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ) ),
    inference(backward_demodulation,[],[f144,f143])).

fof(f144,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK2))
      | ~ r2_hidden(X0,k2_struct_0(sK2))
      | r2_orders_2(sK2,X0,sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2))))) ) ),
    inference(forward_demodulation,[],[f141,f89])).

fof(f141,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r2_orders_2(sK2,X0,sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2))))) ) ),
    inference(resolution,[],[f139,f75])).

fof(f75,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X6,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | r2_orders_2(X0,X6,sK5(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f189,plain,(
    r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(resolution,[],[f188,f133])).

fof(f133,plain,(
    ! [X0] :
      ( ~ sP0(sK2,k1_xboole_0,X0)
      | r2_hidden(X0,k2_struct_0(sK2)) ) ),
    inference(backward_demodulation,[],[f115,f130])).

fof(f130,plain,(
    k2_struct_0(sK2) = a_2_0_orders_2(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f127,f105])).

fof(f105,plain,(
    k2_struct_0(sK2) = k1_orders_2(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f104,f89])).

fof(f104,plain,(
    u1_struct_0(sK2) = k1_orders_2(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f103,f88])).

fof(f88,plain,(
    k1_xboole_0 = k1_struct_0(sK2) ),
    inference(resolution,[],[f59,f87])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

fof(f103,plain,(
    u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f102,f49])).

fof(f102,plain,
    ( u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f101,f50])).

fof(f101,plain,
    ( u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2))
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f100,f51])).

fof(f100,plain,
    ( u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2))
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f99,f53])).

fof(f99,plain,
    ( ~ l1_orders_2(sK2)
    | u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2))
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f65,f52])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_orders_2)).

fof(f127,plain,(
    k1_orders_2(sK2,k1_xboole_0) = a_2_0_orders_2(sK2,k1_xboole_0) ),
    inference(resolution,[],[f125,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f115,plain,(
    ! [X0] :
      ( ~ sP0(sK2,k1_xboole_0,X0)
      | r2_hidden(X0,a_2_0_orders_2(sK2,k1_xboole_0)) ) ),
    inference(resolution,[],[f112,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_hidden(X0,a_2_0_orders_2(X2,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f112,plain,(
    ! [X0] : sP1(X0,k1_xboole_0,sK2) ),
    inference(resolution,[],[f111,f57])).

fof(f188,plain,(
    sP0(sK2,k1_xboole_0,sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(resolution,[],[f179,f55])).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f179,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK4(sK2,X2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)))))
      | sP0(sK2,X2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ) ),
    inference(resolution,[],[f148,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f148,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2)))),X0)
      | sP0(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2)))) ) ),
    inference(resolution,[],[f146,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK2))
      | r2_hidden(sK4(sK2,X1,X0),X1)
      | sP0(sK2,X1,X0) ) ),
    inference(superposition,[],[f83,f89])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_hidden(sK4(X0,X1,X3),X1)
      | sP0(X0,X1,X3) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X3),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:20:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (12269)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.48  % (12253)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.48  % (12255)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.48  % (12271)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.48  % (12253)Refutation not found, incomplete strategy% (12253)------------------------------
% 0.21/0.48  % (12253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12253)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (12253)Memory used [KB]: 10618
% 0.21/0.49  % (12253)Time elapsed: 0.033 s
% 0.21/0.49  % (12253)------------------------------
% 0.21/0.49  % (12253)------------------------------
% 0.21/0.49  % (12259)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (12252)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (12252)Refutation not found, incomplete strategy% (12252)------------------------------
% 0.21/0.50  % (12252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12252)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12252)Memory used [KB]: 6140
% 0.21/0.50  % (12252)Time elapsed: 0.088 s
% 0.21/0.50  % (12252)------------------------------
% 0.21/0.50  % (12252)------------------------------
% 0.21/0.50  % (12268)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (12251)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (12248)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (12249)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (12260)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (12260)Refutation not found, incomplete strategy% (12260)------------------------------
% 0.21/0.51  % (12260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12260)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12260)Memory used [KB]: 6140
% 0.21/0.51  % (12260)Time elapsed: 0.101 s
% 0.21/0.51  % (12260)------------------------------
% 0.21/0.51  % (12260)------------------------------
% 0.21/0.51  % (12266)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (12247)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (12247)Refutation not found, incomplete strategy% (12247)------------------------------
% 0.21/0.51  % (12247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12247)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12247)Memory used [KB]: 10490
% 0.21/0.51  % (12247)Time elapsed: 0.098 s
% 0.21/0.51  % (12247)------------------------------
% 0.21/0.51  % (12247)------------------------------
% 0.21/0.51  % (12261)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (12263)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (12262)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (12256)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (12257)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (12250)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (12264)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (12254)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (12250)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f205,f146])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 0.21/0.53    inference(backward_demodulation,[],[f145,f143])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    sK3(k1_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.53    inference(resolution,[],[f139,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | sK5(X0,X1,X2) = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,sK4(X0,X1,X3),X3) & r2_hidden(sK4(X0,X1,X3),X1) & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,X6,sK5(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK5(X0,X1,X2) = X2 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f47,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X4,X3) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,sK4(X0,X1,X3),X3) & r2_hidden(sK4(X0,X1,X3),X1) & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X6,X5) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,X6,sK5(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK5(X0,X1,X2) = X2 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X4,X3) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X6,X5) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.21/0.53    inference(rectify,[],[f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X1,X2,X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.53    inference(forward_demodulation,[],[f138,f128])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    k1_orders_2(sK2,k2_struct_0(sK2)) = a_2_0_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.53    inference(resolution,[],[f125,f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f58,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f124,f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f60,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    l1_struct_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f61,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    l1_orders_2(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2)) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2)) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.53    inference(negated_conjecture,[],[f15])).
% 0.21/0.53  fof(f15,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f123,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ~v2_struct_0(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) | v2_struct_0(sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f122,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    v3_orders_2(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f121,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    v4_orders_2(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f120,f53])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.53    inference(resolution,[],[f66,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    v5_orders_2(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).
% 0.21/0.53  % (12270)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    sP0(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.53    inference(subsumption_resolution,[],[f135,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2)) | sP0(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.53    inference(backward_demodulation,[],[f126,f128])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    sP0(sK2,k2_struct_0(sK2),sK3(a_2_0_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = a_2_0_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.53    inference(resolution,[],[f118,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(X1,a_2_0_orders_2(sK2,k2_struct_0(sK2))) | sP0(sK2,k2_struct_0(sK2),X1)) )),
% 0.21/0.53    inference(resolution,[],[f113,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X0,a_2_0_orders_2(X2,X1)) | sP0(X2,X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X2,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,a_2_0_orders_2(X2,X1)))) | ~sP1(X0,X1,X2))),
% 0.21/0.53    inference(rectify,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~sP1(X0,X2,X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X1] : (sP1(X1,k2_struct_0(sK2),sK2)) )),
% 0.21/0.53    inference(resolution,[],[f111,f86])).
% 0.21/0.53  % (12254)Refutation not found, incomplete strategy% (12254)------------------------------
% 0.21/0.53  % (12254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12254)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12254)Memory used [KB]: 1663
% 0.21/0.53  % (12254)Time elapsed: 0.123 s
% 0.21/0.53  % (12254)------------------------------
% 0.21/0.53  % (12254)------------------------------
% 0.21/0.53  % (12265)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (12258)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (12272)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (12267)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | sP1(X1,X0,sK2)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f110,f89])).
% 0.21/0.55  fof(f110,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f109,f49])).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | v2_struct_0(sK2)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f108,f50])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f107,f51])).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f106,f53])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.55    inference(resolution,[],[f79,f52])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | sP1(X0,X2,X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.55    inference(definition_folding,[],[f30,f34,f33])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.55    inference(flattening,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 0.21/0.55  fof(f145,plain,(
% 0.21/0.55    m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2))),
% 0.21/0.55    inference(forward_demodulation,[],[f142,f89])).
% 0.21/0.55  fof(f142,plain,(
% 0.21/0.55    m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))),u1_struct_0(sK2))),
% 0.21/0.55    inference(resolution,[],[f139,f73])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f48])).
% 0.21/0.55  fof(f205,plain,(
% 0.21/0.55    ~m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 0.21/0.55    inference(forward_demodulation,[],[f204,f89])).
% 0.21/0.55  fof(f204,plain,(
% 0.21/0.55    ~m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2))),
% 0.21/0.55    inference(subsumption_resolution,[],[f203,f53])).
% 0.21/0.55  fof(f203,plain,(
% 0.21/0.55    ~m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2)) | ~l1_orders_2(sK2)),
% 0.21/0.55    inference(resolution,[],[f201,f85])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f81])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.55    inference(flattening,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.55  fof(f201,plain,(
% 0.21/0.55    r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2))),sK3(k1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.55    inference(subsumption_resolution,[],[f197,f146])).
% 0.21/0.55  fof(f197,plain,(
% 0.21/0.55    ~m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2))),sK3(k1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.55    inference(resolution,[],[f189,f147])).
% 0.21/0.55  fof(f147,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK2)) | ~m1_subset_1(X0,k2_struct_0(sK2)) | r2_orders_2(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2))))) )),
% 0.21/0.55    inference(backward_demodulation,[],[f144,f143])).
% 0.21/0.55  fof(f144,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK2)) | ~r2_hidden(X0,k2_struct_0(sK2)) | r2_orders_2(sK2,X0,sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f141,f89])).
% 0.21/0.55  fof(f141,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r2_orders_2(sK2,X0,sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)))))) )),
% 0.21/0.55    inference(resolution,[],[f139,f75])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X6,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0)) | r2_orders_2(X0,X6,sK5(X0,X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f48])).
% 0.21/0.55  fof(f189,plain,(
% 0.21/0.55    r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 0.21/0.55    inference(resolution,[],[f188,f133])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    ( ! [X0] : (~sP0(sK2,k1_xboole_0,X0) | r2_hidden(X0,k2_struct_0(sK2))) )),
% 0.21/0.55    inference(backward_demodulation,[],[f115,f130])).
% 0.21/0.55  fof(f130,plain,(
% 0.21/0.55    k2_struct_0(sK2) = a_2_0_orders_2(sK2,k1_xboole_0)),
% 0.21/0.55    inference(forward_demodulation,[],[f127,f105])).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    k2_struct_0(sK2) = k1_orders_2(sK2,k1_xboole_0)),
% 0.21/0.55    inference(forward_demodulation,[],[f104,f89])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    u1_struct_0(sK2) = k1_orders_2(sK2,k1_xboole_0)),
% 0.21/0.55    inference(forward_demodulation,[],[f103,f88])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    k1_xboole_0 = k1_struct_0(sK2)),
% 0.21/0.55    inference(resolution,[],[f59,f87])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2))),
% 0.21/0.55    inference(subsumption_resolution,[],[f102,f49])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2)) | v2_struct_0(sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f101,f50])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2)) | ~v3_orders_2(sK2) | v2_struct_0(sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f100,f51])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2)) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f99,f53])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    ~l1_orders_2(sK2) | u1_struct_0(sK2) = k1_orders_2(sK2,k1_struct_0(sK2)) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)),
% 0.21/0.55    inference(resolution,[],[f65,f52])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X0] : (~v5_orders_2(X0) | ~l1_orders_2(X0) | u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0] : (u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k1_orders_2(X0,k1_struct_0(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_orders_2)).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    k1_orders_2(sK2,k1_xboole_0) = a_2_0_orders_2(sK2,k1_xboole_0)),
% 0.21/0.55    inference(resolution,[],[f125,f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.55  fof(f115,plain,(
% 0.21/0.55    ( ! [X0] : (~sP0(sK2,k1_xboole_0,X0) | r2_hidden(X0,a_2_0_orders_2(sK2,k1_xboole_0))) )),
% 0.21/0.55    inference(resolution,[],[f112,f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_hidden(X0,a_2_0_orders_2(X2,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f43])).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    ( ! [X0] : (sP1(X0,k1_xboole_0,sK2)) )),
% 0.21/0.55    inference(resolution,[],[f111,f57])).
% 0.21/0.55  fof(f188,plain,(
% 0.21/0.55    sP0(sK2,k1_xboole_0,sK3(k1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.55    inference(resolution,[],[f179,f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.55  fof(f179,plain,(
% 0.21/0.55    ( ! [X2] : (~r1_tarski(X2,sK4(sK2,X2,sK3(k1_orders_2(sK2,k2_struct_0(sK2))))) | sP0(sK2,X2,sK3(k1_orders_2(sK2,k2_struct_0(sK2))))) )),
% 0.21/0.55    inference(resolution,[],[f148,f70])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.55  fof(f148,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK4(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2)))),X0) | sP0(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2))))) )),
% 0.21/0.55    inference(resolution,[],[f146,f94])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK2)) | r2_hidden(sK4(sK2,X1,X0),X1) | sP0(sK2,X1,X0)) )),
% 0.21/0.55    inference(superposition,[],[f83,f89])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,u1_struct_0(X0)) | r2_hidden(sK4(X0,X1,X3),X1) | sP0(X0,X1,X3)) )),
% 0.21/0.55    inference(equality_resolution,[],[f77])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | r2_hidden(sK4(X0,X1,X3),X1) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f48])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (12250)------------------------------
% 0.21/0.55  % (12250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12250)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (12250)Memory used [KB]: 6268
% 0.21/0.55  % (12250)Time elapsed: 0.123 s
% 0.21/0.55  % (12250)------------------------------
% 0.21/0.55  % (12250)------------------------------
% 0.21/0.55  % (12246)Success in time 0.191 s
%------------------------------------------------------------------------------
