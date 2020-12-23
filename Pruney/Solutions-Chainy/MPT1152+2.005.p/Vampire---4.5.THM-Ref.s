%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:48 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  168 (1175 expanded)
%              Number of leaves         :   28 ( 307 expanded)
%              Depth                    :   30
%              Number of atoms          :  602 (5606 expanded)
%              Number of equality atoms :   90 ( 898 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2340,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1380,f1384,f2338])).

fof(f2338,plain,(
    ~ spl11_33 ),
    inference(avatar_contradiction_clause,[],[f2337])).

fof(f2337,plain,
    ( $false
    | ~ spl11_33 ),
    inference(subsumption_resolution,[],[f2134,f2328])).

fof(f2328,plain,(
    ~ r2_hidden(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),k2_struct_0(sK6)) ),
    inference(resolution,[],[f1989,f119])).

fof(f119,plain,(
    ! [X2,X1] : ~ sP0(X1,X1,X2) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( X0 != X1
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | X0 = X1
        | ~ r1_orders_2(X2,X1,X0) )
      & ( ( X0 != X1
          & r1_orders_2(X2,X1,X0) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | X1 = X2
        | ~ r1_orders_2(X0,X1,X2) )
      & ( ( X1 != X2
          & r1_orders_2(X0,X1,X2) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | X1 = X2
        | ~ r1_orders_2(X0,X1,X2) )
      & ( ( X1 != X2
          & r1_orders_2(X0,X1,X2) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ( X1 != X2
        & r1_orders_2(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1989,plain,(
    ! [X0] :
      ( sP0(X0,sK7(k2_orders_2(sK6,k2_struct_0(sK6))),sK6)
      | ~ r2_hidden(X0,k2_struct_0(sK6)) ) ),
    inference(subsumption_resolution,[],[f1985,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f1985,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK6))
      | sP0(X0,sK7(k2_orders_2(sK6,k2_struct_0(sK6))),sK6)
      | ~ r2_hidden(X0,k2_struct_0(sK6)) ) ),
    inference(resolution,[],[f958,f1022])).

fof(f1022,plain,(
    ! [X0] :
      ( r2_orders_2(sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6))),X0)
      | ~ r2_hidden(X0,k2_struct_0(sK6)) ) ),
    inference(subsumption_resolution,[],[f1021,f99])).

fof(f1021,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK6))
      | ~ r2_hidden(X0,k2_struct_0(sK6))
      | r2_orders_2(sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6))),X0) ) ),
    inference(forward_demodulation,[],[f1019,f128])).

fof(f128,plain,(
    k2_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(resolution,[],[f80,f125])).

fof(f125,plain,(
    l1_struct_0(sK6) ),
    inference(resolution,[],[f82,f77])).

fof(f77,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( k1_xboole_0 != k2_orders_2(sK6,k2_struct_0(sK6))
    & l1_orders_2(sK6)
    & v5_orders_2(sK6)
    & v4_orders_2(sK6)
    & v3_orders_2(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k2_orders_2(sK6,k2_struct_0(sK6))
      & l1_orders_2(sK6)
      & v5_orders_2(sK6)
      & v4_orders_2(sK6)
      & v3_orders_2(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

fof(f82,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f80,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f1019,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_struct_0(sK6))
      | ~ m1_subset_1(X0,u1_struct_0(sK6))
      | r2_orders_2(sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6))),X0) ) ),
    inference(resolution,[],[f1011,f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r2_orders_2(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ~ r2_orders_2(X1,X0,sK10(X0,X1,X2))
          & r2_hidden(sK10(X0,X1,X2),X2)
          & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f70,f71])).

fof(f71,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_orders_2(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X0,sK10(X0,X1,X2))
        & r2_hidden(sK10(X0,X1,X2),X2)
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ~ r2_orders_2(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X3,X1,X2] :
      ( ( sP3(X3,X1,X2)
        | ? [X4] :
            ( ~ r2_orders_2(X1,X3,X4)
            & r2_hidden(X4,X2)
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X3,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X3,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X3,X1,X2] :
      ( sP3(X3,X1,X2)
    <=> ! [X4] :
          ( r2_orders_2(X1,X3,X4)
          | ~ r2_hidden(X4,X2)
          | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f1011,plain,(
    sP3(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),sK6,k2_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f1003,f718])).

fof(f718,plain,(
    sP4(k2_struct_0(sK6),sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6)))) ),
    inference(subsumption_resolution,[],[f715,f78])).

fof(f78,plain,(
    k1_xboole_0 != k2_orders_2(sK6,k2_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f50])).

fof(f715,plain,
    ( sP4(k2_struct_0(sK6),sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6))))
    | k1_xboole_0 = k2_orders_2(sK6,k2_struct_0(sK6)) ),
    inference(resolution,[],[f698,f92])).

fof(f92,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( sP2(sK7(X0),X0)
        & r2_hidden(sK7(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP2(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP2(sK7(X0),X0)
        & r2_hidden(sK7(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP2(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f27,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ! [X2,X3,X4] :
          ( k3_mcart_1(X2,X3,X4) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f698,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_orders_2(sK6,k2_struct_0(sK6)))
      | sP4(k2_struct_0(sK6),sK6,X3) ) ),
    inference(subsumption_resolution,[],[f694,f575])).

fof(f575,plain,(
    ! [X3] : sP5(X3,sK6,k2_struct_0(sK6)) ),
    inference(resolution,[],[f572,f145])).

fof(f145,plain,(
    m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(k2_struct_0(sK6))) ),
    inference(subsumption_resolution,[],[f144,f125])).

fof(f144,plain,
    ( m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(k2_struct_0(sK6)))
    | ~ l1_struct_0(sK6) ),
    inference(superposition,[],[f81,f128])).

fof(f81,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f572,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | sP5(X1,sK6,X0) ) ),
    inference(subsumption_resolution,[],[f571,f73])).

fof(f73,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f571,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | sP5(X1,sK6,X0)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f570,f74])).

fof(f74,plain,(
    v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f570,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | sP5(X1,sK6,X0)
      | ~ v3_orders_2(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f569,f75])).

fof(f75,plain,(
    v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f569,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | sP5(X1,sK6,X0)
      | ~ v4_orders_2(sK6)
      | ~ v3_orders_2(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f568,f76])).

fof(f76,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f568,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | sP5(X1,sK6,X0)
      | ~ v5_orders_2(sK6)
      | ~ v4_orders_2(sK6)
      | ~ v3_orders_2(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f565,f77])).

fof(f565,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | sP5(X1,sK6,X0)
      | ~ l1_orders_2(sK6)
      | ~ v5_orders_2(sK6)
      | ~ v4_orders_2(sK6)
      | ~ v3_orders_2(sK6)
      | v2_struct_0(sK6) ) ),
    inference(superposition,[],[f117,f128])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sP5(X0,X1,X2)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( sP5(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f37,f47,f46,f45])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( sP4(X2,X1,X0)
    <=> ? [X3] :
          ( sP3(X3,X1,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> sP4(X2,X1,X0) )
      | ~ sP5(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f694,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_orders_2(sK6,k2_struct_0(sK6)))
      | sP4(k2_struct_0(sK6),sK6,X3)
      | ~ sP5(X3,sK6,k2_struct_0(sK6)) ) ),
    inference(superposition,[],[f107,f674])).

fof(f674,plain,(
    k2_orders_2(sK6,k2_struct_0(sK6)) = a_2_1_orders_2(sK6,k2_struct_0(sK6)) ),
    inference(resolution,[],[f671,f145])).

fof(f671,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | k2_orders_2(sK6,X0) = a_2_1_orders_2(sK6,X0) ) ),
    inference(subsumption_resolution,[],[f670,f73])).

fof(f670,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | k2_orders_2(sK6,X0) = a_2_1_orders_2(sK6,X0)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f669,f74])).

fof(f669,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | k2_orders_2(sK6,X0) = a_2_1_orders_2(sK6,X0)
      | ~ v3_orders_2(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f668,f75])).

fof(f668,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | k2_orders_2(sK6,X0) = a_2_1_orders_2(sK6,X0)
      | ~ v4_orders_2(sK6)
      | ~ v3_orders_2(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f667,f76])).

fof(f667,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | k2_orders_2(sK6,X0) = a_2_1_orders_2(sK6,X0)
      | ~ v5_orders_2(sK6)
      | ~ v4_orders_2(sK6)
      | ~ v3_orders_2(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f664,f77])).

fof(f664,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | k2_orders_2(sK6,X0) = a_2_1_orders_2(sK6,X0)
      | ~ l1_orders_2(sK6)
      | ~ v5_orders_2(sK6)
      | ~ v4_orders_2(sK6)
      | ~ v3_orders_2(sK6)
      | v2_struct_0(sK6) ) ),
    inference(superposition,[],[f89,f128])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
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
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | sP4(X2,X1,X0)
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ~ sP4(X2,X1,X0) )
        & ( sP4(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f1003,plain,
    ( sP3(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),sK6,k2_struct_0(sK6))
    | ~ sP4(k2_struct_0(sK6),sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6)))) ),
    inference(superposition,[],[f111,f722])).

fof(f722,plain,(
    sK7(k2_orders_2(sK6,k2_struct_0(sK6))) = sK9(k2_struct_0(sK6),sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6)))) ),
    inference(resolution,[],[f718,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | sK9(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ! [X3] :
            ( ~ sP3(X3,X1,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( sP3(sK9(X0,X1,X2),X1,X0)
          & sK9(X0,X1,X2) = X2
          & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f66,f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( sP3(X4,X1,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( sP3(sK9(X0,X1,X2),X1,X0)
        & sK9(X0,X1,X2) = X2
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ! [X3] :
            ( ~ sP3(X3,X1,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( sP3(X4,X1,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ( sP4(X2,X1,X0)
        | ! [X3] :
            ( ~ sP3(X3,X1,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( sP3(X3,X1,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP4(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( sP3(sK9(X0,X1,X2),X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f958,plain,(
    ! [X1] :
      ( ~ r2_orders_2(sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6))),X1)
      | ~ m1_subset_1(X1,k2_struct_0(sK6))
      | sP0(X1,sK7(k2_orders_2(sK6,k2_struct_0(sK6))),sK6) ) ),
    inference(resolution,[],[f939,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_orders_2(X0,X1,X2)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_orders_2(X0,X1,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r2_orders_2(X0,X1,X2)
      <=> sP0(X2,X1,X0) )
      | ~ sP1(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f939,plain,(
    ! [X0] :
      ( sP1(sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6))),X0)
      | ~ m1_subset_1(X0,k2_struct_0(sK6)) ) ),
    inference(resolution,[],[f937,f372])).

fof(f372,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k2_struct_0(sK6))
      | sP1(sK6,X1,X0)
      | ~ m1_subset_1(X0,k2_struct_0(sK6)) ) ),
    inference(subsumption_resolution,[],[f370,f77])).

fof(f370,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK6))
      | sP1(sK6,X1,X0)
      | ~ m1_subset_1(X1,k2_struct_0(sK6))
      | ~ l1_orders_2(sK6) ) ),
    inference(superposition,[],[f88,f128])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f24,f41,f40])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f937,plain,(
    m1_subset_1(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),k2_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f934,f78])).

fof(f934,plain,
    ( m1_subset_1(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),k2_struct_0(sK6))
    | k1_xboole_0 = k2_orders_2(sK6,k2_struct_0(sK6)) ),
    inference(resolution,[],[f900,f92])).

fof(f900,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_orders_2(sK6,k2_struct_0(sK6)))
      | m1_subset_1(X3,k2_struct_0(sK6)) ) ),
    inference(resolution,[],[f855,f145])).

fof(f855,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK6)))
      | m1_subset_1(X5,k2_struct_0(sK6))
      | ~ r2_hidden(X5,k2_orders_2(sK6,X4)) ) ),
    inference(resolution,[],[f835,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f835,plain,(
    ! [X0] :
      ( m1_subset_1(k2_orders_2(sK6,X0),k1_zfmisc_1(k2_struct_0(sK6)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) ) ),
    inference(subsumption_resolution,[],[f834,f73])).

fof(f834,plain,(
    ! [X0] :
      ( m1_subset_1(k2_orders_2(sK6,X0),k1_zfmisc_1(k2_struct_0(sK6)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f833,f74])).

fof(f833,plain,(
    ! [X0] :
      ( m1_subset_1(k2_orders_2(sK6,X0),k1_zfmisc_1(k2_struct_0(sK6)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | ~ v3_orders_2(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f832,f75])).

fof(f832,plain,(
    ! [X0] :
      ( m1_subset_1(k2_orders_2(sK6,X0),k1_zfmisc_1(k2_struct_0(sK6)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | ~ v4_orders_2(sK6)
      | ~ v3_orders_2(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f831,f76])).

fof(f831,plain,(
    ! [X0] :
      ( m1_subset_1(k2_orders_2(sK6,X0),k1_zfmisc_1(k2_struct_0(sK6)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | ~ v5_orders_2(sK6)
      | ~ v4_orders_2(sK6)
      | ~ v3_orders_2(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f827,f77])).

fof(f827,plain,(
    ! [X0] :
      ( m1_subset_1(k2_orders_2(sK6,X0),k1_zfmisc_1(k2_struct_0(sK6)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | ~ l1_orders_2(sK6)
      | ~ v5_orders_2(sK6)
      | ~ v4_orders_2(sK6)
      | ~ v3_orders_2(sK6)
      | v2_struct_0(sK6) ) ),
    inference(superposition,[],[f103,f128])).

fof(f103,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

fof(f2134,plain,
    ( r2_hidden(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),k2_struct_0(sK6))
    | ~ spl11_33 ),
    inference(resolution,[],[f940,f1388])).

fof(f1388,plain,
    ( ! [X2] :
        ( ~ sP4(k1_xboole_0,sK6,X2)
        | r2_hidden(X2,k2_struct_0(sK6)) )
    | ~ spl11_33 ),
    inference(backward_demodulation,[],[f689,f1379])).

fof(f1379,plain,
    ( k2_struct_0(sK6) = k2_orders_2(sK6,k1_xboole_0)
    | ~ spl11_33 ),
    inference(avatar_component_clause,[],[f1377])).

fof(f1377,plain,
    ( spl11_33
  <=> k2_struct_0(sK6) = k2_orders_2(sK6,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).

fof(f689,plain,(
    ! [X2] :
      ( r2_hidden(X2,k2_orders_2(sK6,k1_xboole_0))
      | ~ sP4(k1_xboole_0,sK6,X2) ) ),
    inference(subsumption_resolution,[],[f685,f574])).

fof(f574,plain,(
    ! [X2] : sP5(X2,sK6,k1_xboole_0) ),
    inference(resolution,[],[f572,f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f685,plain,(
    ! [X2] :
      ( r2_hidden(X2,k2_orders_2(sK6,k1_xboole_0))
      | ~ sP4(k1_xboole_0,sK6,X2)
      | ~ sP5(X2,sK6,k1_xboole_0) ) ),
    inference(superposition,[],[f108,f673])).

fof(f673,plain,(
    k2_orders_2(sK6,k1_xboole_0) = a_2_1_orders_2(sK6,k1_xboole_0) ),
    inference(resolution,[],[f671,f79])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ sP4(X2,X1,X0)
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f940,plain,(
    sP4(k1_xboole_0,sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6)))) ),
    inference(resolution,[],[f937,f214])).

fof(f214,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK6))
      | sP4(k1_xboole_0,sK6,X0) ) ),
    inference(superposition,[],[f205,f128])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP4(k1_xboole_0,X0,X1) ) ),
    inference(resolution,[],[f124,f169])).

fof(f169,plain,(
    ! [X0,X1] : sP3(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f115,f126])).

fof(f126,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f94,f122])).

fof(f122,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f94,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X2),X2)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f124,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | sP4(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2)
      | ~ sP3(X3,X1,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1384,plain,(
    spl11_32 ),
    inference(avatar_contradiction_clause,[],[f1383])).

fof(f1383,plain,
    ( $false
    | spl11_32 ),
    inference(subsumption_resolution,[],[f1381,f79])).

fof(f1381,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK6)))
    | spl11_32 ),
    inference(resolution,[],[f1375,f835])).

fof(f1375,plain,
    ( ~ m1_subset_1(k2_orders_2(sK6,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK6)))
    | spl11_32 ),
    inference(avatar_component_clause,[],[f1373])).

fof(f1373,plain,
    ( spl11_32
  <=> m1_subset_1(k2_orders_2(sK6,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f1380,plain,
    ( ~ spl11_32
    | spl11_33 ),
    inference(avatar_split_clause,[],[f1368,f1377,f1373])).

fof(f1368,plain,
    ( k2_struct_0(sK6) = k2_orders_2(sK6,k1_xboole_0)
    | ~ m1_subset_1(k2_orders_2(sK6,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK6))) ),
    inference(duplicate_literal_removal,[],[f1364])).

fof(f1364,plain,
    ( k2_struct_0(sK6) = k2_orders_2(sK6,k1_xboole_0)
    | ~ m1_subset_1(k2_orders_2(sK6,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK6)))
    | k2_struct_0(sK6) = k2_orders_2(sK6,k1_xboole_0)
    | ~ m1_subset_1(k2_orders_2(sK6,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK6))) ),
    inference(resolution,[],[f703,f217])).

fof(f217,plain,(
    ! [X1] :
      ( sP4(k1_xboole_0,sK6,sK8(k2_struct_0(sK6),X1))
      | k2_struct_0(sK6) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK6))) ) ),
    inference(resolution,[],[f214,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK8(X0,X1),X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK8(X0,X1),X1)
        & m1_subset_1(sK8(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f33,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & m1_subset_1(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(f703,plain,(
    ! [X2] :
      ( ~ sP4(k1_xboole_0,sK6,sK8(X2,k2_orders_2(sK6,k1_xboole_0)))
      | k2_orders_2(sK6,k1_xboole_0) = X2
      | ~ m1_subset_1(k2_orders_2(sK6,k1_xboole_0),k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f689,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:46:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (29556)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (29548)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (29554)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (29560)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.50  % (29545)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (29547)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (29565)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (29568)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.50  % (29555)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (29557)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (29546)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (29552)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (29551)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (29543)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (29562)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (29544)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (29550)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (29564)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (29567)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (29549)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (29558)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (29561)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (29563)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (29559)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (29566)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.55  % (29553)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.76/0.62  % (29552)Refutation not found, incomplete strategy% (29552)------------------------------
% 1.76/0.62  % (29552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.63  % (29552)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.63  
% 1.76/0.63  % (29552)Memory used [KB]: 6140
% 1.76/0.63  % (29552)Time elapsed: 0.208 s
% 1.76/0.63  % (29552)------------------------------
% 1.76/0.63  % (29552)------------------------------
% 2.19/0.64  % (29568)Refutation found. Thanks to Tanya!
% 2.19/0.64  % SZS status Theorem for theBenchmark
% 2.19/0.65  % SZS output start Proof for theBenchmark
% 2.19/0.65  fof(f2340,plain,(
% 2.19/0.65    $false),
% 2.19/0.65    inference(avatar_sat_refutation,[],[f1380,f1384,f2338])).
% 2.19/0.65  fof(f2338,plain,(
% 2.19/0.65    ~spl11_33),
% 2.19/0.65    inference(avatar_contradiction_clause,[],[f2337])).
% 2.19/0.65  fof(f2337,plain,(
% 2.19/0.65    $false | ~spl11_33),
% 2.19/0.65    inference(subsumption_resolution,[],[f2134,f2328])).
% 2.19/0.65  fof(f2328,plain,(
% 2.19/0.65    ~r2_hidden(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),k2_struct_0(sK6))),
% 2.19/0.65    inference(resolution,[],[f1989,f119])).
% 2.19/0.65  fof(f119,plain,(
% 2.19/0.65    ( ! [X2,X1] : (~sP0(X1,X1,X2)) )),
% 2.19/0.65    inference(equality_resolution,[],[f86])).
% 2.19/0.65  fof(f86,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (X0 != X1 | ~sP0(X0,X1,X2)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f54])).
% 2.19/0.65  fof(f54,plain,(
% 2.19/0.65    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | X0 = X1 | ~r1_orders_2(X2,X1,X0)) & ((X0 != X1 & r1_orders_2(X2,X1,X0)) | ~sP0(X0,X1,X2)))),
% 2.19/0.65    inference(rectify,[],[f53])).
% 2.19/0.65  fof(f53,plain,(
% 2.19/0.65    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~sP0(X2,X1,X0)))),
% 2.19/0.65    inference(flattening,[],[f52])).
% 2.19/0.65  fof(f52,plain,(
% 2.19/0.65    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~sP0(X2,X1,X0)))),
% 2.19/0.65    inference(nnf_transformation,[],[f40])).
% 2.19/0.65  fof(f40,plain,(
% 2.19/0.65    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> (X1 != X2 & r1_orders_2(X0,X1,X2)))),
% 2.19/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.19/0.65  fof(f1989,plain,(
% 2.19/0.65    ( ! [X0] : (sP0(X0,sK7(k2_orders_2(sK6,k2_struct_0(sK6))),sK6) | ~r2_hidden(X0,k2_struct_0(sK6))) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f1985,f99])).
% 2.19/0.65  fof(f99,plain,(
% 2.19/0.65    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f29])).
% 2.19/0.65  fof(f29,plain,(
% 2.19/0.65    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.19/0.65    inference(ennf_transformation,[],[f6])).
% 2.19/0.65  fof(f6,axiom,(
% 2.19/0.65    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.19/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 2.19/0.65  fof(f1985,plain,(
% 2.19/0.65    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK6)) | sP0(X0,sK7(k2_orders_2(sK6,k2_struct_0(sK6))),sK6) | ~r2_hidden(X0,k2_struct_0(sK6))) )),
% 2.19/0.65    inference(resolution,[],[f958,f1022])).
% 2.19/0.65  fof(f1022,plain,(
% 2.19/0.65    ( ! [X0] : (r2_orders_2(sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6))),X0) | ~r2_hidden(X0,k2_struct_0(sK6))) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f1021,f99])).
% 2.19/0.65  fof(f1021,plain,(
% 2.19/0.65    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK6)) | ~r2_hidden(X0,k2_struct_0(sK6)) | r2_orders_2(sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6))),X0)) )),
% 2.19/0.65    inference(forward_demodulation,[],[f1019,f128])).
% 2.19/0.65  fof(f128,plain,(
% 2.19/0.65    k2_struct_0(sK6) = u1_struct_0(sK6)),
% 2.19/0.65    inference(resolution,[],[f80,f125])).
% 2.19/0.65  fof(f125,plain,(
% 2.19/0.65    l1_struct_0(sK6)),
% 2.19/0.65    inference(resolution,[],[f82,f77])).
% 2.19/0.65  fof(f77,plain,(
% 2.19/0.65    l1_orders_2(sK6)),
% 2.19/0.65    inference(cnf_transformation,[],[f50])).
% 2.19/0.65  fof(f50,plain,(
% 2.19/0.65    k1_xboole_0 != k2_orders_2(sK6,k2_struct_0(sK6)) & l1_orders_2(sK6) & v5_orders_2(sK6) & v4_orders_2(sK6) & v3_orders_2(sK6) & ~v2_struct_0(sK6)),
% 2.19/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f49])).
% 2.19/0.65  fof(f49,plain,(
% 2.19/0.65    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK6,k2_struct_0(sK6)) & l1_orders_2(sK6) & v5_orders_2(sK6) & v4_orders_2(sK6) & v3_orders_2(sK6) & ~v2_struct_0(sK6))),
% 2.19/0.65    introduced(choice_axiom,[])).
% 2.19/0.65  fof(f20,plain,(
% 2.19/0.65    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.19/0.65    inference(flattening,[],[f19])).
% 2.19/0.65  fof(f19,plain,(
% 2.19/0.65    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.19/0.65    inference(ennf_transformation,[],[f18])).
% 2.19/0.65  fof(f18,negated_conjecture,(
% 2.19/0.65    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 2.19/0.65    inference(negated_conjecture,[],[f17])).
% 2.19/0.65  fof(f17,conjecture,(
% 2.19/0.65    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 2.19/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).
% 2.19/0.65  fof(f82,plain,(
% 2.19/0.65    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f23])).
% 2.19/0.65  fof(f23,plain,(
% 2.19/0.65    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 2.19/0.65    inference(ennf_transformation,[],[f15])).
% 2.19/0.65  fof(f15,axiom,(
% 2.19/0.65    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 2.19/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 2.19/0.65  fof(f80,plain,(
% 2.19/0.65    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f21])).
% 2.19/0.65  fof(f21,plain,(
% 2.19/0.65    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.19/0.65    inference(ennf_transformation,[],[f10])).
% 2.19/0.65  fof(f10,axiom,(
% 2.19/0.65    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.19/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 2.19/0.65  fof(f1019,plain,(
% 2.19/0.65    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK6)) | ~m1_subset_1(X0,u1_struct_0(sK6)) | r2_orders_2(sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6))),X0)) )),
% 2.19/0.65    inference(resolution,[],[f1011,f113])).
% 2.19/0.65  fof(f113,plain,(
% 2.19/0.65    ( ! [X4,X2,X0,X1] : (~sP3(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r2_orders_2(X1,X0,X4)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f72])).
% 2.19/0.65  fof(f72,plain,(
% 2.19/0.65    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | (~r2_orders_2(X1,X0,sK10(X0,X1,X2)) & r2_hidden(sK10(X0,X1,X2),X2) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r2_orders_2(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 2.19/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f70,f71])).
% 2.19/0.65  fof(f71,plain,(
% 2.19/0.65    ! [X2,X1,X0] : (? [X3] : (~r2_orders_2(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r2_orders_2(X1,X0,sK10(X0,X1,X2)) & r2_hidden(sK10(X0,X1,X2),X2) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))))),
% 2.19/0.65    introduced(choice_axiom,[])).
% 2.19/0.65  fof(f70,plain,(
% 2.19/0.65    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : (~r2_orders_2(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r2_orders_2(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 2.19/0.65    inference(rectify,[],[f69])).
% 2.19/0.65  fof(f69,plain,(
% 2.19/0.65    ! [X3,X1,X2] : ((sP3(X3,X1,X2) | ? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1)))) & (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X3,X1,X2)))),
% 2.19/0.65    inference(nnf_transformation,[],[f45])).
% 2.19/0.65  fof(f45,plain,(
% 2.19/0.65    ! [X3,X1,X2] : (sP3(X3,X1,X2) <=> ! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))))),
% 2.19/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.19/0.65  fof(f1011,plain,(
% 2.19/0.65    sP3(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),sK6,k2_struct_0(sK6))),
% 2.19/0.65    inference(subsumption_resolution,[],[f1003,f718])).
% 2.19/0.65  fof(f718,plain,(
% 2.19/0.65    sP4(k2_struct_0(sK6),sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6))))),
% 2.19/0.65    inference(subsumption_resolution,[],[f715,f78])).
% 2.19/0.65  fof(f78,plain,(
% 2.19/0.65    k1_xboole_0 != k2_orders_2(sK6,k2_struct_0(sK6))),
% 2.19/0.65    inference(cnf_transformation,[],[f50])).
% 2.19/0.65  fof(f715,plain,(
% 2.19/0.65    sP4(k2_struct_0(sK6),sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6)))) | k1_xboole_0 = k2_orders_2(sK6,k2_struct_0(sK6))),
% 2.19/0.65    inference(resolution,[],[f698,f92])).
% 2.19/0.65  fof(f92,plain,(
% 2.19/0.65    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 2.19/0.65    inference(cnf_transformation,[],[f58])).
% 2.19/0.65  fof(f58,plain,(
% 2.19/0.65    ! [X0] : ((sP2(sK7(X0),X0) & r2_hidden(sK7(X0),X0)) | k1_xboole_0 = X0)),
% 2.19/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f57])).
% 2.19/0.65  fof(f57,plain,(
% 2.19/0.65    ! [X0] : (? [X1] : (sP2(X1,X0) & r2_hidden(X1,X0)) => (sP2(sK7(X0),X0) & r2_hidden(sK7(X0),X0)))),
% 2.19/0.65    introduced(choice_axiom,[])).
% 2.19/0.65  fof(f44,plain,(
% 2.19/0.65    ! [X0] : (? [X1] : (sP2(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.19/0.65    inference(definition_folding,[],[f27,f43])).
% 2.19/0.65  fof(f43,plain,(
% 2.19/0.65    ! [X1,X0] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP2(X1,X0))),
% 2.19/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.19/0.65  fof(f27,plain,(
% 2.19/0.65    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.19/0.65    inference(ennf_transformation,[],[f9])).
% 2.19/0.65  fof(f9,axiom,(
% 2.19/0.65    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.19/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 2.19/0.65  fof(f698,plain,(
% 2.19/0.65    ( ! [X3] : (~r2_hidden(X3,k2_orders_2(sK6,k2_struct_0(sK6))) | sP4(k2_struct_0(sK6),sK6,X3)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f694,f575])).
% 2.19/0.65  fof(f575,plain,(
% 2.19/0.65    ( ! [X3] : (sP5(X3,sK6,k2_struct_0(sK6))) )),
% 2.19/0.65    inference(resolution,[],[f572,f145])).
% 2.19/0.65  fof(f145,plain,(
% 2.19/0.65    m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(k2_struct_0(sK6)))),
% 2.19/0.65    inference(subsumption_resolution,[],[f144,f125])).
% 2.19/0.65  fof(f144,plain,(
% 2.19/0.65    m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(k2_struct_0(sK6))) | ~l1_struct_0(sK6)),
% 2.19/0.65    inference(superposition,[],[f81,f128])).
% 2.19/0.65  fof(f81,plain,(
% 2.19/0.65    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f22])).
% 2.19/0.65  fof(f22,plain,(
% 2.19/0.65    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 2.19/0.65    inference(ennf_transformation,[],[f11])).
% 2.19/0.65  fof(f11,axiom,(
% 2.19/0.65    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.19/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 2.19/0.65  fof(f572,plain,(
% 2.19/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | sP5(X1,sK6,X0)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f571,f73])).
% 2.19/0.65  fof(f73,plain,(
% 2.19/0.65    ~v2_struct_0(sK6)),
% 2.19/0.65    inference(cnf_transformation,[],[f50])).
% 2.19/0.65  fof(f571,plain,(
% 2.19/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | sP5(X1,sK6,X0) | v2_struct_0(sK6)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f570,f74])).
% 2.19/0.65  fof(f74,plain,(
% 2.19/0.65    v3_orders_2(sK6)),
% 2.19/0.65    inference(cnf_transformation,[],[f50])).
% 2.19/0.65  fof(f570,plain,(
% 2.19/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | sP5(X1,sK6,X0) | ~v3_orders_2(sK6) | v2_struct_0(sK6)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f569,f75])).
% 2.19/0.65  fof(f75,plain,(
% 2.19/0.65    v4_orders_2(sK6)),
% 2.19/0.65    inference(cnf_transformation,[],[f50])).
% 2.19/0.65  fof(f569,plain,(
% 2.19/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | sP5(X1,sK6,X0) | ~v4_orders_2(sK6) | ~v3_orders_2(sK6) | v2_struct_0(sK6)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f568,f76])).
% 2.19/0.65  fof(f76,plain,(
% 2.19/0.65    v5_orders_2(sK6)),
% 2.19/0.65    inference(cnf_transformation,[],[f50])).
% 2.19/0.65  fof(f568,plain,(
% 2.19/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | sP5(X1,sK6,X0) | ~v5_orders_2(sK6) | ~v4_orders_2(sK6) | ~v3_orders_2(sK6) | v2_struct_0(sK6)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f565,f77])).
% 2.19/0.65  fof(f565,plain,(
% 2.19/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | sP5(X1,sK6,X0) | ~l1_orders_2(sK6) | ~v5_orders_2(sK6) | ~v4_orders_2(sK6) | ~v3_orders_2(sK6) | v2_struct_0(sK6)) )),
% 2.19/0.65    inference(superposition,[],[f117,f128])).
% 2.19/0.65  fof(f117,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sP5(X0,X1,X2) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f48])).
% 2.19/0.65  fof(f48,plain,(
% 2.19/0.65    ! [X0,X1,X2] : (sP5(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.19/0.65    inference(definition_folding,[],[f37,f47,f46,f45])).
% 2.19/0.65  fof(f46,plain,(
% 2.19/0.65    ! [X2,X1,X0] : (sP4(X2,X1,X0) <=> ? [X3] : (sP3(X3,X1,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 2.19/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 2.19/0.65  fof(f47,plain,(
% 2.19/0.65    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> sP4(X2,X1,X0)) | ~sP5(X0,X1,X2))),
% 2.19/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 2.19/0.65  fof(f37,plain,(
% 2.19/0.65    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 2.19/0.65    inference(flattening,[],[f36])).
% 2.19/0.65  fof(f36,plain,(
% 2.19/0.65    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 2.19/0.65    inference(ennf_transformation,[],[f16])).
% 2.19/0.65  fof(f16,axiom,(
% 2.19/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 2.19/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 2.19/0.65  fof(f694,plain,(
% 2.19/0.65    ( ! [X3] : (~r2_hidden(X3,k2_orders_2(sK6,k2_struct_0(sK6))) | sP4(k2_struct_0(sK6),sK6,X3) | ~sP5(X3,sK6,k2_struct_0(sK6))) )),
% 2.19/0.65    inference(superposition,[],[f107,f674])).
% 2.19/0.65  fof(f674,plain,(
% 2.19/0.65    k2_orders_2(sK6,k2_struct_0(sK6)) = a_2_1_orders_2(sK6,k2_struct_0(sK6))),
% 2.19/0.65    inference(resolution,[],[f671,f145])).
% 2.19/0.65  fof(f671,plain,(
% 2.19/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | k2_orders_2(sK6,X0) = a_2_1_orders_2(sK6,X0)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f670,f73])).
% 2.19/0.65  fof(f670,plain,(
% 2.19/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | k2_orders_2(sK6,X0) = a_2_1_orders_2(sK6,X0) | v2_struct_0(sK6)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f669,f74])).
% 2.19/0.65  fof(f669,plain,(
% 2.19/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | k2_orders_2(sK6,X0) = a_2_1_orders_2(sK6,X0) | ~v3_orders_2(sK6) | v2_struct_0(sK6)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f668,f75])).
% 2.19/0.65  fof(f668,plain,(
% 2.19/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | k2_orders_2(sK6,X0) = a_2_1_orders_2(sK6,X0) | ~v4_orders_2(sK6) | ~v3_orders_2(sK6) | v2_struct_0(sK6)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f667,f76])).
% 2.19/0.65  fof(f667,plain,(
% 2.19/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | k2_orders_2(sK6,X0) = a_2_1_orders_2(sK6,X0) | ~v5_orders_2(sK6) | ~v4_orders_2(sK6) | ~v3_orders_2(sK6) | v2_struct_0(sK6)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f664,f77])).
% 2.19/0.65  fof(f664,plain,(
% 2.19/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | k2_orders_2(sK6,X0) = a_2_1_orders_2(sK6,X0) | ~l1_orders_2(sK6) | ~v5_orders_2(sK6) | ~v4_orders_2(sK6) | ~v3_orders_2(sK6) | v2_struct_0(sK6)) )),
% 2.19/0.65    inference(superposition,[],[f89,f128])).
% 2.19/0.65  fof(f89,plain,(
% 2.19/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f26])).
% 2.19/0.65  fof(f26,plain,(
% 2.19/0.65    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.65    inference(flattening,[],[f25])).
% 2.19/0.65  fof(f25,plain,(
% 2.19/0.65    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.19/0.65    inference(ennf_transformation,[],[f13])).
% 2.19/0.65  fof(f13,axiom,(
% 2.19/0.65    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 2.19/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).
% 2.19/0.65  fof(f107,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | sP4(X2,X1,X0) | ~sP5(X0,X1,X2)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f64])).
% 2.19/0.65  fof(f64,plain,(
% 2.19/0.65    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP4(X2,X1,X0)) & (sP4(X2,X1,X0) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~sP5(X0,X1,X2))),
% 2.19/0.65    inference(nnf_transformation,[],[f47])).
% 2.19/0.65  fof(f1003,plain,(
% 2.19/0.65    sP3(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),sK6,k2_struct_0(sK6)) | ~sP4(k2_struct_0(sK6),sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6))))),
% 2.19/0.65    inference(superposition,[],[f111,f722])).
% 2.19/0.65  fof(f722,plain,(
% 2.19/0.65    sK7(k2_orders_2(sK6,k2_struct_0(sK6))) = sK9(k2_struct_0(sK6),sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6))))),
% 2.19/0.65    inference(resolution,[],[f718,f110])).
% 2.19/0.65  fof(f110,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | sK9(X0,X1,X2) = X2) )),
% 2.19/0.65    inference(cnf_transformation,[],[f68])).
% 2.19/0.65  fof(f68,plain,(
% 2.19/0.65    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ! [X3] : (~sP3(X3,X1,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((sP3(sK9(X0,X1,X2),X1,X0) & sK9(X0,X1,X2) = X2 & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))) | ~sP4(X0,X1,X2)))),
% 2.19/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f66,f67])).
% 2.19/0.65  fof(f67,plain,(
% 2.19/0.65    ! [X2,X1,X0] : (? [X4] : (sP3(X4,X1,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (sP3(sK9(X0,X1,X2),X1,X0) & sK9(X0,X1,X2) = X2 & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))))),
% 2.19/0.65    introduced(choice_axiom,[])).
% 2.19/0.65  fof(f66,plain,(
% 2.19/0.65    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ! [X3] : (~sP3(X3,X1,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (sP3(X4,X1,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP4(X0,X1,X2)))),
% 2.19/0.65    inference(rectify,[],[f65])).
% 2.19/0.65  fof(f65,plain,(
% 2.19/0.65    ! [X2,X1,X0] : ((sP4(X2,X1,X0) | ! [X3] : (~sP3(X3,X1,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (sP3(X3,X1,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP4(X2,X1,X0)))),
% 2.19/0.65    inference(nnf_transformation,[],[f46])).
% 2.19/0.65  fof(f111,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (sP3(sK9(X0,X1,X2),X1,X0) | ~sP4(X0,X1,X2)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f68])).
% 2.19/0.65  fof(f958,plain,(
% 2.19/0.65    ( ! [X1] : (~r2_orders_2(sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6))),X1) | ~m1_subset_1(X1,k2_struct_0(sK6)) | sP0(X1,sK7(k2_orders_2(sK6,k2_struct_0(sK6))),sK6)) )),
% 2.19/0.65    inference(resolution,[],[f939,f83])).
% 2.19/0.65  fof(f83,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_orders_2(X0,X1,X2) | sP0(X2,X1,X0)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f51])).
% 2.19/0.65  fof(f51,plain,(
% 2.19/0.65    ! [X0,X1,X2] : (((r2_orders_2(X0,X1,X2) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_orders_2(X0,X1,X2))) | ~sP1(X0,X1,X2))),
% 2.19/0.65    inference(nnf_transformation,[],[f41])).
% 2.19/0.65  fof(f41,plain,(
% 2.19/0.65    ! [X0,X1,X2] : ((r2_orders_2(X0,X1,X2) <=> sP0(X2,X1,X0)) | ~sP1(X0,X1,X2))),
% 2.19/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.19/0.65  fof(f939,plain,(
% 2.19/0.65    ( ! [X0] : (sP1(sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6))),X0) | ~m1_subset_1(X0,k2_struct_0(sK6))) )),
% 2.19/0.65    inference(resolution,[],[f937,f372])).
% 2.19/0.65  fof(f372,plain,(
% 2.19/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k2_struct_0(sK6)) | sP1(sK6,X1,X0) | ~m1_subset_1(X0,k2_struct_0(sK6))) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f370,f77])).
% 2.19/0.65  fof(f370,plain,(
% 2.19/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK6)) | sP1(sK6,X1,X0) | ~m1_subset_1(X1,k2_struct_0(sK6)) | ~l1_orders_2(sK6)) )),
% 2.19/0.65    inference(superposition,[],[f88,f128])).
% 2.19/0.65  fof(f88,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f42])).
% 2.19/0.65  fof(f42,plain,(
% 2.19/0.65    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.19/0.65    inference(definition_folding,[],[f24,f41,f40])).
% 2.19/0.65  fof(f24,plain,(
% 2.19/0.65    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.19/0.65    inference(ennf_transformation,[],[f12])).
% 2.19/0.65  fof(f12,axiom,(
% 2.19/0.65    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 2.19/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 2.19/0.65  fof(f937,plain,(
% 2.19/0.65    m1_subset_1(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),k2_struct_0(sK6))),
% 2.19/0.65    inference(subsumption_resolution,[],[f934,f78])).
% 2.19/0.65  fof(f934,plain,(
% 2.19/0.65    m1_subset_1(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),k2_struct_0(sK6)) | k1_xboole_0 = k2_orders_2(sK6,k2_struct_0(sK6))),
% 2.19/0.65    inference(resolution,[],[f900,f92])).
% 2.19/0.65  fof(f900,plain,(
% 2.19/0.65    ( ! [X3] : (~r2_hidden(X3,k2_orders_2(sK6,k2_struct_0(sK6))) | m1_subset_1(X3,k2_struct_0(sK6))) )),
% 2.19/0.65    inference(resolution,[],[f855,f145])).
% 2.19/0.65  fof(f855,plain,(
% 2.19/0.65    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK6))) | m1_subset_1(X5,k2_struct_0(sK6)) | ~r2_hidden(X5,k2_orders_2(sK6,X4))) )),
% 2.19/0.65    inference(resolution,[],[f835,f118])).
% 2.19/0.65  fof(f118,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f39])).
% 2.19/0.65  fof(f39,plain,(
% 2.19/0.65    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.19/0.65    inference(flattening,[],[f38])).
% 2.19/0.65  fof(f38,plain,(
% 2.19/0.65    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.19/0.65    inference(ennf_transformation,[],[f8])).
% 2.19/0.65  fof(f8,axiom,(
% 2.19/0.65    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.19/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 2.19/0.65  fof(f835,plain,(
% 2.19/0.65    ( ! [X0] : (m1_subset_1(k2_orders_2(sK6,X0),k1_zfmisc_1(k2_struct_0(sK6))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f834,f73])).
% 2.19/0.65  fof(f834,plain,(
% 2.19/0.65    ( ! [X0] : (m1_subset_1(k2_orders_2(sK6,X0),k1_zfmisc_1(k2_struct_0(sK6))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | v2_struct_0(sK6)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f833,f74])).
% 2.19/0.65  fof(f833,plain,(
% 2.19/0.65    ( ! [X0] : (m1_subset_1(k2_orders_2(sK6,X0),k1_zfmisc_1(k2_struct_0(sK6))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | ~v3_orders_2(sK6) | v2_struct_0(sK6)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f832,f75])).
% 2.19/0.65  fof(f832,plain,(
% 2.19/0.65    ( ! [X0] : (m1_subset_1(k2_orders_2(sK6,X0),k1_zfmisc_1(k2_struct_0(sK6))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | ~v4_orders_2(sK6) | ~v3_orders_2(sK6) | v2_struct_0(sK6)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f831,f76])).
% 2.19/0.65  fof(f831,plain,(
% 2.19/0.65    ( ! [X0] : (m1_subset_1(k2_orders_2(sK6,X0),k1_zfmisc_1(k2_struct_0(sK6))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | ~v5_orders_2(sK6) | ~v4_orders_2(sK6) | ~v3_orders_2(sK6) | v2_struct_0(sK6)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f827,f77])).
% 2.19/0.65  fof(f827,plain,(
% 2.19/0.65    ( ! [X0] : (m1_subset_1(k2_orders_2(sK6,X0),k1_zfmisc_1(k2_struct_0(sK6))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | ~l1_orders_2(sK6) | ~v5_orders_2(sK6) | ~v4_orders_2(sK6) | ~v3_orders_2(sK6) | v2_struct_0(sK6)) )),
% 2.19/0.65    inference(superposition,[],[f103,f128])).
% 2.19/0.65  fof(f103,plain,(
% 2.19/0.65    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f35])).
% 2.19/0.65  fof(f35,plain,(
% 2.19/0.65    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.19/0.65    inference(flattening,[],[f34])).
% 2.19/0.65  fof(f34,plain,(
% 2.19/0.65    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.19/0.65    inference(ennf_transformation,[],[f14])).
% 2.19/0.65  fof(f14,axiom,(
% 2.19/0.65    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.19/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).
% 2.19/0.65  fof(f2134,plain,(
% 2.19/0.65    r2_hidden(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),k2_struct_0(sK6)) | ~spl11_33),
% 2.19/0.65    inference(resolution,[],[f940,f1388])).
% 2.19/0.65  fof(f1388,plain,(
% 2.19/0.65    ( ! [X2] : (~sP4(k1_xboole_0,sK6,X2) | r2_hidden(X2,k2_struct_0(sK6))) ) | ~spl11_33),
% 2.19/0.65    inference(backward_demodulation,[],[f689,f1379])).
% 2.19/0.65  fof(f1379,plain,(
% 2.19/0.65    k2_struct_0(sK6) = k2_orders_2(sK6,k1_xboole_0) | ~spl11_33),
% 2.19/0.65    inference(avatar_component_clause,[],[f1377])).
% 2.19/0.65  fof(f1377,plain,(
% 2.19/0.65    spl11_33 <=> k2_struct_0(sK6) = k2_orders_2(sK6,k1_xboole_0)),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).
% 2.19/0.65  fof(f689,plain,(
% 2.19/0.65    ( ! [X2] : (r2_hidden(X2,k2_orders_2(sK6,k1_xboole_0)) | ~sP4(k1_xboole_0,sK6,X2)) )),
% 2.19/0.65    inference(subsumption_resolution,[],[f685,f574])).
% 2.19/0.65  fof(f574,plain,(
% 2.19/0.65    ( ! [X2] : (sP5(X2,sK6,k1_xboole_0)) )),
% 2.19/0.65    inference(resolution,[],[f572,f79])).
% 2.19/0.65  fof(f79,plain,(
% 2.19/0.65    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.19/0.65    inference(cnf_transformation,[],[f5])).
% 2.19/0.65  fof(f5,axiom,(
% 2.19/0.65    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.19/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.19/0.65  fof(f685,plain,(
% 2.19/0.65    ( ! [X2] : (r2_hidden(X2,k2_orders_2(sK6,k1_xboole_0)) | ~sP4(k1_xboole_0,sK6,X2) | ~sP5(X2,sK6,k1_xboole_0)) )),
% 2.19/0.65    inference(superposition,[],[f108,f673])).
% 2.19/0.65  fof(f673,plain,(
% 2.19/0.65    k2_orders_2(sK6,k1_xboole_0) = a_2_1_orders_2(sK6,k1_xboole_0)),
% 2.19/0.65    inference(resolution,[],[f671,f79])).
% 2.19/0.65  fof(f108,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP4(X2,X1,X0) | ~sP5(X0,X1,X2)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f64])).
% 2.19/0.65  fof(f940,plain,(
% 2.19/0.65    sP4(k1_xboole_0,sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6))))),
% 2.19/0.65    inference(resolution,[],[f937,f214])).
% 2.19/0.65  fof(f214,plain,(
% 2.19/0.65    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK6)) | sP4(k1_xboole_0,sK6,X0)) )),
% 2.19/0.65    inference(superposition,[],[f205,f128])).
% 2.19/0.65  fof(f205,plain,(
% 2.19/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP4(k1_xboole_0,X0,X1)) )),
% 2.19/0.65    inference(resolution,[],[f124,f169])).
% 2.19/0.65  fof(f169,plain,(
% 2.19/0.65    ( ! [X0,X1] : (sP3(X0,X1,k1_xboole_0)) )),
% 2.19/0.65    inference(resolution,[],[f115,f126])).
% 2.19/0.65  fof(f126,plain,(
% 2.19/0.65    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.19/0.65    inference(superposition,[],[f94,f122])).
% 2.19/0.65  fof(f122,plain,(
% 2.19/0.65    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.19/0.65    inference(equality_resolution,[],[f106])).
% 2.19/0.65  fof(f106,plain,(
% 2.19/0.65    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.19/0.65    inference(cnf_transformation,[],[f63])).
% 2.19/0.65  fof(f63,plain,(
% 2.19/0.65    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.19/0.65    inference(flattening,[],[f62])).
% 2.19/0.65  fof(f62,plain,(
% 2.19/0.65    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.19/0.65    inference(nnf_transformation,[],[f1])).
% 2.19/0.65  fof(f1,axiom,(
% 2.19/0.65    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.19/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.19/0.65  fof(f94,plain,(
% 2.19/0.65    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.19/0.65    inference(cnf_transformation,[],[f2])).
% 2.19/0.65  fof(f2,axiom,(
% 2.19/0.65    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.19/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 2.19/0.65  fof(f115,plain,(
% 2.19/0.65    ( ! [X2,X0,X1] : (r2_hidden(sK10(X0,X1,X2),X2) | sP3(X0,X1,X2)) )),
% 2.19/0.65    inference(cnf_transformation,[],[f72])).
% 2.19/0.65  fof(f124,plain,(
% 2.19/0.65    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | sP4(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 2.19/0.65    inference(equality_resolution,[],[f112])).
% 2.19/0.65  fof(f112,plain,(
% 2.19/0.65    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2) | ~sP3(X3,X1,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 2.19/0.65    inference(cnf_transformation,[],[f68])).
% 2.19/0.65  fof(f1384,plain,(
% 2.19/0.65    spl11_32),
% 2.19/0.65    inference(avatar_contradiction_clause,[],[f1383])).
% 2.19/0.65  fof(f1383,plain,(
% 2.19/0.65    $false | spl11_32),
% 2.19/0.65    inference(subsumption_resolution,[],[f1381,f79])).
% 2.19/0.65  fof(f1381,plain,(
% 2.19/0.65    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK6))) | spl11_32),
% 2.19/0.65    inference(resolution,[],[f1375,f835])).
% 2.19/0.65  fof(f1375,plain,(
% 2.19/0.65    ~m1_subset_1(k2_orders_2(sK6,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK6))) | spl11_32),
% 2.19/0.65    inference(avatar_component_clause,[],[f1373])).
% 2.19/0.65  fof(f1373,plain,(
% 2.19/0.65    spl11_32 <=> m1_subset_1(k2_orders_2(sK6,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK6)))),
% 2.19/0.65    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).
% 2.19/0.65  fof(f1380,plain,(
% 2.19/0.65    ~spl11_32 | spl11_33),
% 2.19/0.65    inference(avatar_split_clause,[],[f1368,f1377,f1373])).
% 2.19/0.65  fof(f1368,plain,(
% 2.19/0.65    k2_struct_0(sK6) = k2_orders_2(sK6,k1_xboole_0) | ~m1_subset_1(k2_orders_2(sK6,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK6)))),
% 2.19/0.65    inference(duplicate_literal_removal,[],[f1364])).
% 2.19/0.65  fof(f1364,plain,(
% 2.19/0.65    k2_struct_0(sK6) = k2_orders_2(sK6,k1_xboole_0) | ~m1_subset_1(k2_orders_2(sK6,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK6))) | k2_struct_0(sK6) = k2_orders_2(sK6,k1_xboole_0) | ~m1_subset_1(k2_orders_2(sK6,k1_xboole_0),k1_zfmisc_1(k2_struct_0(sK6)))),
% 2.19/0.65    inference(resolution,[],[f703,f217])).
% 2.19/0.65  fof(f217,plain,(
% 2.19/0.65    ( ! [X1] : (sP4(k1_xboole_0,sK6,sK8(k2_struct_0(sK6),X1)) | k2_struct_0(sK6) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK6)))) )),
% 2.19/0.65    inference(resolution,[],[f214,f101])).
% 2.19/0.65  fof(f101,plain,(
% 2.19/0.65    ( ! [X0,X1] : (m1_subset_1(sK8(X0,X1),X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.19/0.65    inference(cnf_transformation,[],[f61])).
% 2.19/0.65  fof(f61,plain,(
% 2.19/0.65    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK8(X0,X1),X1) & m1_subset_1(sK8(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.19/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f33,f60])).
% 2.19/0.65  fof(f60,plain,(
% 2.19/0.65    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & m1_subset_1(sK8(X0,X1),X0)))),
% 2.19/0.65    introduced(choice_axiom,[])).
% 2.19/0.65  fof(f33,plain,(
% 2.19/0.65    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.19/0.65    inference(flattening,[],[f32])).
% 2.19/0.65  fof(f32,plain,(
% 2.19/0.65    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.19/0.65    inference(ennf_transformation,[],[f4])).
% 2.19/0.65  fof(f4,axiom,(
% 2.19/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 2.19/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).
% 2.19/0.65  fof(f703,plain,(
% 2.19/0.65    ( ! [X2] : (~sP4(k1_xboole_0,sK6,sK8(X2,k2_orders_2(sK6,k1_xboole_0))) | k2_orders_2(sK6,k1_xboole_0) = X2 | ~m1_subset_1(k2_orders_2(sK6,k1_xboole_0),k1_zfmisc_1(X2))) )),
% 2.19/0.65    inference(resolution,[],[f689,f102])).
% 2.19/0.65  fof(f102,plain,(
% 2.19/0.65    ( ! [X0,X1] : (~r2_hidden(sK8(X0,X1),X1) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.19/0.65    inference(cnf_transformation,[],[f61])).
% 2.19/0.65  % SZS output end Proof for theBenchmark
% 2.19/0.65  % (29568)------------------------------
% 2.19/0.65  % (29568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.65  % (29568)Termination reason: Refutation
% 2.19/0.65  
% 2.19/0.65  % (29568)Memory used [KB]: 12281
% 2.19/0.65  % (29568)Time elapsed: 0.233 s
% 2.19/0.65  % (29568)------------------------------
% 2.19/0.65  % (29568)------------------------------
% 2.33/0.65  % (29542)Success in time 0.292 s
%------------------------------------------------------------------------------
