%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:58 EST 2020

% Result     : Theorem 2.32s
% Output     : Refutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 294 expanded)
%              Number of leaves         :   39 ( 113 expanded)
%              Depth                    :   12
%              Number of atoms          :  643 ( 945 expanded)
%              Number of equality atoms :   48 (  81 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f212,f241,f250,f386,f398,f400,f401,f438,f439,f558,f1020,f2064,f2107,f2138,f2201,f2207])).

fof(f2207,plain,
    ( spl11_20
    | ~ spl11_6
    | ~ spl11_17 ),
    inference(avatar_split_clause,[],[f1305,f265,f152,f278])).

fof(f278,plain,
    ( spl11_20
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f152,plain,
    ( spl11_6
  <=> r2_hidden(sK5(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)),k1_funct_2(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f265,plain,
    ( spl11_17
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f1305,plain,
    ( v1_xboole_0(sK2)
    | ~ spl11_6
    | ~ spl11_17 ),
    inference(resolution,[],[f980,f154])).

fof(f154,plain,
    ( r2_hidden(sK5(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)),k1_funct_2(sK2,sK3))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f152])).

fof(f980,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k1_funct_2(X5,sK3))
        | v1_xboole_0(X5) )
    | ~ spl11_17 ),
    inference(resolution,[],[f402,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f402,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_funct_2(X0,sK3))
        | v1_xboole_0(X0) )
    | ~ spl11_17 ),
    inference(resolution,[],[f267,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

fof(f267,plain,
    ( v1_xboole_0(sK3)
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f265])).

fof(f2201,plain,
    ( spl11_1
    | ~ spl11_9
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f2200,f193,f189,f124])).

fof(f124,plain,
    ( spl11_1
  <=> r2_hidden(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_funct_2(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f189,plain,
    ( spl11_9
  <=> v1_funct_1(k3_partfun1(k1_xboole_0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f193,plain,
    ( spl11_10
  <=> m1_subset_1(k3_partfun1(k1_xboole_0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f2200,plain,
    ( r2_hidden(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_funct_2(sK2,sK3))
    | ~ spl11_9
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f526,f611])).

fof(f611,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
        | r2_hidden(X0,k1_funct_2(sK2,sK3)) )
    | ~ spl11_9
    | ~ spl11_10 ),
    inference(resolution,[],[f284,f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f284,plain,
    ( r1_tarski(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3))
    | ~ spl11_9
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f257,f190])).

fof(f190,plain,
    ( v1_funct_1(k3_partfun1(k1_xboole_0,sK2,sK3))
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f189])).

fof(f257,plain,
    ( r1_tarski(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3))
    | ~ v1_funct_1(k3_partfun1(k1_xboole_0,sK2,sK3))
    | ~ spl11_10 ),
    inference(resolution,[],[f194,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_funct_2)).

fof(f194,plain,
    ( m1_subset_1(k3_partfun1(k1_xboole_0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f193])).

fof(f526,plain,
    ( r2_hidden(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | r2_hidden(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_funct_2(sK2,sK3)) ),
    inference(resolution,[],[f157,f116])).

fof(f116,plain,(
    ! [X0] : sQ10_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f108])).

fof(f108,plain,(
    ! [X1,X0] :
      ( sQ10_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ10_eqProxy])])).

fof(f157,plain,(
    ! [X0] :
      ( ~ sQ10_eqProxy(k1_funct_2(sK2,sK3),X0)
      | r2_hidden(sK5(X0,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
      | r2_hidden(sK5(X0,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),X0) ) ),
    inference(resolution,[],[f122,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( sQ10_eqProxy(X0,X1)
      | r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f74,f108])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1),X1)
          | ~ r2_hidden(sK5(X0,X1),X0) )
        & ( r2_hidden(sK5(X0,X1),X1)
          | r2_hidden(sK5(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f122,plain,(
    ! [X0] :
      ( ~ sQ10_eqProxy(X0,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
      | ~ sQ10_eqProxy(k1_funct_2(sK2,sK3),X0) ) ),
    inference(resolution,[],[f110,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ10_eqProxy(X0,X1)
      | ~ sQ10_eqProxy(X1,X2)
      | sQ10_eqProxy(X0,X2) ) ),
    inference(equality_proxy_axiom,[],[f108])).

fof(f110,plain,(
    ~ sQ10_eqProxy(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) ),
    inference(equality_proxy_replacement,[],[f62,f108])).

fof(f62,plain,(
    k1_funct_2(sK2,sK3) != k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    k1_funct_2(sK2,sK3) != k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f41])).

fof(f41,plain,
    ( ? [X0,X1] : k1_funct_2(X0,X1) != k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))
   => k1_funct_2(sK2,sK3) != k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] : k1_funct_2(X0,X1) != k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_funct_2)).

fof(f2138,plain,
    ( spl11_7
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f387,f124,f170])).

fof(f170,plain,
    ( spl11_7
  <=> v1_funct_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f387,plain,
    ( v1_funct_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))
    | ~ spl11_1 ),
    inference(resolution,[],[f126,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f126,plain,
    ( r2_hidden(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_funct_2(sK2,sK3))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f2107,plain,
    ( ~ spl11_7
    | spl11_31
    | ~ spl11_30 ),
    inference(avatar_split_clause,[],[f647,f351,f355,f170])).

fof(f355,plain,
    ( spl11_31
  <=> ! [X3,X2] : r1_partfun1(k3_partfun1(k1_xboole_0,X2,X3),sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f351,plain,
    ( spl11_30
  <=> v1_relat_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f647,plain,
    ( ! [X4,X5] :
        ( r1_partfun1(k3_partfun1(k1_xboole_0,X4,X5),sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))
        | ~ v1_funct_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) )
    | ~ spl11_30 ),
    inference(resolution,[],[f352,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_partfun1)).

fof(f352,plain,
    ( v1_relat_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f351])).

fof(f2064,plain,
    ( ~ spl11_3
    | ~ spl11_31
    | ~ spl11_39 ),
    inference(avatar_contradiction_clause,[],[f2063])).

fof(f2063,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_31
    | ~ spl11_39 ),
    inference(subsumption_resolution,[],[f2055,f140])).

fof(f140,plain,
    ( sP1(sK3,sK2,k3_partfun1(k1_xboole_0,sK2,sK3))
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl11_3
  <=> sP1(sK3,sK2,k3_partfun1(k1_xboole_0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f2055,plain,
    ( ~ sP1(sK3,sK2,k3_partfun1(k1_xboole_0,sK2,sK3))
    | ~ spl11_31
    | ~ spl11_39 ),
    inference(resolution,[],[f1223,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0,k5_partfun1(X1,X0,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_partfun1(X1,X0,X2) != X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X0,X2) = X3
            | ~ sP0(X2,X1,X0,X3) )
          & ( sP0(X2,X1,X0,X3)
            | k5_partfun1(X1,X0,X2) != X3 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP0(X2,X0,X1,X3) )
          & ( sP0(X2,X0,X1,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP0(X2,X0,X1,X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1223,plain,
    ( ! [X0,X1] : ~ sP0(k3_partfun1(k1_xboole_0,X0,X1),sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | ~ spl11_31
    | ~ spl11_39 ),
    inference(resolution,[],[f557,f356])).

fof(f356,plain,
    ( ! [X2,X3] : r1_partfun1(k3_partfun1(k1_xboole_0,X2,X3),sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f355])).

fof(f557,plain,
    ( ! [X7] :
        ( ~ r1_partfun1(X7,sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))
        | ~ sP0(X7,sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) )
    | ~ spl11_39 ),
    inference(avatar_component_clause,[],[f556])).

fof(f556,plain,
    ( spl11_39
  <=> ! [X7] :
        ( ~ r1_partfun1(X7,sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))
        | ~ sP0(X7,sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_39])])).

fof(f1020,plain,
    ( spl11_6
    | ~ spl11_9
    | ~ spl11_10 ),
    inference(avatar_contradiction_clause,[],[f1019])).

fof(f1019,plain,
    ( $false
    | spl11_6
    | ~ spl11_9
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f1018,f153])).

fof(f153,plain,
    ( ~ r2_hidden(sK5(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)),k1_funct_2(sK2,sK3))
    | spl11_6 ),
    inference(avatar_component_clause,[],[f152])).

fof(f1018,plain,
    ( r2_hidden(sK5(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)),k1_funct_2(sK2,sK3))
    | spl11_6
    | ~ spl11_9
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f1017,f121])).

fof(f121,plain,(
    ~ sQ10_eqProxy(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)) ),
    inference(resolution,[],[f110,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ sQ10_eqProxy(X0,X1)
      | sQ10_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f108])).

fof(f1017,plain,
    ( sQ10_eqProxy(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3))
    | r2_hidden(sK5(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)),k1_funct_2(sK2,sK3))
    | spl11_6
    | ~ spl11_9
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f1012,f284])).

fof(f1012,plain,
    ( ~ r1_tarski(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3))
    | sQ10_eqProxy(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3))
    | r2_hidden(sK5(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)),k1_funct_2(sK2,sK3))
    | spl11_6 ),
    inference(resolution,[],[f903,f112])).

fof(f903,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK5(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)),X3)
        | ~ r1_tarski(X3,k1_funct_2(sK2,sK3)) )
    | spl11_6 ),
    inference(resolution,[],[f153,f76])).

fof(f558,plain,
    ( spl11_39
    | ~ spl11_34
    | spl11_2
    | ~ spl11_7
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f554,f203,f170,f128,f383,f556])).

fof(f383,plain,
    ( spl11_34
  <=> v1_partfun1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f128,plain,
    ( spl11_2
  <=> r2_hidden(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f203,plain,
    ( spl11_12
  <=> m1_subset_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f554,plain,
    ( ! [X7] :
        ( ~ v1_partfun1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2)
        | ~ r1_partfun1(X7,sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))
        | ~ sP0(X7,sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) )
    | spl11_2
    | ~ spl11_7
    | ~ spl11_12 ),
    inference(resolution,[],[f408,f205])).

fof(f205,plain,
    ( m1_subset_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f203])).

fof(f408,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_partfun1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),X1)
        | ~ r1_partfun1(X0,sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))
        | ~ sP0(X0,X1,X2,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) )
    | spl11_2
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f406,f171])).

fof(f171,plain,
    ( v1_funct_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f170])).

fof(f406,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_partfun1(X0,sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))
        | ~ v1_partfun1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),X1)
        | ~ m1_subset_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))
        | ~ sP0(X0,X1,X2,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) )
    | spl11_2 ),
    inference(resolution,[],[f129,f107])).

fof(f107,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | sK7(X0,X1,X2,X3) != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
          & ( ( r1_partfun1(X0,sK8(X0,X1,X2,X3))
              & v1_partfun1(sK8(X0,X1,X2,X3),X1)
              & sK7(X0,X1,X2,X3) = sK8(X0,X1,X2,X3)
              & m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(sK8(X0,X1,X2,X3)) )
            | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ( r1_partfun1(X0,sK9(X0,X1,X2,X7))
                & v1_partfun1(sK9(X0,X1,X2,X7),X1)
                & sK9(X0,X1,X2,X7) = X7
                & m1_subset_1(sK9(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(sK9(X0,X1,X2,X7)) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f57,f60,f59,f58])).

fof(f58,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | X4 != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( r1_partfun1(X0,X6)
                & v1_partfun1(X6,X1)
                & X4 = X6
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(X6) )
            | r2_hidden(X4,X3) ) )
     => ( ( ! [X5] :
              ( ~ r1_partfun1(X0,X5)
              | ~ v1_partfun1(X5,X1)
              | sK7(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X0,X6)
              & v1_partfun1(X6,X1)
              & sK7(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X6) )
          | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X0,X6)
          & v1_partfun1(X6,X1)
          & sK7(X0,X1,X2,X3) = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X0,sK8(X0,X1,X2,X3))
        & v1_partfun1(sK8(X0,X1,X2,X3),X1)
        & sK7(X0,X1,X2,X3) = sK8(X0,X1,X2,X3)
        & m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK8(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X0,X9)
          & v1_partfun1(X9,X1)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X0,sK9(X0,X1,X2,X7))
        & v1_partfun1(sK9(X0,X1,X2,X7),X1)
        & sK9(X0,X1,X2,X7) = X7
        & m1_subset_1(sK9(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK9(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X0,X5)
                  | ~ v1_partfun1(X5,X1)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X6] :
                  ( r1_partfun1(X0,X6)
                  & v1_partfun1(X6,X1)
                  & X4 = X6
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X6) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ? [X9] :
                  ( r1_partfun1(X0,X9)
                  & v1_partfun1(X9,X1)
                  & X7 = X9
                  & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X9) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1,X3] :
      ( ( sP0(X2,X0,X1,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) ) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X0,X1,X3) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1,X3] :
      ( sP0(X2,X0,X1,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( r1_partfun1(X2,X5)
              & v1_partfun1(X5,X0)
              & X4 = X5
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X5) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f129,plain,
    ( ~ r2_hidden(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | spl11_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f439,plain,
    ( spl11_30
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f431,f203,f351])).

fof(f431,plain,
    ( v1_relat_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))
    | ~ spl11_12 ),
    inference(resolution,[],[f205,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f438,plain,
    ( ~ spl11_20
    | spl11_34
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f430,f203,f383,f278])).

fof(f430,plain,
    ( v1_partfun1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2)
    | ~ v1_xboole_0(sK2)
    | ~ spl11_12 ),
    inference(resolution,[],[f205,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f401,plain,
    ( spl11_11
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f388,f124,f198])).

fof(f198,plain,
    ( spl11_11
  <=> v1_funct_2(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f388,plain,
    ( v1_funct_2(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2,sK3)
    | ~ spl11_1 ),
    inference(resolution,[],[f126,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f400,plain,
    ( ~ spl11_2
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f399,f124,f128])).

fof(f399,plain,
    ( ~ r2_hidden(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f390,f110])).

fof(f390,plain,
    ( sQ10_eqProxy(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | ~ r2_hidden(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | ~ spl11_1 ),
    inference(resolution,[],[f126,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( sQ10_eqProxy(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1)
      | ~ r2_hidden(sK5(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f75,f108])).

fof(f75,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK5(X0,X1),X1)
      | ~ r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f398,plain,
    ( spl11_12
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f389,f124,f203])).

fof(f389,plain,
    ( m1_subset_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl11_1 ),
    inference(resolution,[],[f126,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f386,plain,
    ( spl11_17
    | ~ spl11_12
    | spl11_34
    | ~ spl11_7
    | ~ spl11_11 ),
    inference(avatar_split_clause,[],[f381,f198,f170,f383,f203,f265])).

fof(f381,plain,
    ( v1_partfun1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2)
    | ~ m1_subset_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_xboole_0(sK3)
    | ~ spl11_7
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f380,f171])).

fof(f380,plain,
    ( v1_partfun1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2)
    | ~ v1_funct_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))
    | ~ m1_subset_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_xboole_0(sK3)
    | ~ spl11_11 ),
    inference(resolution,[],[f200,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f200,plain,
    ( v1_funct_2(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2,sK3)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f198])).

fof(f250,plain,(
    spl11_10 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | spl11_10 ),
    inference(subsumption_resolution,[],[f248,f64])).

fof(f64,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

fof(f248,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl11_10 ),
    inference(subsumption_resolution,[],[f245,f66])).

fof(f66,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f245,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl11_10 ),
    inference(resolution,[],[f195,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(k3_partfun1(X0,X1,X2)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(k3_partfun1(X0,X1,X2)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(k3_partfun1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_partfun1)).

fof(f195,plain,
    ( ~ m1_subset_1(k3_partfun1(k1_xboole_0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | spl11_10 ),
    inference(avatar_component_clause,[],[f193])).

fof(f241,plain,
    ( ~ spl11_10
    | spl11_3
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f240,f189,f139,f193])).

fof(f240,plain,
    ( ~ m1_subset_1(k3_partfun1(k1_xboole_0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | spl11_3
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f239,f190])).

fof(f239,plain,
    ( ~ m1_subset_1(k3_partfun1(k1_xboole_0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(k3_partfun1(k1_xboole_0,sK2,sK3))
    | spl11_3 ),
    inference(resolution,[],[f141,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f37,f39,f38])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

fof(f141,plain,
    ( ~ sP1(sK3,sK2,k3_partfun1(k1_xboole_0,sK2,sK3))
    | spl11_3 ),
    inference(avatar_component_clause,[],[f139])).

fof(f212,plain,(
    spl11_9 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl11_9 ),
    inference(subsumption_resolution,[],[f210,f64])).

fof(f210,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl11_9 ),
    inference(subsumption_resolution,[],[f207,f66])).

fof(f207,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl11_9 ),
    inference(resolution,[],[f191,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_partfun1(X0,X1,X2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f191,plain,
    ( ~ v1_funct_1(k3_partfun1(k1_xboole_0,sK2,sK3))
    | spl11_9 ),
    inference(avatar_component_clause,[],[f189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:45 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.53  % (21947)dis+1002_5_av=off:cond=on:gs=on:lma=on:nm=2:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (21945)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
% 0.20/0.53  % (21947)Refutation not found, incomplete strategy% (21947)------------------------------
% 0.20/0.53  % (21947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (21947)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (21947)Memory used [KB]: 6140
% 0.20/0.53  % (21947)Time elapsed: 0.008 s
% 0.20/0.53  % (21947)------------------------------
% 0.20/0.53  % (21947)------------------------------
% 0.20/0.54  % (21939)dis+1004_1_aac=none:acc=on:afp=40000:afq=1.2:anc=none:cond=on:fde=unused:gs=on:gsem=off:irw=on:nm=32:nwc=2:sd=1:ss=axioms:sos=theory:sp=reverse_arity:urr=ec_only_17 on theBenchmark
% 0.20/0.54  % (21939)Refutation not found, incomplete strategy% (21939)------------------------------
% 0.20/0.54  % (21939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (21939)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (21939)Memory used [KB]: 10618
% 0.20/0.54  % (21939)Time elapsed: 0.029 s
% 0.20/0.54  % (21939)------------------------------
% 0.20/0.54  % (21939)------------------------------
% 0.20/0.54  % (21961)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_4 on theBenchmark
% 0.20/0.54  % (21961)Refutation not found, incomplete strategy% (21961)------------------------------
% 0.20/0.54  % (21961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (21961)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (21961)Memory used [KB]: 6268
% 0.20/0.54  % (21961)Time elapsed: 0.114 s
% 0.20/0.54  % (21961)------------------------------
% 0.20/0.54  % (21961)------------------------------
% 0.20/0.54  % (21953)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
% 0.20/0.54  % (21953)Refutation not found, incomplete strategy% (21953)------------------------------
% 0.20/0.54  % (21953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (21941)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11 on theBenchmark
% 0.20/0.55  % (21953)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (21953)Memory used [KB]: 10618
% 0.20/0.55  % (21953)Time elapsed: 0.126 s
% 0.20/0.55  % (21953)------------------------------
% 0.20/0.55  % (21953)------------------------------
% 0.20/0.56  % (21942)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_6 on theBenchmark
% 0.20/0.57  % (21934)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.57  % (21942)Refutation not found, incomplete strategy% (21942)------------------------------
% 0.20/0.57  % (21942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (21941)Refutation not found, incomplete strategy% (21941)------------------------------
% 0.20/0.57  % (21941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (21941)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (21941)Memory used [KB]: 6140
% 0.20/0.57  % (21941)Time elapsed: 0.153 s
% 0.20/0.57  % (21941)------------------------------
% 0.20/0.57  % (21941)------------------------------
% 0.20/0.57  % (21942)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (21942)Memory used [KB]: 6268
% 0.20/0.57  % (21942)Time elapsed: 0.142 s
% 0.20/0.57  % (21942)------------------------------
% 0.20/0.57  % (21942)------------------------------
% 0.20/0.58  % (21957)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.58  % (21935)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41 on theBenchmark
% 0.20/0.58  % (21957)Refutation not found, incomplete strategy% (21957)------------------------------
% 0.20/0.58  % (21957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (21957)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (21957)Memory used [KB]: 10618
% 0.20/0.58  % (21957)Time elapsed: 0.164 s
% 0.20/0.58  % (21957)------------------------------
% 0.20/0.58  % (21957)------------------------------
% 0.20/0.58  % (21938)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8 on theBenchmark
% 0.20/0.58  % (21937)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
% 0.20/0.58  % (21935)Refutation not found, incomplete strategy% (21935)------------------------------
% 0.20/0.58  % (21935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (21935)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (21935)Memory used [KB]: 6140
% 0.20/0.58  % (21935)Time elapsed: 0.148 s
% 0.20/0.58  % (21935)------------------------------
% 0.20/0.58  % (21935)------------------------------
% 0.20/0.58  % (21938)Refutation not found, incomplete strategy% (21938)------------------------------
% 0.20/0.58  % (21938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (21938)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (21938)Memory used [KB]: 1663
% 0.20/0.58  % (21938)Time elapsed: 0.146 s
% 0.20/0.58  % (21938)------------------------------
% 0.20/0.58  % (21938)------------------------------
% 0.20/0.59  % (21949)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_23 on theBenchmark
% 0.20/0.59  % (21950)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
% 0.20/0.59  % (21958)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.59  % (21958)Refutation not found, incomplete strategy% (21958)------------------------------
% 0.20/0.59  % (21958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (21958)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (21958)Memory used [KB]: 6140
% 0.20/0.59  % (21958)Time elapsed: 0.183 s
% 0.20/0.59  % (21958)------------------------------
% 0.20/0.59  % (21958)------------------------------
% 0.20/0.61  % (21944)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
% 1.66/0.61  % (21936)lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8 on theBenchmark
% 1.66/0.61  % (21936)Refutation not found, incomplete strategy% (21936)------------------------------
% 1.66/0.61  % (21936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (21946)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
% 1.66/0.61  % (21951)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
% 1.66/0.61  % (21951)Refutation not found, incomplete strategy% (21951)------------------------------
% 1.66/0.61  % (21951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (21951)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.61  
% 1.66/0.61  % (21951)Memory used [KB]: 10746
% 1.66/0.61  % (21951)Time elapsed: 0.178 s
% 1.66/0.61  % (21951)------------------------------
% 1.66/0.61  % (21951)------------------------------
% 1.66/0.61  % (21936)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.61  
% 1.66/0.61  % (21936)Memory used [KB]: 6140
% 1.66/0.61  % (21936)Time elapsed: 0.176 s
% 1.66/0.61  % (21936)------------------------------
% 1.66/0.61  % (21936)------------------------------
% 1.66/0.61  % (21940)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_6 on theBenchmark
% 1.66/0.62  % (21950)Refutation not found, incomplete strategy% (21950)------------------------------
% 1.66/0.62  % (21950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.62  % (21950)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.62  
% 1.66/0.62  % (21950)Memory used [KB]: 6268
% 1.66/0.62  % (21950)Time elapsed: 0.189 s
% 1.66/0.62  % (21950)------------------------------
% 1.66/0.62  % (21950)------------------------------
% 1.66/0.62  % (21952)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
% 1.66/0.62  % (21962)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_48 on theBenchmark
% 1.66/0.62  % (21959)dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4 on theBenchmark
% 1.66/0.62  % (21955)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_157 on theBenchmark
% 1.66/0.62  % (21943)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_3 on theBenchmark
% 1.66/0.62  % (21954)ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=input_only:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_70 on theBenchmark
% 1.66/0.62  % (21960)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
% 1.66/0.62  % (21943)Refutation not found, incomplete strategy% (21943)------------------------------
% 1.66/0.62  % (21943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.62  % (21943)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.62  
% 1.66/0.62  % (21943)Memory used [KB]: 6268
% 1.66/0.62  % (21943)Time elapsed: 0.189 s
% 1.66/0.62  % (21943)------------------------------
% 1.66/0.62  % (21943)------------------------------
% 1.66/0.62  % (21954)Refutation not found, incomplete strategy% (21954)------------------------------
% 1.66/0.62  % (21954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.63  % (21954)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.63  
% 2.07/0.63  % (21954)Memory used [KB]: 6140
% 2.07/0.63  % (21954)Time elapsed: 0.187 s
% 2.07/0.63  % (21954)------------------------------
% 2.07/0.63  % (21954)------------------------------
% 2.07/0.63  % (21933)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
% 2.07/0.63  % (21959)Refutation not found, incomplete strategy% (21959)------------------------------
% 2.07/0.63  % (21959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.63  % (21959)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.63  
% 2.07/0.63  % (21959)Memory used [KB]: 10618
% 2.07/0.63  % (21959)Time elapsed: 0.200 s
% 2.07/0.63  % (21959)------------------------------
% 2.07/0.63  % (21959)------------------------------
% 2.07/0.63  % (21933)Refutation not found, incomplete strategy% (21933)------------------------------
% 2.07/0.63  % (21933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.63  % (21933)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.63  
% 2.07/0.63  % (21933)Memory used [KB]: 6140
% 2.07/0.63  % (21933)Time elapsed: 0.199 s
% 2.07/0.63  % (21933)------------------------------
% 2.07/0.63  % (21933)------------------------------
% 2.07/0.63  % (21952)Refutation not found, incomplete strategy% (21952)------------------------------
% 2.07/0.63  % (21952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.63  % (21952)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.63  
% 2.07/0.63  % (21952)Memory used [KB]: 1663
% 2.07/0.63  % (21952)Time elapsed: 0.197 s
% 2.07/0.63  % (21952)------------------------------
% 2.07/0.63  % (21952)------------------------------
% 2.07/0.63  % (21962)Refutation not found, incomplete strategy% (21962)------------------------------
% 2.07/0.63  % (21962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.64  % (21948)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_7 on theBenchmark
% 2.07/0.64  % (21962)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.64  
% 2.07/0.64  % (21962)Memory used [KB]: 10618
% 2.07/0.64  % (21962)Time elapsed: 0.198 s
% 2.07/0.64  % (21962)------------------------------
% 2.07/0.64  % (21962)------------------------------
% 2.07/0.64  % (21960)Refutation not found, incomplete strategy% (21960)------------------------------
% 2.07/0.64  % (21960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.64  % (21960)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.64  
% 2.07/0.64  % (21960)Memory used [KB]: 6140
% 2.07/0.64  % (21960)Time elapsed: 0.209 s
% 2.07/0.64  % (21960)------------------------------
% 2.07/0.64  % (21960)------------------------------
% 2.07/0.65  % (21987)dis+1011_8:1_aac=none:acc=on:afp=1000:afq=1.4:amm=off:anc=all:bs=unit_only:bce=on:ccuc=small_ones:fsr=off:fde=unused:gsp=input_only:gs=on:gsem=off:lma=on:nm=16:nwc=2.5:sd=4:ss=axioms:st=1.5:sos=all:uhcvi=on_65 on theBenchmark
% 2.07/0.66  % (21988)ott+1_5:1_acc=on:add=off:afr=on:afp=100000:afq=1.1:amm=sco:anc=none:lcm=predicate:nm=16:nwc=1.1:sd=1:ss=axioms:st=3.0:sos=on:sac=on:updr=off_18 on theBenchmark
% 2.07/0.67  % (21988)Refutation not found, incomplete strategy% (21988)------------------------------
% 2.07/0.67  % (21988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.67  % (21988)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.67  
% 2.07/0.67  % (21988)Memory used [KB]: 6140
% 2.07/0.67  % (21988)Time elapsed: 0.007 s
% 2.07/0.67  % (21988)------------------------------
% 2.07/0.67  % (21988)------------------------------
% 2.07/0.67  % (21956)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 2.32/0.72  % (21989)lrs+1002_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:cond=fast:fde=none:gs=on:gsem=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence_8 on theBenchmark
% 2.32/0.72  % (21989)Refutation not found, incomplete strategy% (21989)------------------------------
% 2.32/0.72  % (21989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.32/0.72  % (21989)Termination reason: Refutation not found, incomplete strategy
% 2.32/0.72  
% 2.32/0.72  % (21989)Memory used [KB]: 10618
% 2.32/0.72  % (21989)Time elapsed: 0.123 s
% 2.32/0.72  % (21989)------------------------------
% 2.32/0.72  % (21989)------------------------------
% 2.32/0.72  % (21945)Refutation not found, incomplete strategy% (21945)------------------------------
% 2.32/0.72  % (21945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.32/0.72  % (21945)Termination reason: Refutation not found, incomplete strategy
% 2.32/0.72  
% 2.32/0.72  % (21945)Memory used [KB]: 6268
% 2.32/0.72  % (21945)Time elapsed: 0.276 s
% 2.32/0.72  % (21945)------------------------------
% 2.32/0.72  % (21945)------------------------------
% 2.32/0.72  % (21990)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_4 on theBenchmark
% 2.32/0.72  % (21990)Refutation not found, incomplete strategy% (21990)------------------------------
% 2.32/0.72  % (21990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.32/0.72  % (21990)Termination reason: Refutation not found, incomplete strategy
% 2.32/0.72  
% 2.32/0.72  % (21990)Memory used [KB]: 10746
% 2.32/0.72  % (21990)Time elapsed: 0.113 s
% 2.32/0.72  % (21990)------------------------------
% 2.32/0.72  % (21990)------------------------------
% 2.32/0.74  % (21991)lrs+1002_3:1_av=off:bd=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:lma=on:lwlo=on:nm=4:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_134 on theBenchmark
% 2.32/0.74  % (21991)Refutation not found, incomplete strategy% (21991)------------------------------
% 2.32/0.74  % (21991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.32/0.74  % (21991)Termination reason: Refutation not found, incomplete strategy
% 2.32/0.74  
% 2.32/0.74  % (21991)Memory used [KB]: 1663
% 2.32/0.74  % (21991)Time elapsed: 0.132 s
% 2.32/0.74  % (21991)------------------------------
% 2.32/0.74  % (21991)------------------------------
% 2.32/0.74  % (21937)Refutation found. Thanks to Tanya!
% 2.32/0.74  % SZS status Theorem for theBenchmark
% 2.32/0.74  % SZS output start Proof for theBenchmark
% 2.32/0.74  fof(f2215,plain,(
% 2.32/0.74    $false),
% 2.32/0.74    inference(avatar_sat_refutation,[],[f212,f241,f250,f386,f398,f400,f401,f438,f439,f558,f1020,f2064,f2107,f2138,f2201,f2207])).
% 2.32/0.74  fof(f2207,plain,(
% 2.32/0.74    spl11_20 | ~spl11_6 | ~spl11_17),
% 2.32/0.74    inference(avatar_split_clause,[],[f1305,f265,f152,f278])).
% 2.32/0.74  fof(f278,plain,(
% 2.32/0.74    spl11_20 <=> v1_xboole_0(sK2)),
% 2.32/0.74    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).
% 2.32/0.74  fof(f152,plain,(
% 2.32/0.74    spl11_6 <=> r2_hidden(sK5(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)),k1_funct_2(sK2,sK3))),
% 2.32/0.74    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 2.32/0.74  fof(f265,plain,(
% 2.32/0.74    spl11_17 <=> v1_xboole_0(sK3)),
% 2.32/0.74    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).
% 2.32/0.74  fof(f1305,plain,(
% 2.32/0.74    v1_xboole_0(sK2) | (~spl11_6 | ~spl11_17)),
% 2.32/0.74    inference(resolution,[],[f980,f154])).
% 2.32/0.74  fof(f154,plain,(
% 2.32/0.74    r2_hidden(sK5(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)),k1_funct_2(sK2,sK3)) | ~spl11_6),
% 2.32/0.74    inference(avatar_component_clause,[],[f152])).
% 2.32/0.74  fof(f980,plain,(
% 2.32/0.74    ( ! [X6,X5] : (~r2_hidden(X6,k1_funct_2(X5,sK3)) | v1_xboole_0(X5)) ) | ~spl11_17),
% 2.32/0.74    inference(resolution,[],[f402,f68])).
% 2.32/0.74  fof(f68,plain,(
% 2.32/0.74    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.32/0.74    inference(cnf_transformation,[],[f46])).
% 2.32/0.74  fof(f46,plain,(
% 2.32/0.74    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.32/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).
% 2.32/0.74  fof(f45,plain,(
% 2.32/0.74    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 2.32/0.74    introduced(choice_axiom,[])).
% 2.32/0.74  fof(f44,plain,(
% 2.32/0.74    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.32/0.74    inference(rectify,[],[f43])).
% 2.32/0.74  fof(f43,plain,(
% 2.32/0.74    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.32/0.74    inference(nnf_transformation,[],[f1])).
% 2.32/0.74  fof(f1,axiom,(
% 2.32/0.74    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.32/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.32/0.74  fof(f402,plain,(
% 2.32/0.74    ( ! [X0] : (v1_xboole_0(k1_funct_2(X0,sK3)) | v1_xboole_0(X0)) ) | ~spl11_17),
% 2.32/0.74    inference(resolution,[],[f267,f73])).
% 2.32/0.74  fof(f73,plain,(
% 2.32/0.74    ( ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.32/0.74    inference(cnf_transformation,[],[f23])).
% 2.32/0.74  fof(f23,plain,(
% 2.32/0.74    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.32/0.74    inference(flattening,[],[f22])).
% 2.32/0.74  fof(f22,plain,(
% 2.32/0.74    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.32/0.74    inference(ennf_transformation,[],[f11])).
% 2.32/0.74  fof(f11,axiom,(
% 2.32/0.74    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 2.32/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).
% 2.32/0.74  fof(f267,plain,(
% 2.32/0.74    v1_xboole_0(sK3) | ~spl11_17),
% 2.32/0.74    inference(avatar_component_clause,[],[f265])).
% 2.32/0.74  fof(f2201,plain,(
% 2.32/0.74    spl11_1 | ~spl11_9 | ~spl11_10),
% 2.32/0.74    inference(avatar_split_clause,[],[f2200,f193,f189,f124])).
% 2.32/0.74  fof(f124,plain,(
% 2.32/0.74    spl11_1 <=> r2_hidden(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_funct_2(sK2,sK3))),
% 2.32/0.74    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 2.32/0.74  fof(f189,plain,(
% 2.32/0.74    spl11_9 <=> v1_funct_1(k3_partfun1(k1_xboole_0,sK2,sK3))),
% 2.32/0.74    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 2.32/0.74  fof(f193,plain,(
% 2.32/0.74    spl11_10 <=> m1_subset_1(k3_partfun1(k1_xboole_0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.32/0.74    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 2.32/0.74  fof(f2200,plain,(
% 2.32/0.74    r2_hidden(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_funct_2(sK2,sK3)) | (~spl11_9 | ~spl11_10)),
% 2.32/0.74    inference(subsumption_resolution,[],[f526,f611])).
% 2.32/0.74  fof(f611,plain,(
% 2.32/0.74    ( ! [X0] : (~r2_hidden(X0,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) | r2_hidden(X0,k1_funct_2(sK2,sK3))) ) | (~spl11_9 | ~spl11_10)),
% 2.32/0.74    inference(resolution,[],[f284,f76])).
% 2.32/0.74  fof(f76,plain,(
% 2.32/0.74    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.32/0.74    inference(cnf_transformation,[],[f53])).
% 2.32/0.74  fof(f53,plain,(
% 2.32/0.74    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.32/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f51,f52])).
% 2.32/0.74  fof(f52,plain,(
% 2.32/0.74    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 2.32/0.74    introduced(choice_axiom,[])).
% 2.32/0.74  fof(f51,plain,(
% 2.32/0.74    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.32/0.74    inference(rectify,[],[f50])).
% 2.32/0.74  fof(f50,plain,(
% 2.32/0.74    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.32/0.74    inference(nnf_transformation,[],[f25])).
% 2.32/0.74  fof(f25,plain,(
% 2.32/0.74    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.32/0.74    inference(ennf_transformation,[],[f3])).
% 2.32/0.74  fof(f3,axiom,(
% 2.32/0.74    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.32/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.32/0.74  fof(f284,plain,(
% 2.32/0.74    r1_tarski(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)) | (~spl11_9 | ~spl11_10)),
% 2.32/0.74    inference(subsumption_resolution,[],[f257,f190])).
% 2.32/0.74  fof(f190,plain,(
% 2.32/0.74    v1_funct_1(k3_partfun1(k1_xboole_0,sK2,sK3)) | ~spl11_9),
% 2.32/0.74    inference(avatar_component_clause,[],[f189])).
% 2.32/0.74  fof(f257,plain,(
% 2.32/0.74    r1_tarski(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)) | ~v1_funct_1(k3_partfun1(k1_xboole_0,sK2,sK3)) | ~spl11_10),
% 2.32/0.74    inference(resolution,[],[f194,f86])).
% 2.32/0.74  fof(f86,plain,(
% 2.32/0.74    ( ! [X2,X0,X1] : (r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.32/0.74    inference(cnf_transformation,[],[f33])).
% 2.32/0.74  fof(f33,plain,(
% 2.32/0.74    ! [X0,X1,X2] : (r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.32/0.74    inference(flattening,[],[f32])).
% 2.32/0.74  fof(f32,plain,(
% 2.32/0.74    ! [X0,X1,X2] : (r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.32/0.74    inference(ennf_transformation,[],[f15])).
% 2.32/0.74  fof(f15,axiom,(
% 2.32/0.74    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)))),
% 2.32/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_funct_2)).
% 2.32/0.74  fof(f194,plain,(
% 2.32/0.74    m1_subset_1(k3_partfun1(k1_xboole_0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~spl11_10),
% 2.32/0.74    inference(avatar_component_clause,[],[f193])).
% 2.32/0.74  fof(f526,plain,(
% 2.32/0.74    r2_hidden(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) | r2_hidden(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_funct_2(sK2,sK3))),
% 2.32/0.74    inference(resolution,[],[f157,f116])).
% 2.32/0.74  fof(f116,plain,(
% 2.32/0.74    ( ! [X0] : (sQ10_eqProxy(X0,X0)) )),
% 2.32/0.74    inference(equality_proxy_axiom,[],[f108])).
% 2.32/0.74  fof(f108,plain,(
% 2.32/0.74    ! [X1,X0] : (sQ10_eqProxy(X0,X1) <=> X0 = X1)),
% 2.32/0.74    introduced(equality_proxy_definition,[new_symbols(naming,[sQ10_eqProxy])])).
% 2.32/0.74  fof(f157,plain,(
% 2.32/0.74    ( ! [X0] : (~sQ10_eqProxy(k1_funct_2(sK2,sK3),X0) | r2_hidden(sK5(X0,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) | r2_hidden(sK5(X0,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),X0)) )),
% 2.32/0.74    inference(resolution,[],[f122,f112])).
% 2.32/0.74  fof(f112,plain,(
% 2.32/0.74    ( ! [X0,X1] : (sQ10_eqProxy(X0,X1) | r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 2.32/0.74    inference(equality_proxy_replacement,[],[f74,f108])).
% 2.32/0.74  fof(f74,plain,(
% 2.32/0.74    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 2.32/0.74    inference(cnf_transformation,[],[f49])).
% 2.32/0.74  fof(f49,plain,(
% 2.32/0.74    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0)) & (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0))))),
% 2.32/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f47,f48])).
% 2.32/0.74  fof(f48,plain,(
% 2.32/0.74    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0)) & (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0))))),
% 2.32/0.74    introduced(choice_axiom,[])).
% 2.32/0.74  fof(f47,plain,(
% 2.32/0.74    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.32/0.74    inference(nnf_transformation,[],[f24])).
% 2.32/0.74  fof(f24,plain,(
% 2.32/0.74    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.32/0.74    inference(ennf_transformation,[],[f4])).
% 2.32/0.74  fof(f4,axiom,(
% 2.32/0.74    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.32/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 2.32/0.74  fof(f122,plain,(
% 2.32/0.74    ( ! [X0] : (~sQ10_eqProxy(X0,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) | ~sQ10_eqProxy(k1_funct_2(sK2,sK3),X0)) )),
% 2.32/0.74    inference(resolution,[],[f110,f118])).
% 2.32/0.74  fof(f118,plain,(
% 2.32/0.74    ( ! [X2,X0,X1] : (~sQ10_eqProxy(X0,X1) | ~sQ10_eqProxy(X1,X2) | sQ10_eqProxy(X0,X2)) )),
% 2.32/0.74    inference(equality_proxy_axiom,[],[f108])).
% 2.32/0.74  fof(f110,plain,(
% 2.32/0.74    ~sQ10_eqProxy(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))),
% 2.32/0.74    inference(equality_proxy_replacement,[],[f62,f108])).
% 2.32/0.74  fof(f62,plain,(
% 2.32/0.74    k1_funct_2(sK2,sK3) != k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),
% 2.32/0.74    inference(cnf_transformation,[],[f42])).
% 2.32/0.74  fof(f42,plain,(
% 2.32/0.74    k1_funct_2(sK2,sK3) != k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),
% 2.32/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f41])).
% 2.32/0.74  fof(f41,plain,(
% 2.32/0.74    ? [X0,X1] : k1_funct_2(X0,X1) != k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) => k1_funct_2(sK2,sK3) != k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),
% 2.32/0.74    introduced(choice_axiom,[])).
% 2.32/0.74  fof(f18,plain,(
% 2.32/0.74    ? [X0,X1] : k1_funct_2(X0,X1) != k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))),
% 2.32/0.74    inference(ennf_transformation,[],[f17])).
% 2.32/0.74  fof(f17,negated_conjecture,(
% 2.32/0.74    ~! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))),
% 2.32/0.74    inference(negated_conjecture,[],[f16])).
% 2.32/0.74  fof(f16,conjecture,(
% 2.32/0.74    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))),
% 2.32/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_funct_2)).
% 2.32/0.74  fof(f2138,plain,(
% 2.32/0.74    spl11_7 | ~spl11_1),
% 2.32/0.74    inference(avatar_split_clause,[],[f387,f124,f170])).
% 2.32/0.74  fof(f170,plain,(
% 2.32/0.74    spl11_7 <=> v1_funct_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))),
% 2.32/0.74    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 2.32/0.74  fof(f387,plain,(
% 2.32/0.74    v1_funct_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) | ~spl11_1),
% 2.32/0.74    inference(resolution,[],[f126,f79])).
% 2.32/0.74  fof(f79,plain,(
% 2.32/0.74    ( ! [X2,X0,X1] : (v1_funct_1(X2) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 2.32/0.74    inference(cnf_transformation,[],[f26])).
% 2.32/0.74  fof(f26,plain,(
% 2.32/0.74    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 2.32/0.74    inference(ennf_transformation,[],[f12])).
% 2.32/0.74  fof(f12,axiom,(
% 2.32/0.74    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.32/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 2.32/0.74  fof(f126,plain,(
% 2.32/0.74    r2_hidden(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_funct_2(sK2,sK3)) | ~spl11_1),
% 2.32/0.74    inference(avatar_component_clause,[],[f124])).
% 2.32/0.74  fof(f2107,plain,(
% 2.32/0.74    ~spl11_7 | spl11_31 | ~spl11_30),
% 2.32/0.74    inference(avatar_split_clause,[],[f647,f351,f355,f170])).
% 2.32/0.74  fof(f355,plain,(
% 2.32/0.74    spl11_31 <=> ! [X3,X2] : r1_partfun1(k3_partfun1(k1_xboole_0,X2,X3),sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))),
% 2.32/0.74    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).
% 2.32/0.74  fof(f351,plain,(
% 2.32/0.74    spl11_30 <=> v1_relat_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))),
% 2.32/0.74    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).
% 2.32/0.74  fof(f647,plain,(
% 2.32/0.74    ( ! [X4,X5] : (r1_partfun1(k3_partfun1(k1_xboole_0,X4,X5),sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) | ~v1_funct_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))) ) | ~spl11_30),
% 2.32/0.74    inference(resolution,[],[f352,f83])).
% 2.32/0.74  fof(f83,plain,(
% 2.32/0.74    ( ! [X2,X0,X1] : (r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.32/0.74    inference(cnf_transformation,[],[f29])).
% 2.32/0.74  fof(f29,plain,(
% 2.32/0.74    ! [X0,X1,X2] : (r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.32/0.74    inference(flattening,[],[f28])).
% 2.32/0.74  fof(f28,plain,(
% 2.32/0.74    ! [X0,X1,X2] : (r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.32/0.74    inference(ennf_transformation,[],[f13])).
% 2.32/0.74  fof(f13,axiom,(
% 2.32/0.74    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_partfun1(k3_partfun1(k1_xboole_0,X0,X1),X2))),
% 2.32/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_partfun1)).
% 2.32/0.74  fof(f352,plain,(
% 2.32/0.74    v1_relat_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) | ~spl11_30),
% 2.32/0.74    inference(avatar_component_clause,[],[f351])).
% 2.32/0.74  fof(f2064,plain,(
% 2.32/0.74    ~spl11_3 | ~spl11_31 | ~spl11_39),
% 2.32/0.74    inference(avatar_contradiction_clause,[],[f2063])).
% 2.32/0.74  fof(f2063,plain,(
% 2.32/0.74    $false | (~spl11_3 | ~spl11_31 | ~spl11_39)),
% 2.32/0.74    inference(subsumption_resolution,[],[f2055,f140])).
% 2.32/0.74  fof(f140,plain,(
% 2.32/0.74    sP1(sK3,sK2,k3_partfun1(k1_xboole_0,sK2,sK3)) | ~spl11_3),
% 2.32/0.74    inference(avatar_component_clause,[],[f139])).
% 2.32/0.74  fof(f139,plain,(
% 2.32/0.74    spl11_3 <=> sP1(sK3,sK2,k3_partfun1(k1_xboole_0,sK2,sK3))),
% 2.32/0.74    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 2.32/0.74  fof(f2055,plain,(
% 2.32/0.74    ~sP1(sK3,sK2,k3_partfun1(k1_xboole_0,sK2,sK3)) | (~spl11_31 | ~spl11_39)),
% 2.32/0.74    inference(resolution,[],[f1223,f105])).
% 2.32/0.74  fof(f105,plain,(
% 2.32/0.74    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k5_partfun1(X1,X0,X2)) | ~sP1(X0,X1,X2)) )),
% 2.32/0.74    inference(equality_resolution,[],[f90])).
% 2.32/0.74  fof(f90,plain,(
% 2.32/0.74    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3 | ~sP1(X0,X1,X2)) )),
% 2.32/0.74    inference(cnf_transformation,[],[f55])).
% 2.32/0.74  fof(f55,plain,(
% 2.32/0.74    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X0,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3)) | ~sP1(X0,X1,X2))),
% 2.32/0.74    inference(rectify,[],[f54])).
% 2.32/0.74  fof(f54,plain,(
% 2.32/0.74    ! [X1,X0,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP0(X2,X0,X1,X3)) & (sP0(X2,X0,X1,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP1(X1,X0,X2))),
% 2.32/0.74    inference(nnf_transformation,[],[f39])).
% 2.32/0.74  fof(f39,plain,(
% 2.32/0.74    ! [X1,X0,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP0(X2,X0,X1,X3)) | ~sP1(X1,X0,X2))),
% 2.32/0.74    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.32/0.74  fof(f1223,plain,(
% 2.32/0.74    ( ! [X0,X1] : (~sP0(k3_partfun1(k1_xboole_0,X0,X1),sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) ) | (~spl11_31 | ~spl11_39)),
% 2.32/0.74    inference(resolution,[],[f557,f356])).
% 2.32/0.74  fof(f356,plain,(
% 2.32/0.74    ( ! [X2,X3] : (r1_partfun1(k3_partfun1(k1_xboole_0,X2,X3),sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))) ) | ~spl11_31),
% 2.32/0.74    inference(avatar_component_clause,[],[f355])).
% 2.32/0.74  fof(f557,plain,(
% 2.32/0.74    ( ! [X7] : (~r1_partfun1(X7,sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) | ~sP0(X7,sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) ) | ~spl11_39),
% 2.32/0.74    inference(avatar_component_clause,[],[f556])).
% 2.32/0.74  fof(f556,plain,(
% 2.32/0.74    spl11_39 <=> ! [X7] : (~r1_partfun1(X7,sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) | ~sP0(X7,sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))),
% 2.32/0.74    introduced(avatar_definition,[new_symbols(naming,[spl11_39])])).
% 2.32/0.74  fof(f1020,plain,(
% 2.32/0.74    spl11_6 | ~spl11_9 | ~spl11_10),
% 2.32/0.74    inference(avatar_contradiction_clause,[],[f1019])).
% 2.32/0.74  fof(f1019,plain,(
% 2.32/0.74    $false | (spl11_6 | ~spl11_9 | ~spl11_10)),
% 2.32/0.74    inference(subsumption_resolution,[],[f1018,f153])).
% 2.32/0.74  fof(f153,plain,(
% 2.32/0.74    ~r2_hidden(sK5(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)),k1_funct_2(sK2,sK3)) | spl11_6),
% 2.32/0.74    inference(avatar_component_clause,[],[f152])).
% 2.32/0.74  fof(f1018,plain,(
% 2.32/0.74    r2_hidden(sK5(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)),k1_funct_2(sK2,sK3)) | (spl11_6 | ~spl11_9 | ~spl11_10)),
% 2.32/0.74    inference(subsumption_resolution,[],[f1017,f121])).
% 2.32/0.74  fof(f121,plain,(
% 2.32/0.74    ~sQ10_eqProxy(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3))),
% 2.32/0.74    inference(resolution,[],[f110,f117])).
% 2.32/0.74  fof(f117,plain,(
% 2.32/0.74    ( ! [X0,X1] : (~sQ10_eqProxy(X0,X1) | sQ10_eqProxy(X1,X0)) )),
% 2.32/0.74    inference(equality_proxy_axiom,[],[f108])).
% 2.32/0.74  fof(f1017,plain,(
% 2.32/0.74    sQ10_eqProxy(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)) | r2_hidden(sK5(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)),k1_funct_2(sK2,sK3)) | (spl11_6 | ~spl11_9 | ~spl11_10)),
% 2.32/0.74    inference(subsumption_resolution,[],[f1012,f284])).
% 2.32/0.74  fof(f1012,plain,(
% 2.32/0.74    ~r1_tarski(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)) | sQ10_eqProxy(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)) | r2_hidden(sK5(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)),k1_funct_2(sK2,sK3)) | spl11_6),
% 2.32/0.74    inference(resolution,[],[f903,f112])).
% 2.32/0.74  fof(f903,plain,(
% 2.32/0.74    ( ! [X3] : (~r2_hidden(sK5(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),k1_funct_2(sK2,sK3)),X3) | ~r1_tarski(X3,k1_funct_2(sK2,sK3))) ) | spl11_6),
% 2.32/0.74    inference(resolution,[],[f153,f76])).
% 2.32/0.74  fof(f558,plain,(
% 2.32/0.74    spl11_39 | ~spl11_34 | spl11_2 | ~spl11_7 | ~spl11_12),
% 2.32/0.74    inference(avatar_split_clause,[],[f554,f203,f170,f128,f383,f556])).
% 2.32/0.74  fof(f383,plain,(
% 2.32/0.74    spl11_34 <=> v1_partfun1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2)),
% 2.32/0.74    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).
% 2.32/0.74  fof(f128,plain,(
% 2.32/0.74    spl11_2 <=> r2_hidden(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))),
% 2.32/0.74    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 2.32/0.74  fof(f203,plain,(
% 2.32/0.74    spl11_12 <=> m1_subset_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.32/0.74    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 2.32/0.74  fof(f554,plain,(
% 2.32/0.74    ( ! [X7] : (~v1_partfun1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2) | ~r1_partfun1(X7,sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) | ~sP0(X7,sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) ) | (spl11_2 | ~spl11_7 | ~spl11_12)),
% 2.32/0.74    inference(resolution,[],[f408,f205])).
% 2.32/0.74  fof(f205,plain,(
% 2.32/0.74    m1_subset_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~spl11_12),
% 2.32/0.74    inference(avatar_component_clause,[],[f203])).
% 2.32/0.74  fof(f408,plain,(
% 2.32/0.74    ( ! [X2,X0,X1] : (~m1_subset_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_partfun1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),X1) | ~r1_partfun1(X0,sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) | ~sP0(X0,X1,X2,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) ) | (spl11_2 | ~spl11_7)),
% 2.32/0.74    inference(subsumption_resolution,[],[f406,f171])).
% 2.32/0.74  fof(f171,plain,(
% 2.32/0.74    v1_funct_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) | ~spl11_7),
% 2.32/0.74    inference(avatar_component_clause,[],[f170])).
% 2.32/0.74  fof(f406,plain,(
% 2.32/0.74    ( ! [X2,X0,X1] : (~r1_partfun1(X0,sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) | ~v1_partfun1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),X1) | ~m1_subset_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) | ~sP0(X0,X1,X2,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) ) | spl11_2),
% 2.32/0.74    inference(resolution,[],[f129,f107])).
% 2.32/0.74  fof(f107,plain,(
% 2.32/0.74    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(X8,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 2.32/0.74    inference(equality_resolution,[],[f97])).
% 2.32/0.74  fof(f97,plain,(
% 2.32/0.74    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 2.32/0.74    inference(cnf_transformation,[],[f61])).
% 2.32/0.74  fof(f61,plain,(
% 2.32/0.74    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK7(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & ((r1_partfun1(X0,sK8(X0,X1,X2,X3)) & v1_partfun1(sK8(X0,X1,X2,X3),X1) & sK7(X0,X1,X2,X3) = sK8(X0,X1,X2,X3) & m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK8(X0,X1,X2,X3))) | r2_hidden(sK7(X0,X1,X2,X3),X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & ((r1_partfun1(X0,sK9(X0,X1,X2,X7)) & v1_partfun1(sK9(X0,X1,X2,X7),X1) & sK9(X0,X1,X2,X7) = X7 & m1_subset_1(sK9(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK9(X0,X1,X2,X7))) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 2.32/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f57,f60,f59,f58])).
% 2.32/0.74  fof(f58,plain,(
% 2.32/0.74    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3))) => ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK7(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & sK7(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(sK7(X0,X1,X2,X3),X3))))),
% 2.32/0.74    introduced(choice_axiom,[])).
% 2.32/0.74  fof(f59,plain,(
% 2.32/0.74    ! [X3,X2,X1,X0] : (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & sK7(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) => (r1_partfun1(X0,sK8(X0,X1,X2,X3)) & v1_partfun1(sK8(X0,X1,X2,X3),X1) & sK7(X0,X1,X2,X3) = sK8(X0,X1,X2,X3) & m1_subset_1(sK8(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK8(X0,X1,X2,X3))))),
% 2.32/0.74    introduced(choice_axiom,[])).
% 2.32/0.74  fof(f60,plain,(
% 2.32/0.74    ! [X7,X2,X1,X0] : (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) => (r1_partfun1(X0,sK9(X0,X1,X2,X7)) & v1_partfun1(sK9(X0,X1,X2,X7),X1) & sK9(X0,X1,X2,X7) = X7 & m1_subset_1(sK9(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK9(X0,X1,X2,X7))))),
% 2.32/0.74    introduced(choice_axiom,[])).
% 2.32/0.74  fof(f57,plain,(
% 2.32/0.74    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 2.32/0.74    inference(rectify,[],[f56])).
% 2.32/0.74  fof(f56,plain,(
% 2.32/0.74    ! [X2,X0,X1,X3] : ((sP0(X2,X0,X1,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~r2_hidden(X4,X3))) | ~sP0(X2,X0,X1,X3)))),
% 2.32/0.74    inference(nnf_transformation,[],[f38])).
% 2.32/0.74  fof(f38,plain,(
% 2.32/0.74    ! [X2,X0,X1,X3] : (sP0(X2,X0,X1,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5))))),
% 2.32/0.74    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.32/0.74  fof(f129,plain,(
% 2.32/0.74    ~r2_hidden(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) | spl11_2),
% 2.32/0.74    inference(avatar_component_clause,[],[f128])).
% 2.32/0.74  fof(f439,plain,(
% 2.32/0.74    spl11_30 | ~spl11_12),
% 2.32/0.74    inference(avatar_split_clause,[],[f431,f203,f351])).
% 2.32/0.74  fof(f431,plain,(
% 2.32/0.74    v1_relat_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) | ~spl11_12),
% 2.32/0.74    inference(resolution,[],[f205,f82])).
% 2.32/0.74  fof(f82,plain,(
% 2.32/0.74    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/0.74    inference(cnf_transformation,[],[f27])).
% 2.32/0.74  fof(f27,plain,(
% 2.32/0.74    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/0.74    inference(ennf_transformation,[],[f6])).
% 2.32/0.74  fof(f6,axiom,(
% 2.32/0.74    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.32/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.32/0.74  fof(f438,plain,(
% 2.32/0.74    ~spl11_20 | spl11_34 | ~spl11_12),
% 2.32/0.74    inference(avatar_split_clause,[],[f430,f203,f383,f278])).
% 2.32/0.74  fof(f430,plain,(
% 2.32/0.74    v1_partfun1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2) | ~v1_xboole_0(sK2) | ~spl11_12),
% 2.32/0.74    inference(resolution,[],[f205,f72])).
% 2.32/0.74  fof(f72,plain,(
% 2.32/0.74    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.32/0.74    inference(cnf_transformation,[],[f21])).
% 2.32/0.74  fof(f21,plain,(
% 2.32/0.74    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.32/0.74    inference(ennf_transformation,[],[f7])).
% 2.32/0.74  fof(f7,axiom,(
% 2.32/0.74    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 2.32/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).
% 2.32/0.74  fof(f401,plain,(
% 2.32/0.74    spl11_11 | ~spl11_1),
% 2.32/0.74    inference(avatar_split_clause,[],[f388,f124,f198])).
% 2.32/0.74  fof(f198,plain,(
% 2.32/0.74    spl11_11 <=> v1_funct_2(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2,sK3)),
% 2.32/0.74    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 2.32/0.74  fof(f388,plain,(
% 2.32/0.74    v1_funct_2(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2,sK3) | ~spl11_1),
% 2.32/0.74    inference(resolution,[],[f126,f80])).
% 2.32/0.74  fof(f80,plain,(
% 2.32/0.74    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 2.32/0.74    inference(cnf_transformation,[],[f26])).
% 2.32/0.74  fof(f400,plain,(
% 2.32/0.74    ~spl11_2 | ~spl11_1),
% 2.32/0.74    inference(avatar_split_clause,[],[f399,f124,f128])).
% 2.32/0.74  fof(f399,plain,(
% 2.32/0.74    ~r2_hidden(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) | ~spl11_1),
% 2.32/0.74    inference(subsumption_resolution,[],[f390,f110])).
% 2.32/0.74  fof(f390,plain,(
% 2.32/0.74    sQ10_eqProxy(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) | ~r2_hidden(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) | ~spl11_1),
% 2.32/0.74    inference(resolution,[],[f126,f111])).
% 2.32/0.74  fof(f111,plain,(
% 2.32/0.74    ( ! [X0,X1] : (sQ10_eqProxy(X0,X1) | ~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0)) )),
% 2.32/0.74    inference(equality_proxy_replacement,[],[f75,f108])).
% 2.32/0.74  fof(f75,plain,(
% 2.32/0.74    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0)) )),
% 2.32/0.74    inference(cnf_transformation,[],[f49])).
% 2.32/0.74  fof(f398,plain,(
% 2.32/0.74    spl11_12 | ~spl11_1),
% 2.32/0.74    inference(avatar_split_clause,[],[f389,f124,f203])).
% 2.32/0.74  fof(f389,plain,(
% 2.32/0.74    m1_subset_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~spl11_1),
% 2.32/0.74    inference(resolution,[],[f126,f81])).
% 2.32/0.74  fof(f81,plain,(
% 2.32/0.74    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 2.32/0.74    inference(cnf_transformation,[],[f26])).
% 2.32/0.74  fof(f386,plain,(
% 2.32/0.74    spl11_17 | ~spl11_12 | spl11_34 | ~spl11_7 | ~spl11_11),
% 2.32/0.74    inference(avatar_split_clause,[],[f381,f198,f170,f383,f203,f265])).
% 2.32/0.74  fof(f381,plain,(
% 2.32/0.74    v1_partfun1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2) | ~m1_subset_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | v1_xboole_0(sK3) | (~spl11_7 | ~spl11_11)),
% 2.32/0.74    inference(subsumption_resolution,[],[f380,f171])).
% 2.32/0.74  fof(f380,plain,(
% 2.32/0.74    v1_partfun1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2) | ~v1_funct_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) | ~m1_subset_1(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | v1_xboole_0(sK3) | ~spl11_11),
% 2.32/0.74    inference(resolution,[],[f200,f71])).
% 2.32/0.74  fof(f71,plain,(
% 2.32/0.74    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.32/0.74    inference(cnf_transformation,[],[f20])).
% 2.32/0.74  fof(f20,plain,(
% 2.32/0.74    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.32/0.74    inference(flattening,[],[f19])).
% 2.32/0.74  fof(f19,plain,(
% 2.32/0.74    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.32/0.74    inference(ennf_transformation,[],[f8])).
% 2.32/0.74  fof(f8,axiom,(
% 2.32/0.74    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.32/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 2.32/0.75  fof(f200,plain,(
% 2.32/0.75    v1_funct_2(sK5(k1_funct_2(sK2,sK3),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2,sK3) | ~spl11_11),
% 2.32/0.75    inference(avatar_component_clause,[],[f198])).
% 2.32/0.75  fof(f250,plain,(
% 2.32/0.75    spl11_10),
% 2.32/0.75    inference(avatar_contradiction_clause,[],[f249])).
% 2.32/0.75  fof(f249,plain,(
% 2.32/0.75    $false | spl11_10),
% 2.32/0.75    inference(subsumption_resolution,[],[f248,f64])).
% 2.32/0.75  fof(f64,plain,(
% 2.32/0.75    v1_relat_1(k1_xboole_0)),
% 2.32/0.75    inference(cnf_transformation,[],[f5])).
% 2.32/0.75  fof(f5,axiom,(
% 2.32/0.75    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 2.32/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).
% 2.32/0.75  fof(f248,plain,(
% 2.32/0.75    ~v1_relat_1(k1_xboole_0) | spl11_10),
% 2.32/0.75    inference(subsumption_resolution,[],[f245,f66])).
% 2.32/0.75  fof(f66,plain,(
% 2.32/0.75    v1_funct_1(k1_xboole_0)),
% 2.32/0.75    inference(cnf_transformation,[],[f5])).
% 2.32/0.75  fof(f245,plain,(
% 2.32/0.75    ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | spl11_10),
% 2.32/0.75    inference(resolution,[],[f195,f85])).
% 2.32/0.75  fof(f85,plain,(
% 2.32/0.75    ( ! [X2,X0,X1] : (m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/0.75    inference(cnf_transformation,[],[f31])).
% 2.32/0.75  fof(f31,plain,(
% 2.32/0.75    ! [X0,X1,X2] : ((m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(k3_partfun1(X0,X1,X2))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.32/0.75    inference(flattening,[],[f30])).
% 2.32/0.75  fof(f30,plain,(
% 2.32/0.75    ! [X0,X1,X2] : ((m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(k3_partfun1(X0,X1,X2))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.32/0.75    inference(ennf_transformation,[],[f10])).
% 2.32/0.75  fof(f10,axiom,(
% 2.32/0.75    ! [X0,X1,X2] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(k3_partfun1(X0,X1,X2))))),
% 2.32/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_partfun1)).
% 2.32/0.75  fof(f195,plain,(
% 2.32/0.75    ~m1_subset_1(k3_partfun1(k1_xboole_0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | spl11_10),
% 2.32/0.75    inference(avatar_component_clause,[],[f193])).
% 2.32/0.75  fof(f241,plain,(
% 2.32/0.75    ~spl11_10 | spl11_3 | ~spl11_9),
% 2.32/0.75    inference(avatar_split_clause,[],[f240,f189,f139,f193])).
% 2.32/0.75  fof(f240,plain,(
% 2.32/0.75    ~m1_subset_1(k3_partfun1(k1_xboole_0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | (spl11_3 | ~spl11_9)),
% 2.32/0.75    inference(subsumption_resolution,[],[f239,f190])).
% 2.32/0.75  fof(f239,plain,(
% 2.32/0.75    ~m1_subset_1(k3_partfun1(k1_xboole_0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_1(k3_partfun1(k1_xboole_0,sK2,sK3)) | spl11_3),
% 2.32/0.75    inference(resolution,[],[f141,f104])).
% 2.32/0.75  fof(f104,plain,(
% 2.32/0.75    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.32/0.75    inference(cnf_transformation,[],[f40])).
% 2.32/0.75  fof(f40,plain,(
% 2.32/0.75    ! [X0,X1,X2] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.32/0.75    inference(definition_folding,[],[f37,f39,f38])).
% 2.32/0.75  fof(f37,plain,(
% 2.32/0.75    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.32/0.75    inference(flattening,[],[f36])).
% 2.32/0.75  fof(f36,plain,(
% 2.32/0.75    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.32/0.75    inference(ennf_transformation,[],[f9])).
% 2.32/0.75  fof(f9,axiom,(
% 2.32/0.75    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 2.32/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).
% 2.32/0.75  fof(f141,plain,(
% 2.32/0.75    ~sP1(sK3,sK2,k3_partfun1(k1_xboole_0,sK2,sK3)) | spl11_3),
% 2.32/0.75    inference(avatar_component_clause,[],[f139])).
% 2.32/0.75  fof(f212,plain,(
% 2.32/0.75    spl11_9),
% 2.32/0.75    inference(avatar_contradiction_clause,[],[f211])).
% 2.32/0.75  fof(f211,plain,(
% 2.32/0.75    $false | spl11_9),
% 2.32/0.75    inference(subsumption_resolution,[],[f210,f64])).
% 2.32/0.75  fof(f210,plain,(
% 2.32/0.75    ~v1_relat_1(k1_xboole_0) | spl11_9),
% 2.32/0.75    inference(subsumption_resolution,[],[f207,f66])).
% 2.32/0.75  fof(f207,plain,(
% 2.32/0.75    ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | spl11_9),
% 2.32/0.75    inference(resolution,[],[f191,f84])).
% 2.32/0.75  fof(f84,plain,(
% 2.32/0.75    ( ! [X2,X0,X1] : (v1_funct_1(k3_partfun1(X0,X1,X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/0.75    inference(cnf_transformation,[],[f31])).
% 2.32/0.75  fof(f191,plain,(
% 2.32/0.75    ~v1_funct_1(k3_partfun1(k1_xboole_0,sK2,sK3)) | spl11_9),
% 2.32/0.75    inference(avatar_component_clause,[],[f189])).
% 2.32/0.75  % SZS output end Proof for theBenchmark
% 2.32/0.75  % (21937)------------------------------
% 2.32/0.75  % (21937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.32/0.75  % (21937)Termination reason: Refutation
% 2.32/0.75  
% 2.32/0.75  % (21937)Memory used [KB]: 7164
% 2.32/0.75  % (21937)Time elapsed: 0.293 s
% 2.32/0.75  % (21937)------------------------------
% 2.32/0.75  % (21937)------------------------------
% 2.32/0.75  % (21932)Success in time 0.373 s
%------------------------------------------------------------------------------
