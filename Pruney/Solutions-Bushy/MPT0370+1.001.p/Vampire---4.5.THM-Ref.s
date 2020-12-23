%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0370+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:51 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 225 expanded)
%              Number of leaves         :   12 (  73 expanded)
%              Depth                    :   20
%              Number of atoms          :  314 (1170 expanded)
%              Number of equality atoms :   27 ( 153 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1285,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f848,f864,f1277,f1284])).

fof(f1284,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f1282])).

fof(f1282,plain,
    ( $false
    | spl5_3
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f58,f842,f58,f847,f1281,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,sK2)
      | ~ sQ4_eqProxy(sK1,X2)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(resolution,[],[f108,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f30,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,sK0)
      | ~ sQ4_eqProxy(X1,X2)
      | r2_hidden(X2,X0)
      | r2_hidden(X1,sK2)
      | ~ sQ4_eqProxy(sK1,X0) ) ),
    inference(resolution,[],[f57,f27])).

fof(f27,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k3_subset_1(sK0,sK2)
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK1)
            | r2_hidden(X3,sK2) )
          & ( ~ r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | r2_hidden(X3,X2) )
                  & ( ~ r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != k3_subset_1(sK0,X2)
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK1)
                  | r2_hidden(X3,X2) )
                & ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK1) ) )
              | ~ m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( sK1 != k3_subset_1(sK0,X2)
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK1)
                | r2_hidden(X3,X2) )
              & ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,sK1) ) )
            | ~ m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( sK1 != k3_subset_1(sK0,sK2)
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK1)
              | r2_hidden(X3,sK2) )
            & ( ~ r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) ) )
          | ~ m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | r2_hidden(X3,X2) )
                & ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> ~ r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> ~ r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> ~ r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> ~ r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_subset_1)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ sQ4_eqProxy(X2,X3)
      | ~ sQ4_eqProxy(X0,X1)
      | r2_hidden(X1,X3) ) ),
    inference(equality_proxy_axiom,[],[f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f1281,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f105,f842])).

fof(f105,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | r2_hidden(sK3(sK0,sK2,sK1),sK1) ),
    inference(resolution,[],[f102,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k4_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f40,f45])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f102,plain,(
    ~ sQ4_eqProxy(k4_xboole_0(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f98,f25])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f98,plain,
    ( ~ sQ4_eqProxy(k4_xboole_0(sK0,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f91,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(k3_subset_1(X0,X1),k4_xboole_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(equality_proxy_replacement,[],[f33,f45])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f91,plain,(
    ! [X1] :
      ( ~ sQ4_eqProxy(k3_subset_1(sK0,sK2),X1)
      | ~ sQ4_eqProxy(X1,sK1) ) ),
    inference(resolution,[],[f60,f61])).

fof(f61,plain,(
    ~ sQ4_eqProxy(k3_subset_1(sK0,sK2),sK1) ),
    inference(resolution,[],[f59,f46])).

fof(f46,plain,(
    ~ sQ4_eqProxy(sK1,k3_subset_1(sK0,sK2)) ),
    inference(equality_proxy_replacement,[],[f28,f45])).

fof(f28,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X1,X0)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f45])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(X0,X2)
      | ~ sQ4_eqProxy(X1,X2)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f45])).

fof(f847,plain,
    ( r2_hidden(sK3(sK0,sK2,sK1),sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f845])).

fof(f845,plain,
    ( spl5_4
  <=> r2_hidden(sK3(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f842,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f841])).

fof(f841,plain,
    ( spl5_3
  <=> r2_hidden(sK3(sK0,sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f58,plain,(
    ! [X0] : sQ4_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f45])).

fof(f1277,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f1276])).

fof(f1276,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1265,f847])).

fof(f1265,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),sK0)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f1248,f80])).

fof(f1248,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2,sK1),sK0)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1243,f843])).

fof(f843,plain,
    ( r2_hidden(sK3(sK0,sK2,sK1),sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f841])).

fof(f1243,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),sK1)
    | ~ m1_subset_1(sK3(sK0,sK2,sK1),sK0)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f1238,f26])).

fof(f26,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,sK0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1238,plain,
    ( r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1237,f843])).

fof(f1237,plain,
    ( r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | ~ r2_hidden(sK3(sK0,sK2,sK1),sK1)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f103,f847])).

fof(f103,plain,
    ( r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | ~ r2_hidden(sK3(sK0,sK2,sK1),sK0)
    | ~ r2_hidden(sK3(sK0,sK2,sK1),sK1) ),
    inference(resolution,[],[f102,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f41,f45])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f864,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f859])).

fof(f859,plain,
    ( $false
    | ~ spl5_3
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f58,f843,f58,f846,f186])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X1,X2)
      | ~ sQ4_eqProxy(X0,X1)
      | ~ sQ4_eqProxy(sK0,X2) ) ),
    inference(resolution,[],[f109,f24])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f109,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(X3))
      | ~ sQ4_eqProxy(X5,X6)
      | r2_hidden(X6,X4)
      | ~ r2_hidden(X5,X7)
      | ~ sQ4_eqProxy(X3,X4) ) ),
    inference(resolution,[],[f57,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f846,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f845])).

fof(f848,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f104,f845,f841])).

fof(f104,plain,
    ( r2_hidden(sK3(sK0,sK2,sK1),sK0)
    | r2_hidden(sK3(sK0,sK2,sK1),sK1) ),
    inference(resolution,[],[f102,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f39,f45])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------
