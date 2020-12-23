%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1164+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:10 EST 2020

% Result     : Theorem 7.06s
% Output     : Refutation 7.06s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 517 expanded)
%              Number of leaves         :   19 ( 197 expanded)
%              Depth                    :   18
%              Number of atoms          :  699 (3684 expanded)
%              Number of equality atoms :   74 ( 142 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8602,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2351,f2380,f3416,f3475,f8200,f8484,f8595])).

fof(f8595,plain,
    ( ~ spl18_5
    | spl18_45 ),
    inference(avatar_contradiction_clause,[],[f8594])).

fof(f8594,plain,
    ( $false
    | ~ spl18_5
    | spl18_45 ),
    inference(subsumption_resolution,[],[f8541,f3415])).

fof(f3415,plain,
    ( ~ m1_orders_2(sK2,sK0,k1_xboole_0)
    | spl18_45 ),
    inference(avatar_component_clause,[],[f3413])).

fof(f3413,plain,
    ( spl18_45
  <=> m1_orders_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_45])])).

fof(f8541,plain,
    ( m1_orders_2(sK2,sK0,k1_xboole_0)
    | ~ spl18_5 ),
    inference(superposition,[],[f2048,f2346])).

fof(f2346,plain,
    ( k1_xboole_0 = sK1
    | ~ spl18_5 ),
    inference(avatar_component_clause,[],[f2344])).

fof(f2344,plain,
    ( spl18_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_5])])).

fof(f2048,plain,(
    m1_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f1993])).

fof(f1993,plain,
    ( ~ r1_tarski(sK2,sK1)
    & m1_orders_2(sK2,sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1929,f1992,f1991,f1990])).

fof(f1990,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(X2,X1)
                & m1_orders_2(X2,X0,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & m1_orders_2(X2,sK0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1991,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,X1)
            & m1_orders_2(X2,sK0,X1) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,sK1)
          & m1_orders_2(X2,sK0,sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f1992,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,sK1)
        & m1_orders_2(X2,sK0,sK1) )
   => ( ~ r1_tarski(sK2,sK1)
      & m1_orders_2(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1929,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & m1_orders_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f1928])).

fof(f1928,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & m1_orders_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1925])).

fof(f1925,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_orders_2(X2,X0,X1)
               => r1_tarski(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1924])).

fof(f1924,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

fof(f8484,plain,
    ( spl18_5
    | spl18_8 ),
    inference(avatar_split_clause,[],[f8483,f2370,f2344])).

fof(f2370,plain,
    ( spl18_8
  <=> sK2 = k3_orders_2(sK0,sK1,sK8(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_8])])).

fof(f8483,plain,
    ( sK2 = k3_orders_2(sK0,sK1,sK8(sK0,sK1,sK2))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f6992,f2047])).

fof(f2047,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f1993])).

fof(f6992,plain,
    ( sK2 = k3_orders_2(sK0,sK1,sK8(sK0,sK1,sK2))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f2181,f2048])).

fof(f2181,plain,(
    ! [X8,X7] :
      ( ~ m1_orders_2(X8,sK0,X7)
      | k3_orders_2(sK0,X7,sK8(sK0,X7,X8)) = X8
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f2180,f2166])).

fof(f2166,plain,(
    ! [X2,X1] :
      ( ~ m1_orders_2(X1,sK0,X2)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f2165,f2043])).

fof(f2043,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f1993])).

fof(f2165,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X1,sK0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f2164,f2044])).

fof(f2044,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f1993])).

fof(f2164,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X1,sK0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f2163,f2045])).

fof(f2045,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f1993])).

fof(f2163,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X1,sK0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f2143,f2046])).

fof(f2046,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f1993])).

fof(f2143,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X1,sK0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f2042,f2071])).

fof(f2071,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1942])).

fof(f1942,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f1941])).

fof(f1941,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1881])).

fof(f1881,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).

fof(f2042,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f1993])).

fof(f2180,plain,(
    ! [X8,X7] :
      ( k3_orders_2(sK0,X7,sK8(sK0,X7,X8)) = X8
      | ~ m1_orders_2(X8,sK0,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f2179,f2043])).

fof(f2179,plain,(
    ! [X8,X7] :
      ( k3_orders_2(sK0,X7,sK8(sK0,X7,X8)) = X8
      | ~ m1_orders_2(X8,sK0,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f2178,f2044])).

fof(f2178,plain,(
    ! [X8,X7] :
      ( k3_orders_2(sK0,X7,sK8(sK0,X7,X8)) = X8
      | ~ m1_orders_2(X8,sK0,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f2177,f2045])).

fof(f2177,plain,(
    ! [X8,X7] :
      ( k3_orders_2(sK0,X7,sK8(sK0,X7,X8)) = X8
      | ~ m1_orders_2(X8,sK0,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f2146,f2046])).

fof(f2146,plain,(
    ! [X8,X7] :
      ( k3_orders_2(sK0,X7,sK8(sK0,X7,X8)) = X8
      | ~ m1_orders_2(X8,sK0,X7)
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f2042,f2074])).

fof(f2074,plain,(
    ! [X2,X0,X1] :
      ( k3_orders_2(X0,X1,sK8(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2014])).

fof(f2014,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ( k3_orders_2(X0,X1,sK8(X0,X1,X2)) = X2
                        & r2_hidden(sK8(X0,X1,X2),X1)
                        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f2012,f2013])).

fof(f2013,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK8(X0,X1,X2)) = X2
        & r2_hidden(sK8(X0,X1,X2),X1)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2012,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X4] :
                          ( k3_orders_2(X0,X1,X4) = X2
                          & r2_hidden(X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f2011])).

fof(f2011,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X3] :
                          ( k3_orders_2(X0,X1,X3) = X2
                          & r2_hidden(X3,X1)
                          & m1_subset_1(X3,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f1944])).

fof(f1944,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f1943])).

fof(f1943,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1868])).

fof(f1868,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( k1_xboole_0 = X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 ) )
                & ( k1_xboole_0 != X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).

fof(f8200,plain,
    ( ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8 ),
    inference(avatar_contradiction_clause,[],[f8199])).

fof(f8199,plain,
    ( $false
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8 ),
    inference(subsumption_resolution,[],[f8183,f2305])).

fof(f2305,plain,(
    ~ r2_hidden(sK4(sK2,sK1),sK1) ),
    inference(resolution,[],[f2049,f2060])).

fof(f2060,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f2002])).

fof(f2002,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f2000,f2001])).

fof(f2001,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2000,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1999])).

fof(f1999,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1933])).

fof(f1933,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f2049,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f1993])).

fof(f8183,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8 ),
    inference(resolution,[],[f4658,f2304])).

fof(f2304,plain,(
    r2_hidden(sK4(sK2,sK1),sK2) ),
    inference(resolution,[],[f2049,f2059])).

fof(f2059,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f2002])).

fof(f4658,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | r2_hidden(X3,sK1) )
    | ~ spl18_4
    | ~ spl18_6
    | ~ spl18_8 ),
    inference(subsumption_resolution,[],[f4657,f3086])).

fof(f3086,plain,
    ( ! [X33] :
        ( m1_subset_1(X33,u1_struct_0(sK0))
        | ~ r2_hidden(X33,sK2) )
    | ~ spl18_4 ),
    inference(resolution,[],[f2341,f2085])).

fof(f2085,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1951])).

fof(f1951,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f1950])).

fof(f1950,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f618])).

fof(f618,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f2341,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl18_4 ),
    inference(avatar_component_clause,[],[f2340])).

fof(f2340,plain,
    ( spl18_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).

fof(f4657,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl18_6
    | ~ spl18_8 ),
    inference(subsumption_resolution,[],[f4656,f2042])).

fof(f4656,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl18_6
    | ~ spl18_8 ),
    inference(subsumption_resolution,[],[f4655,f2043])).

fof(f4655,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_6
    | ~ spl18_8 ),
    inference(subsumption_resolution,[],[f4654,f2044])).

fof(f4654,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_6
    | ~ spl18_8 ),
    inference(subsumption_resolution,[],[f4653,f2045])).

fof(f4653,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_6
    | ~ spl18_8 ),
    inference(subsumption_resolution,[],[f4652,f2046])).

fof(f4652,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_6
    | ~ spl18_8 ),
    inference(subsumption_resolution,[],[f4651,f2350])).

fof(f2350,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl18_6 ),
    inference(avatar_component_clause,[],[f2348])).

fof(f2348,plain,
    ( spl18_6
  <=> m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_6])])).

fof(f4651,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | r2_hidden(X3,sK1)
        | ~ m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_8 ),
    inference(subsumption_resolution,[],[f4614,f2047])).

fof(f4614,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | r2_hidden(X3,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl18_8 ),
    inference(superposition,[],[f2106,f2372])).

fof(f2372,plain,
    ( sK2 = k3_orders_2(sK0,sK1,sK8(sK0,sK1,sK2))
    | ~ spl18_8 ),
    inference(avatar_component_clause,[],[f2370])).

fof(f2106,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2035])).

fof(f2035,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2034])).

fof(f2034,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f1972])).

fof(f1972,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f1971])).

fof(f1971,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1919])).

fof(f1919,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

fof(f3475,plain,(
    ~ spl18_17 ),
    inference(avatar_contradiction_clause,[],[f3474])).

fof(f3474,plain,
    ( $false
    | ~ spl18_17 ),
    inference(subsumption_resolution,[],[f3465,f2128])).

fof(f2128,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f3465,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl18_17 ),
    inference(superposition,[],[f2303,f3124])).

fof(f3124,plain,
    ( k1_xboole_0 = sK2
    | ~ spl18_17 ),
    inference(avatar_component_clause,[],[f3122])).

fof(f3122,plain,
    ( spl18_17
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_17])])).

fof(f2303,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f2049,f2052])).

fof(f2052,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1994])).

fof(f1994,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f3416,plain,
    ( ~ spl18_45
    | spl18_17
    | ~ spl18_4 ),
    inference(avatar_split_clause,[],[f3411,f2340,f3122,f3413])).

fof(f3411,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,k1_xboole_0)
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f3410,f2042])).

fof(f3410,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,k1_xboole_0)
    | v2_struct_0(sK0)
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f3409,f2043])).

fof(f3409,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,k1_xboole_0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f3408,f2044])).

fof(f3408,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,k1_xboole_0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f3407,f2045])).

fof(f3407,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,k1_xboole_0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f3406,f2046])).

fof(f3406,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,k1_xboole_0)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f3072,f2128])).

fof(f3072,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl18_4 ),
    inference(resolution,[],[f2341,f2136])).

fof(f2136,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f2076])).

fof(f2076,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2014])).

fof(f2380,plain,(
    spl18_4 ),
    inference(avatar_split_clause,[],[f2379,f2340])).

fof(f2379,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2378,f2042])).

fof(f2378,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2377,f2043])).

fof(f2377,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2376,f2044])).

fof(f2376,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2375,f2045])).

fof(f2375,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2374,f2046])).

fof(f2374,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2332,f2047])).

fof(f2332,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f2048,f2071])).

fof(f2351,plain,
    ( ~ spl18_4
    | spl18_5
    | spl18_6 ),
    inference(avatar_split_clause,[],[f2338,f2348,f2344,f2340])).

fof(f2338,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2337,f2042])).

fof(f2337,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2336,f2043])).

fof(f2336,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2335,f2044])).

fof(f2335,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2334,f2045])).

fof(f2334,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2333,f2046])).

fof(f2333,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2329,f2047])).

fof(f2329,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f2048,f2072])).

fof(f2072,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2014])).
%------------------------------------------------------------------------------
