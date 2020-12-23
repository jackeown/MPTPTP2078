%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1156+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:10 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 197 expanded)
%              Number of leaves         :   10 (  61 expanded)
%              Depth                    :   17
%              Number of atoms          :  251 (1145 expanded)
%              Number of equality atoms :   33 (  39 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2853,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2852,f2227])).

fof(f2227,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f2111])).

fof(f2111,plain,
    ( r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_orders_2(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f1917,f2110,f2109])).

fof(f2109,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X1)))
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_orders_2(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f2110,plain,
    ( ? [X1] :
        ( r2_hidden(X1,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X1)))
        & m1_subset_1(X1,u1_struct_0(sK4)) )
   => ( r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
      & m1_subset_1(sK5,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f1917,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f1916])).

fof(f1916,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1912])).

fof(f1912,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    inference(negated_conjecture,[],[f1911])).

fof(f1911,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_orders_2)).

fof(f2852,plain,(
    v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f2851,f2228])).

fof(f2228,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f2111])).

fof(f2851,plain,
    ( ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f2850,f2229])).

fof(f2229,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f2111])).

fof(f2850,plain,
    ( ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f2849,f2230])).

fof(f2230,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f2111])).

fof(f2849,plain,
    ( ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f2848,f2231])).

fof(f2231,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f2111])).

fof(f2848,plain,
    ( ~ l1_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f2847,f2232])).

fof(f2232,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f2111])).

fof(f2847,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f2846,f2765])).

fof(f2765,plain,(
    m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(backward_demodulation,[],[f2693,f2763])).

fof(f2763,plain,(
    k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5) ),
    inference(global_subsumption,[],[f2502,f2629,f2682])).

fof(f2682,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f2232,f2259])).

fof(f2259,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1946])).

fof(f1946,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1945])).

fof(f1945,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1887])).

fof(f1887,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f2629,plain,(
    l1_struct_0(sK4) ),
    inference(resolution,[],[f2231,f2415])).

fof(f2415,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2057])).

fof(f2057,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1877])).

fof(f1877,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f2502,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_struct_0(sK4) ),
    inference(resolution,[],[f2227,f2413])).

fof(f2413,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2055])).

fof(f2055,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2054])).

fof(f2054,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1795])).

fof(f1795,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f2693,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subsumption_resolution,[],[f2692,f2227])).

fof(f2692,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f2691,f2228])).

fof(f2691,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f2644,f2231])).

fof(f2644,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK4),sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f2232,f2261])).

fof(f2261,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1948])).

fof(f1948,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f1947])).

fof(f1947,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1898])).

fof(f1898,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

fof(f2846,plain,
    ( ~ m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f2796,f2480])).

fof(f2480,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f2479])).

fof(f2479,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f2345])).

fof(f2345,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2167])).

fof(f2167,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK24(X0,X1) != X0
            | ~ r2_hidden(sK24(X0,X1),X1) )
          & ( sK24(X0,X1) = X0
            | r2_hidden(sK24(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24])],[f2165,f2166])).

fof(f2166,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK24(X0,X1) != X0
          | ~ r2_hidden(sK24(X0,X1),X1) )
        & ( sK24(X0,X1) = X0
          | r2_hidden(sK24(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2165,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f2164])).

fof(f2164,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f2796,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK5))
    | ~ m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f2767,f2255])).

fof(f2255,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1938])).

fof(f1938,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f1937])).

fof(f1937,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1910])).

fof(f1910,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( r2_hidden(X1,k2_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_orders_2)).

fof(f2767,plain,(
    r2_hidden(sK5,k2_orders_2(sK4,k1_tarski(sK5))) ),
    inference(backward_demodulation,[],[f2233,f2763])).

fof(f2233,plain,(
    r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) ),
    inference(cnf_transformation,[],[f2111])).
%------------------------------------------------------------------------------
