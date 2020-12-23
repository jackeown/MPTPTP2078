%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1162+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:10 EST 2020

% Result     : Theorem 10.86s
% Output     : Refutation 11.00s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 768 expanded)
%              Number of leaves         :   11 ( 336 expanded)
%              Depth                    :   25
%              Number of atoms          :  459 (6688 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16183,plain,(
    $false ),
    inference(subsumption_resolution,[],[f16175,f3970])).

fof(f3970,plain,(
    ~ r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f3969,f2064])).

fof(f2064,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2016])).

fof(f2016,plain,
    ( ~ r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2))
    & r2_orders_2(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f1934,f2015,f2014,f2013,f2012])).

fof(f2012,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2))
                    & r2_orders_2(X0,X1,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k3_orders_2(sK0,X3,X1),k3_orders_2(sK0,X3,X2))
                  & r2_orders_2(sK0,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2013,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k3_orders_2(sK0,X3,X1),k3_orders_2(sK0,X3,X2))
                & r2_orders_2(sK0,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k3_orders_2(sK0,X3,sK1),k3_orders_2(sK0,X3,X2))
              & r2_orders_2(sK0,sK1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2014,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k3_orders_2(sK0,X3,sK1),k3_orders_2(sK0,X3,X2))
            & r2_orders_2(sK0,sK1,X2)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ~ r1_tarski(k3_orders_2(sK0,X3,sK1),k3_orders_2(sK0,X3,sK2))
          & r2_orders_2(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2015,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k3_orders_2(sK0,X3,sK1),k3_orders_2(sK0,X3,sK2))
        & r2_orders_2(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2))
      & r2_orders_2(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f1934,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2))
                  & r2_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f1933])).

fof(f1933,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2))
                  & r2_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1920])).

fof(f1920,negated_conjecture,(
    ~ ! [X0] :
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
                   => ( r2_orders_2(X0,X1,X2)
                     => r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1919])).

fof(f1919,conjecture,(
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
                 => ( r2_orders_2(X0,X1,X2)
                   => r1_tarski(k3_orders_2(X0,X3,X1),k3_orders_2(X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_orders_2)).

fof(f3969,plain,
    ( ~ r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3968,f2065])).

fof(f2065,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2016])).

fof(f3968,plain,
    ( ~ r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3967,f2066])).

fof(f2066,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2016])).

fof(f3967,plain,
    ( ~ r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3966,f2067])).

fof(f2067,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2016])).

fof(f3966,plain,
    ( ~ r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3965,f2068])).

fof(f2068,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2016])).

fof(f3965,plain,
    ( ~ r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3964,f3926])).

fof(f3926,plain,(
    m1_subset_1(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f2227,f2272,f2111])).

fof(f2111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1966])).

fof(f1966,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f1965])).

fof(f1965,plain,(
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

fof(f2272,plain,(
    r2_hidden(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f2073,f2083])).

fof(f2083,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2025])).

fof(f2025,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f2023,f2024])).

fof(f2024,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2023,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f2022])).

fof(f2022,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1938])).

fof(f1938,plain,(
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

fof(f2073,plain,(
    ~ r1_tarski(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f2016])).

fof(f2227,plain,(
    m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f2064,f2065,f2066,f2067,f2068,f2069,f2071,f2094])).

fof(f2094,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1945])).

fof(f1945,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f1944])).

fof(f1944,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1876])).

fof(f1876,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(f2071,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2016])).

fof(f2069,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2016])).

fof(f3964,plain,
    ( ~ r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2)
    | ~ m1_subset_1(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3963,f2070])).

fof(f2070,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2016])).

fof(f3963,plain,
    ( ~ r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3962,f2071])).

fof(f3962,plain,
    ( ~ r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3961,f3953])).

fof(f3953,plain,(
    r2_hidden(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3) ),
    inference(subsumption_resolution,[],[f3952,f2064])).

fof(f3952,plain,
    ( r2_hidden(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3951,f2065])).

fof(f3951,plain,
    ( r2_hidden(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3950,f2066])).

fof(f3950,plain,
    ( r2_hidden(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3949,f2067])).

fof(f3949,plain,
    ( r2_hidden(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3948,f2068])).

fof(f3948,plain,
    ( r2_hidden(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3947,f3926])).

fof(f3947,plain,
    ( r2_hidden(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3)
    | ~ m1_subset_1(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3946,f2069])).

fof(f3946,plain,
    ( r2_hidden(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3934,f2071])).

fof(f3934,plain,
    ( r2_hidden(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f2272,f2098])).

fof(f2098,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | r2_hidden(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2033])).

fof(f2033,plain,(
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
    inference(flattening,[],[f2032])).

fof(f2032,plain,(
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
    inference(nnf_transformation,[],[f1951])).

fof(f1951,plain,(
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
    inference(flattening,[],[f1950])).

fof(f1950,plain,(
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
    inference(ennf_transformation,[],[f1916])).

fof(f1916,axiom,(
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

fof(f3961,plain,
    ( ~ r2_hidden(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK3)
    | ~ r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f2273,f2099])).

fof(f2099,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ r2_hidden(X1,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2033])).

fof(f2273,plain,(
    ~ r2_hidden(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),k3_orders_2(sK0,sK3,sK2)) ),
    inference(unit_resulting_resolution,[],[f2073,f2084])).

fof(f2084,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2025])).

fof(f16175,plain,(
    r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK2) ),
    inference(unit_resulting_resolution,[],[f2066,f2067,f2068,f2072,f2070,f2069,f3926,f3945,f2103])).

fof(f2103,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_orders_2(X0,X1,X3)
      | ~ r2_orders_2(X0,X2,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f1959])).

fof(f1959,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ~ r2_orders_2(X0,X2,X3)
                  | ~ r2_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f1958])).

fof(f1958,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ~ r2_orders_2(X0,X2,X3)
                  | ~ r2_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1897])).

fof(f1897,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r2_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_orders_2)).

fof(f3945,plain,(
    r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f3944,f2064])).

fof(f3944,plain,
    ( r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3943,f2065])).

fof(f3943,plain,
    ( r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3942,f2066])).

fof(f3942,plain,
    ( r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3941,f2067])).

fof(f3941,plain,
    ( r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3940,f2068])).

fof(f3940,plain,
    ( r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3939,f3926])).

fof(f3939,plain,
    ( r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1)
    | ~ m1_subset_1(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3938,f2069])).

fof(f3938,plain,
    ( r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3933,f2071])).

fof(f3933,plain,
    ( r2_orders_2(sK0,sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(k3_orders_2(sK0,sK3,sK1),k3_orders_2(sK0,sK3,sK2)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f2272,f2097])).

fof(f2097,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2033])).

fof(f2072,plain,(
    r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f2016])).
%------------------------------------------------------------------------------
