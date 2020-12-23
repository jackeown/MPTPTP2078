%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1140+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:09 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 280 expanded)
%              Number of leaves         :    8 ( 120 expanded)
%              Depth                    :   21
%              Number of atoms          :  275 (2404 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2067,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2058,f1990])).

fof(f1990,plain,(
    ~ r2_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f1989,f1932])).

fof(f1932,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f1909])).

fof(f1909,plain,
    ( ~ r2_orders_2(sK0,sK1,sK3)
    & r2_orders_2(sK0,sK2,sK3)
    & r2_orders_2(sK0,sK1,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f1882,f1908,f1907,f1906,f1905])).

fof(f1905,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_orders_2(X0,X1,X3)
                    & r2_orders_2(X0,X2,X3)
                    & r2_orders_2(X0,X1,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(sK0,X1,X3)
                  & r2_orders_2(sK0,X2,X3)
                  & r2_orders_2(sK0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1906,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_orders_2(sK0,X1,X3)
                & r2_orders_2(sK0,X2,X3)
                & r2_orders_2(sK0,X1,X2)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_orders_2(sK0,sK1,X3)
              & r2_orders_2(sK0,X2,X3)
              & r2_orders_2(sK0,sK1,X2)
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f1907,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_orders_2(sK0,sK1,X3)
            & r2_orders_2(sK0,X2,X3)
            & r2_orders_2(sK0,sK1,X2)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ~ r2_orders_2(sK0,sK1,X3)
          & r2_orders_2(sK0,sK2,X3)
          & r2_orders_2(sK0,sK1,sK2)
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f1908,plain,
    ( ? [X3] :
        ( ~ r2_orders_2(sK0,sK1,X3)
        & r2_orders_2(sK0,sK2,X3)
        & r2_orders_2(sK0,sK1,sK2)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r2_orders_2(sK0,sK1,sK3)
      & r2_orders_2(sK0,sK2,sK3)
      & r2_orders_2(sK0,sK1,sK2)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f1882,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & r2_orders_2(X0,X2,X3)
                  & r2_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f1881])).

fof(f1881,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & r2_orders_2(X0,X2,X3)
                  & r2_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1879])).

fof(f1879,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f1878])).

fof(f1878,conjecture,(
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

fof(f1989,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f1987,f1931])).

fof(f1931,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f1909])).

fof(f1987,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_orders_2(sK0,sK2,sK1) ),
    inference(resolution,[],[f1977,f1934])).

fof(f1934,plain,(
    r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f1909])).

fof(f1977,plain,(
    ! [X0,X1] :
      ( ~ r2_orders_2(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f1976,f1930])).

fof(f1930,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f1909])).

fof(f1976,plain,(
    ! [X0,X1] :
      ( ~ r2_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ r2_orders_2(sK0,X1,X0) ) ),
    inference(resolution,[],[f1938,f1929])).

fof(f1929,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f1909])).

fof(f1938,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f1886])).

fof(f1886,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f1885])).

fof(f1885,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1877])).

fof(f1877,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r2_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_orders_2)).

fof(f2058,plain,(
    r2_orders_2(sK0,sK2,sK1) ),
    inference(backward_demodulation,[],[f1935,f2056])).

fof(f2056,plain,(
    sK1 = sK3 ),
    inference(subsumption_resolution,[],[f2055,f1930])).

fof(f2055,plain,
    ( sK1 = sK3
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f2054,f1931])).

fof(f2054,plain,
    ( sK1 = sK3
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f2053,f1933])).

fof(f1933,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f1909])).

fof(f2053,plain,
    ( sK1 = sK3
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f2048,f1936])).

fof(f1936,plain,(
    ~ r2_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f1909])).

fof(f2048,plain,
    ( sK1 = sK3
    | r2_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f2035,f1941])).

fof(f1941,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | X1 = X2
      | r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f1911,plain,(
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
    inference(flattening,[],[f1910])).

fof(f1910,plain,(
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
    inference(nnf_transformation,[],[f1887])).

fof(f1887,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1861])).

fof(f1861,axiom,(
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

fof(f2035,plain,(
    r1_orders_2(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f2034,f1931])).

fof(f2034,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK3) ),
    inference(resolution,[],[f2011,f1973])).

fof(f1973,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f1972,f1931])).

fof(f1972,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f1970,f1932])).

fof(f1970,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f1968,f1934])).

fof(f1968,plain,(
    ! [X0,X1] :
      ( ~ r2_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X1) ) ),
    inference(resolution,[],[f1939,f1930])).

fof(f1939,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f1911])).

fof(f2011,plain,(
    ! [X1] :
      ( ~ r1_orders_2(sK0,X1,sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,sK3) ) ),
    inference(subsumption_resolution,[],[f2010,f1932])).

fof(f2010,plain,(
    ! [X1] :
      ( ~ r1_orders_2(sK0,X1,sK2)
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,sK3) ) ),
    inference(subsumption_resolution,[],[f2007,f1933])).

fof(f2007,plain,(
    ! [X1] :
      ( ~ r1_orders_2(sK0,X1,sK2)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,sK3) ) ),
    inference(resolution,[],[f1999,f1975])).

fof(f1975,plain,(
    r1_orders_2(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f1974,f1932])).

fof(f1974,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f1971,f1933])).

fof(f1971,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK3) ),
    inference(resolution,[],[f1968,f1935])).

fof(f1999,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ r1_orders_2(sK0,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_orders_2(sK0,X2,X1) ) ),
    inference(subsumption_resolution,[],[f1998,f1930])).

fof(f1998,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ r1_orders_2(sK0,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r1_orders_2(sK0,X2,X1) ) ),
    inference(resolution,[],[f1959,f1928])).

fof(f1928,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f1909])).

fof(f1959,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f1903])).

fof(f1903,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f1902])).

fof(f1902,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1876])).

fof(f1876,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

fof(f1935,plain,(
    r2_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f1909])).
%------------------------------------------------------------------------------
