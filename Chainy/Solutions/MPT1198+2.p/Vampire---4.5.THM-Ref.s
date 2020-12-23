%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1198+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:11 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 260 expanded)
%              Number of leaves         :   10 ( 112 expanded)
%              Depth                    :   19
%              Number of atoms          :  286 (2225 expanded)
%              Number of equality atoms :   42 (  55 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2358,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2357,f2130])).

fof(f2130,plain,(
    ~ r1_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f2093])).

fof(f2093,plain,
    ( ~ r1_lattices(sK0,sK1,sK3)
    & r1_lattices(sK0,sK2,sK3)
    & r1_lattices(sK0,sK1,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l2_lattices(sK0)
    & v5_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f2058,f2092,f2091,f2090,f2089])).

fof(f2089,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r1_lattices(X0,X2,X3)
                    & r1_lattices(X0,X1,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l2_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(sK0,X1,X3)
                  & r1_lattices(sK0,X2,X3)
                  & r1_lattices(sK0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l2_lattices(sK0)
      & v5_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2090,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_lattices(sK0,X1,X3)
                & r1_lattices(sK0,X2,X3)
                & r1_lattices(sK0,X1,X2)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(sK0,sK1,X3)
              & r1_lattices(sK0,X2,X3)
              & r1_lattices(sK0,sK1,X2)
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2091,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_lattices(sK0,sK1,X3)
            & r1_lattices(sK0,X2,X3)
            & r1_lattices(sK0,sK1,X2)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ~ r1_lattices(sK0,sK1,X3)
          & r1_lattices(sK0,sK2,X3)
          & r1_lattices(sK0,sK1,sK2)
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2092,plain,
    ( ? [X3] :
        ( ~ r1_lattices(sK0,sK1,X3)
        & r1_lattices(sK0,sK2,X3)
        & r1_lattices(sK0,sK1,sK2)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r1_lattices(sK0,sK1,sK3)
      & r1_lattices(sK0,sK2,sK3)
      & r1_lattices(sK0,sK1,sK2)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2058,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X1,X3)
                  & r1_lattices(X0,X2,X3)
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l2_lattices(X0)
      & v5_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2057])).

fof(f2057,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X1,X3)
                  & r1_lattices(X0,X2,X3)
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l2_lattices(X0)
      & v5_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2044])).

fof(f2044,negated_conjecture,(
    ~ ! [X0] :
        ( ( l2_lattices(X0)
          & v5_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_lattices(X0,X2,X3)
                        & r1_lattices(X0,X1,X2) )
                     => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2043])).

fof(f2043,conjecture,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_lattices(X0,X2,X3)
                      & r1_lattices(X0,X1,X2) )
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_lattices)).

fof(f2357,plain,(
    r1_lattices(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f2356,f2125])).

fof(f2125,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2093])).

fof(f2356,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f2355,f2127])).

fof(f2127,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2093])).

fof(f2355,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f2353])).

fof(f2353,plain,
    ( sK3 != sK3
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,sK3) ),
    inference(superposition,[],[f2174,f2352])).

fof(f2352,plain,(
    sK3 = k1_lattices(sK0,sK1,sK3) ),
    inference(forward_demodulation,[],[f2351,f2180])).

fof(f2180,plain,(
    sK3 = k1_lattices(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f2179,f2126])).

fof(f2126,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2093])).

fof(f2179,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK3 = k1_lattices(sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f2176,f2127])).

fof(f2176,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK3 = k1_lattices(sK0,sK2,sK3) ),
    inference(resolution,[],[f2173,f2129])).

fof(f2129,plain,(
    r1_lattices(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f2093])).

fof(f2173,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,X0,X1) = X1 ) ),
    inference(subsumption_resolution,[],[f2171,f2122])).

fof(f2122,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2093])).

fof(f2171,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,X0,X1) = X1
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2124,f2131])).

fof(f2131,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = X2
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2094])).

fof(f2094,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2060])).

fof(f2060,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2059])).

fof(f2059,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2015])).

fof(f2015,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

fof(f2124,plain,(
    l2_lattices(sK0) ),
    inference(cnf_transformation,[],[f2093])).

fof(f2351,plain,(
    k1_lattices(sK0,sK2,sK3) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK3)) ),
    inference(forward_demodulation,[],[f2342,f2178])).

fof(f2178,plain,(
    sK2 = k1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f2177,f2125])).

fof(f2177,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK2 = k1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f2175,f2126])).

fof(f2175,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK2 = k1_lattices(sK0,sK1,sK2) ),
    inference(resolution,[],[f2173,f2128])).

fof(f2128,plain,(
    r1_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f2093])).

fof(f2342,plain,(
    k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k1_lattices(sK0,sK1,sK2),sK3) ),
    inference(resolution,[],[f2200,f2126])).

fof(f2200,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | k1_lattices(sK0,sK1,k1_lattices(sK0,X5,sK3)) = k1_lattices(sK0,k1_lattices(sK0,sK1,X5),sK3) ) ),
    inference(resolution,[],[f2188,f2127])).

fof(f2188,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k1_lattices(sK0,sK1,k1_lattices(sK0,X4,X5)) = k1_lattices(sK0,k1_lattices(sK0,sK1,X4),X5) ) ),
    inference(resolution,[],[f2170,f2125])).

fof(f2170,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,X2,k1_lattices(sK0,X1,X0)) = k1_lattices(sK0,k1_lattices(sK0,X2,X1),X0) ) ),
    inference(global_subsumption,[],[f2124,f2169])).

fof(f2169,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k1_lattices(sK0,X2,k1_lattices(sK0,X1,X0)) = k1_lattices(sK0,k1_lattices(sK0,X2,X1),X0)
      | ~ l2_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f2168,f2122])).

fof(f2168,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k1_lattices(sK0,X2,k1_lattices(sK0,X1,X0)) = k1_lattices(sK0,k1_lattices(sK0,X2,X1),X0)
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2123,f2163])).

fof(f2163,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v5_lattices(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2121])).

fof(f2121,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ( k1_lattices(X0,sK12(X0),k1_lattices(X0,sK13(X0),sK14(X0))) != k1_lattices(X0,k1_lattices(X0,sK12(X0),sK13(X0)),sK14(X0))
            & m1_subset_1(sK14(X0),u1_struct_0(X0))
            & m1_subset_1(sK13(X0),u1_struct_0(X0))
            & m1_subset_1(sK12(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14])],[f2117,f2120,f2119,f2118])).

fof(f2118,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k1_lattices(X0,sK12(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,sK12(X0),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK12(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2119,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k1_lattices(X0,sK12(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,sK12(X0),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k1_lattices(X0,sK12(X0),k1_lattices(X0,sK13(X0),X3)) != k1_lattices(X0,k1_lattices(X0,sK12(X0),sK13(X0)),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK13(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2120,plain,(
    ! [X0] :
      ( ? [X3] :
          ( k1_lattices(X0,sK12(X0),k1_lattices(X0,sK13(X0),X3)) != k1_lattices(X0,k1_lattices(X0,sK12(X0),sK13(X0)),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_lattices(X0,sK12(X0),k1_lattices(X0,sK13(X0),sK14(X0))) != k1_lattices(X0,k1_lattices(X0,sK12(X0),sK13(X0)),sK14(X0))
        & m1_subset_1(sK14(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2117,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f2116])).

fof(f2116,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2088])).

fof(f2088,plain,(
    ! [X0] :
      ( ( v5_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2087])).

fof(f2087,plain,(
    ! [X0] :
      ( ( v5_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2016])).

fof(f2016,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_lattices)).

fof(f2123,plain,(
    v5_lattices(sK0) ),
    inference(cnf_transformation,[],[f2093])).

fof(f2174,plain,(
    ! [X2,X3] :
      ( k1_lattices(sK0,X2,X3) != X3
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattices(sK0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f2172,f2122])).

fof(f2172,plain,(
    ! [X2,X3] :
      ( k1_lattices(sK0,X2,X3) != X3
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattices(sK0,X2,X3)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2124,f2132])).

fof(f2132,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2094])).
%------------------------------------------------------------------------------
