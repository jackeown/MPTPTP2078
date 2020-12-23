%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  142 (3776 expanded)
%              Number of leaves         :   19 (1387 expanded)
%              Depth                    :   32
%              Number of atoms          :  745 (39585 expanded)
%              Number of equality atoms :   69 ( 267 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f543,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f276,f470,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f470,plain,(
    ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f244,f462])).

fof(f462,plain,(
    k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f426,f461])).

fof(f461,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f460,f456])).

fof(f456,plain,(
    m1_orders_2(sK2,sK0,sK2) ),
    inference(subsumption_resolution,[],[f455,f98])).

fof(f98,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(f455,plain,
    ( r2_xboole_0(sK2,sK2)
    | m1_orders_2(sK2,sK0,sK2) ),
    inference(forward_demodulation,[],[f428,f426])).

fof(f428,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | r2_xboole_0(sK2,sK3) ),
    inference(backward_demodulation,[],[f82,f426])).

fof(f82,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,
    ( ( ~ m1_orders_2(sK2,sK0,sK3)
      | ~ r2_xboole_0(sK2,sK3) )
    & ( m1_orders_2(sK2,sK0,sK3)
      | r2_xboole_0(sK2,sK3) )
    & m2_orders_2(sK3,sK0,sK1)
    & m2_orders_2(sK2,sK0,sK1)
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f58,f62,f61,f60,f59])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_orders_2(X2,X0,X3)
                      | ~ r2_xboole_0(X2,X3) )
                    & ( m1_orders_2(X2,X0,X3)
                      | r2_xboole_0(X2,X3) )
                    & m2_orders_2(X3,X0,X1) )
                & m2_orders_2(X2,X0,X1) )
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,sK0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,sK0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,sK0,X1) )
              & m2_orders_2(X2,sK0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_orders_2(X2,sK0,X3)
                  | ~ r2_xboole_0(X2,X3) )
                & ( m1_orders_2(X2,sK0,X3)
                  | r2_xboole_0(X2,X3) )
                & m2_orders_2(X3,sK0,X1) )
            & m2_orders_2(X2,sK0,X1) )
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_orders_2(X2,sK0,X3)
                | ~ r2_xboole_0(X2,X3) )
              & ( m1_orders_2(X2,sK0,X3)
                | r2_xboole_0(X2,X3) )
              & m2_orders_2(X3,sK0,sK1) )
          & m2_orders_2(X2,sK0,sK1) )
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_orders_2(X2,sK0,X3)
              | ~ r2_xboole_0(X2,X3) )
            & ( m1_orders_2(X2,sK0,X3)
              | r2_xboole_0(X2,X3) )
            & m2_orders_2(X3,sK0,sK1) )
        & m2_orders_2(X2,sK0,sK1) )
   => ( ? [X3] :
          ( ( ~ m1_orders_2(sK2,sK0,X3)
            | ~ r2_xboole_0(sK2,X3) )
          & ( m1_orders_2(sK2,sK0,X3)
            | r2_xboole_0(sK2,X3) )
          & m2_orders_2(X3,sK0,sK1) )
      & m2_orders_2(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X3] :
        ( ( ~ m1_orders_2(sK2,sK0,X3)
          | ~ r2_xboole_0(sK2,X3) )
        & ( m1_orders_2(sK2,sK0,X3)
          | r2_xboole_0(sK2,X3) )
        & m2_orders_2(X3,sK0,sK1) )
   => ( ( ~ m1_orders_2(sK2,sK0,sK3)
        | ~ r2_xboole_0(sK2,sK3) )
      & ( m1_orders_2(sK2,sK0,sK3)
        | r2_xboole_0(sK2,sK3) )
      & m2_orders_2(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_orders_2(X2,X0,X1)
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X1)
                   => ( r2_xboole_0(X2,X3)
                    <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( r2_xboole_0(X2,X3)
                  <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).

fof(f460,plain,
    ( ~ m1_orders_2(sK2,sK0,sK2)
    | k1_xboole_0 = sK3 ),
    inference(forward_demodulation,[],[f459,f426])).

fof(f459,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f433,f98])).

fof(f433,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3 ),
    inference(backward_demodulation,[],[f211,f426])).

fof(f211,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3
    | r2_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f210,f74])).

fof(f74,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f210,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3
    | v2_struct_0(sK0)
    | r2_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f209,f75])).

fof(f75,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f209,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | r2_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f208,f76])).

fof(f76,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f208,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | r2_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f207,f77])).

fof(f77,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f207,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | r2_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f206,f78])).

fof(f78,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f206,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | r2_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f205,f188])).

fof(f188,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f187,f74])).

fof(f187,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f186,f75])).

% (3980)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f186,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f185,f76])).

fof(f185,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f184,f77])).

fof(f184,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f183,f78])).

fof(f183,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f176,f79])).

fof(f79,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

fof(f176,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f102,f81])).

fof(f81,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f205,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | r2_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f204,f182])).

fof(f182,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f181,f74])).

fof(f181,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f180,f75])).

fof(f180,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f179,f76])).

fof(f179,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f178,f77])).

fof(f178,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f177,f78])).

fof(f177,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f175,f79])).

fof(f175,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f102,f80])).

fof(f80,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f204,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | r2_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f94,f82])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_2(X2,X0,X1)
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
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
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

fof(f426,plain,(
    sK2 = sK3 ),
    inference(subsumption_resolution,[],[f422,f309])).

fof(f309,plain,
    ( r2_xboole_0(sK2,sK3)
    | sK2 = sK3 ),
    inference(resolution,[],[f248,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f248,plain,(
    r1_tarski(sK2,sK3) ),
    inference(resolution,[],[f174,f188])).

fof(f174,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK3) ),
    inference(subsumption_resolution,[],[f173,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f173,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f172,f74])).

fof(f172,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | r2_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f171,f75])).

fof(f171,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | r2_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f170,f76])).

fof(f170,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | r2_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f169,f77])).

fof(f169,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | r2_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f168,f78])).

fof(f168,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | r2_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f93,f82])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_2(X2,X0,X1)
      | r1_tarski(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

fof(f422,plain,
    ( sK2 = sK3
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f334,f83])).

fof(f83,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f334,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f333,f310])).

fof(f310,plain,
    ( ~ r1_tarski(sK3,sK2)
    | sK2 = sK3 ),
    inference(resolution,[],[f248,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f333,plain,
    ( sK2 = sK3
    | m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(sK3,sK2) ),
    inference(subsumption_resolution,[],[f332,f74])).

fof(f332,plain,
    ( sK2 = sK3
    | m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(sK3,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f331,f75])).

fof(f331,plain,
    ( sK2 = sK3
    | m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(sK3,sK2)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f330,f76])).

fof(f330,plain,
    ( sK2 = sK3
    | m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(sK3,sK2)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f329,f77])).

fof(f329,plain,
    ( sK2 = sK3
    | m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(sK3,sK2)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f328,f78])).

fof(f328,plain,
    ( sK2 = sK3
    | m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(sK3,sK2)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f326,f182])).

fof(f326,plain,
    ( sK2 = sK3
    | m1_orders_2(sK2,sK0,sK3)
    | r1_tarski(sK3,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f256,f93])).

fof(f256,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | sK2 = sK3
    | m1_orders_2(sK2,sK0,sK3) ),
    inference(resolution,[],[f235,f81])).

fof(f235,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | m1_orders_2(sK2,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f234,f74])).

fof(f234,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f233,f75])).

fof(f233,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f232,f76])).

fof(f232,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f231,f77])).

fof(f231,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f230,f78])).

fof(f230,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f228,f79])).

fof(f228,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f92,f80])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m2_orders_2(X3,X0,X1)
      | m1_orders_2(X3,X0,X2)
      | X2 = X3
      | m1_orders_2(X2,X0,X3)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_orders_2(X2,X0,X3)
                      | m1_orders_2(X3,X0,X2) )
                    & ( ~ m1_orders_2(X3,X0,X2)
                      | ~ m1_orders_2(X2,X0,X3) ) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).

fof(f244,plain,(
    ~ r1_xboole_0(sK2,sK2) ),
    inference(resolution,[],[f197,f80])).

fof(f197,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f196,f74])).

fof(f196,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f195,f75])).

fof(f195,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f194,f76])).

fof(f194,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f193,f77])).

fof(f193,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f192,f78])).

fof(f192,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f190,f79])).

fof(f190,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f90,f80])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m2_orders_2(X3,X0,X1)
      | ~ r1_xboole_0(X2,X3)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

fof(f276,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f128,f151])).

fof(f151,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(resolution,[],[f117,f99])).

fof(f99,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f128,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK4(X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f95,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f95,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:52:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (3983)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.51  % (3975)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.51  % (3972)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (3970)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (3969)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (3990)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (3991)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (3971)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (3976)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (3982)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (3975)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f543,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f276,f470,f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.53  fof(f470,plain,(
% 0.22/0.53    ~r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.53    inference(backward_demodulation,[],[f244,f462])).
% 0.22/0.53  fof(f462,plain,(
% 0.22/0.53    k1_xboole_0 = sK2),
% 0.22/0.53    inference(backward_demodulation,[],[f426,f461])).
% 0.22/0.53  fof(f461,plain,(
% 0.22/0.53    k1_xboole_0 = sK3),
% 0.22/0.53    inference(subsumption_resolution,[],[f460,f456])).
% 0.22/0.53  fof(f456,plain,(
% 0.22/0.53    m1_orders_2(sK2,sK0,sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f455,f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_xboole_0(X0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0] : ~r2_xboole_0(X0,X0)),
% 0.22/0.53    inference(rectify,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : ~r2_xboole_0(X0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).
% 0.22/0.53  fof(f455,plain,(
% 0.22/0.53    r2_xboole_0(sK2,sK2) | m1_orders_2(sK2,sK0,sK2)),
% 0.22/0.53    inference(forward_demodulation,[],[f428,f426])).
% 0.22/0.53  fof(f428,plain,(
% 0.22/0.53    m1_orders_2(sK2,sK0,sK2) | r2_xboole_0(sK2,sK3)),
% 0.22/0.53    inference(backward_demodulation,[],[f82,f426])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f58,f62,f61,f60,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) => (? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) => ((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f28])).
% 0.22/0.53  fof(f28,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).
% 0.22/0.53  fof(f460,plain,(
% 0.22/0.53    ~m1_orders_2(sK2,sK0,sK2) | k1_xboole_0 = sK3),
% 0.22/0.53    inference(forward_demodulation,[],[f459,f426])).
% 0.22/0.53  fof(f459,plain,(
% 0.22/0.53    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3),
% 0.22/0.53    inference(subsumption_resolution,[],[f433,f98])).
% 0.22/0.53  fof(f433,plain,(
% 0.22/0.53    r2_xboole_0(sK2,sK2) | ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3),
% 0.22/0.53    inference(backward_demodulation,[],[f211,f426])).
% 0.22/0.53  fof(f211,plain,(
% 0.22/0.53    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3 | r2_xboole_0(sK2,sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f210,f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f63])).
% 0.22/0.53  fof(f210,plain,(
% 0.22/0.53    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3 | v2_struct_0(sK0) | r2_xboole_0(sK2,sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f209,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    v3_orders_2(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f63])).
% 0.22/0.53  fof(f209,plain,(
% 0.22/0.53    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3 | ~v3_orders_2(sK0) | v2_struct_0(sK0) | r2_xboole_0(sK2,sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f208,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    v4_orders_2(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f63])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | r2_xboole_0(sK2,sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f207,f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    v5_orders_2(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f63])).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | r2_xboole_0(sK2,sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f206,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    l1_orders_2(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f63])).
% 0.22/0.53  fof(f206,plain,(
% 0.22/0.53    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3 | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | r2_xboole_0(sK2,sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f205,f188])).
% 0.22/0.53  fof(f188,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(subsumption_resolution,[],[f187,f74])).
% 0.22/0.53  fof(f187,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f186,f75])).
% 0.22/0.53  % (3980)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  fof(f186,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f185,f76])).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f184,f77])).
% 0.22/0.53  fof(f184,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f183,f78])).
% 0.22/0.53  fof(f183,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f176,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f63])).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f102,f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    m2_orders_2(sK3,sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f63])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f23])).
% 0.22/0.53  fof(f23,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | r2_xboole_0(sK2,sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f204,f182])).
% 0.22/0.53  fof(f182,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(subsumption_resolution,[],[f181,f74])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f180,f75])).
% 0.22/0.53  fof(f180,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f179,f76])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f178,f77])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f177,f78])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f175,f79])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f102,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    m2_orders_2(sK2,sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f63])).
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    ~m1_orders_2(sK3,sK0,sK2) | k1_xboole_0 = sK3 | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | r2_xboole_0(sK2,sK3)),
% 0.22/0.53    inference(resolution,[],[f94,f82])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,axiom,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).
% 0.22/0.53  fof(f426,plain,(
% 0.22/0.53    sK2 = sK3),
% 0.22/0.53    inference(subsumption_resolution,[],[f422,f309])).
% 0.22/0.53  fof(f309,plain,(
% 0.22/0.53    r2_xboole_0(sK2,sK3) | sK2 = sK3),
% 0.22/0.53    inference(resolution,[],[f248,f109])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.53    inference(flattening,[],[f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.53  fof(f248,plain,(
% 0.22/0.53    r1_tarski(sK2,sK3)),
% 0.22/0.53    inference(resolution,[],[f174,f188])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2,sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f173,f107])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f70])).
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_xboole_0(sK2,sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f172,f74])).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | r2_xboole_0(sK2,sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f171,f75])).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | r2_xboole_0(sK2,sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f170,f76])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | r2_xboole_0(sK2,sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f169,f77])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | r2_xboole_0(sK2,sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f168,f78])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | r2_xboole_0(sK2,sK3)),
% 0.22/0.53    inference(resolution,[],[f93,f82])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,axiom,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).
% 0.22/0.53  fof(f422,plain,(
% 0.22/0.53    sK2 = sK3 | ~r2_xboole_0(sK2,sK3)),
% 0.22/0.53    inference(resolution,[],[f334,f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f63])).
% 0.22/0.53  fof(f334,plain,(
% 0.22/0.53    m1_orders_2(sK2,sK0,sK3) | sK2 = sK3),
% 0.22/0.53    inference(subsumption_resolution,[],[f333,f310])).
% 0.22/0.53  fof(f310,plain,(
% 0.22/0.53    ~r1_tarski(sK3,sK2) | sK2 = sK3),
% 0.22/0.53    inference(resolution,[],[f248,f106])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f333,plain,(
% 0.22/0.53    sK2 = sK3 | m1_orders_2(sK2,sK0,sK3) | r1_tarski(sK3,sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f332,f74])).
% 0.22/0.53  fof(f332,plain,(
% 0.22/0.53    sK2 = sK3 | m1_orders_2(sK2,sK0,sK3) | r1_tarski(sK3,sK2) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f331,f75])).
% 0.22/0.53  fof(f331,plain,(
% 0.22/0.53    sK2 = sK3 | m1_orders_2(sK2,sK0,sK3) | r1_tarski(sK3,sK2) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f330,f76])).
% 0.22/0.53  fof(f330,plain,(
% 0.22/0.53    sK2 = sK3 | m1_orders_2(sK2,sK0,sK3) | r1_tarski(sK3,sK2) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f329,f77])).
% 0.22/0.53  fof(f329,plain,(
% 0.22/0.53    sK2 = sK3 | m1_orders_2(sK2,sK0,sK3) | r1_tarski(sK3,sK2) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f328,f78])).
% 0.22/0.53  fof(f328,plain,(
% 0.22/0.53    sK2 = sK3 | m1_orders_2(sK2,sK0,sK3) | r1_tarski(sK3,sK2) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f326,f182])).
% 0.22/0.53  fof(f326,plain,(
% 0.22/0.53    sK2 = sK3 | m1_orders_2(sK2,sK0,sK3) | r1_tarski(sK3,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f256,f93])).
% 0.22/0.53  fof(f256,plain,(
% 0.22/0.53    m1_orders_2(sK3,sK0,sK2) | sK2 = sK3 | m1_orders_2(sK2,sK0,sK3)),
% 0.22/0.53    inference(resolution,[],[f235,f81])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | m1_orders_2(sK2,sK0,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f234,f74])).
% 0.22/0.53  fof(f234,plain,(
% 0.22/0.53    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | ~m2_orders_2(X0,sK0,sK1) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f233,f75])).
% 0.22/0.53  fof(f233,plain,(
% 0.22/0.53    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f232,f76])).
% 0.22/0.53  fof(f232,plain,(
% 0.22/0.53    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f231,f77])).
% 0.22/0.53  fof(f231,plain,(
% 0.22/0.53    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f230,f78])).
% 0.22/0.53  fof(f230,plain,(
% 0.22/0.53    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f228,f79])).
% 0.22/0.53  fof(f228,plain,(
% 0.22/0.53    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f92,f80])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~m2_orders_2(X3,X0,X1) | m1_orders_2(X3,X0,X2) | X2 = X3 | m1_orders_2(X2,X0,X3) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,axiom,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).
% 0.22/0.53  fof(f244,plain,(
% 0.22/0.53    ~r1_xboole_0(sK2,sK2)),
% 0.22/0.53    inference(resolution,[],[f197,f80])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(X0,sK2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f196,f74])).
% 0.22/0.53  fof(f196,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~m2_orders_2(X0,sK0,sK1) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f195,f75])).
% 0.22/0.53  fof(f195,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f194,f76])).
% 0.22/0.53  fof(f194,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f193,f77])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f192,f78])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f190,f79])).
% 0.22/0.53  fof(f190,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f90,f80])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~m2_orders_2(X3,X0,X1) | ~r1_xboole_0(X2,X3) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,axiom,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).
% 0.22/0.53  fof(f276,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.53    inference(resolution,[],[f128,f151])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 0.22/0.53    inference(resolution,[],[f117,f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(X0,sK4(X0)) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(resolution,[],[f95,f116])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,axiom,(
% 0.22/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.53    inference(ennf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,axiom,(
% 0.22/0.53    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (3975)------------------------------
% 0.22/0.53  % (3975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (3975)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (3975)Memory used [KB]: 2046
% 0.22/0.53  % (3975)Time elapsed: 0.104 s
% 0.22/0.53  % (3975)------------------------------
% 0.22/0.53  % (3975)------------------------------
% 0.22/0.53  % (3978)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (3985)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (3984)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (3988)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (3974)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (3979)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (3987)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (3992)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (3997)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (3968)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (3969)Refutation not found, incomplete strategy% (3969)------------------------------
% 0.22/0.54  % (3969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (3969)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (3969)Memory used [KB]: 1791
% 0.22/0.54  % (3969)Time elapsed: 0.135 s
% 0.22/0.54  % (3969)------------------------------
% 0.22/0.54  % (3969)------------------------------
% 0.22/0.54  % (3995)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (3986)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (3973)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (3994)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (3977)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (3994)Refutation not found, incomplete strategy% (3994)------------------------------
% 0.22/0.55  % (3994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (3994)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (3994)Memory used [KB]: 6268
% 0.22/0.55  % (3994)Time elapsed: 0.141 s
% 0.22/0.55  % (3994)------------------------------
% 0.22/0.55  % (3994)------------------------------
% 0.22/0.55  % (3967)Success in time 0.191 s
%------------------------------------------------------------------------------
