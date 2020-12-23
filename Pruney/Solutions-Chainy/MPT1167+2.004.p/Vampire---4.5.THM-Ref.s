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
% DateTime   : Thu Dec  3 13:10:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  118 (2594 expanded)
%              Number of leaves         :   10 (1235 expanded)
%              Depth                    :   44
%              Number of atoms          :  870 (35572 expanded)
%              Number of equality atoms :   99 ( 765 expanded)
%              Maximal formula depth    :   17 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f450,plain,(
    $false ),
    inference(subsumption_resolution,[],[f424,f326])).

fof(f326,plain,(
    r2_hidden(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f36,f324])).

fof(f324,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f323,f26])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r2_hidden(sK1,sK4)
    & m1_orders_2(sK4,sK0,sK3)
    & r2_hidden(sK2,sK4)
    & r2_hidden(sK1,sK3)
    & r2_orders_2(sK0,sK1,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f7,f18,f17,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(X1,X4)
                        & m1_orders_2(X4,X0,X3)
                        & r2_hidden(X2,X4)
                        & r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
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
                  ( ? [X4] :
                      ( ~ r2_hidden(X1,X4)
                      & m1_orders_2(X4,sK0,X3)
                      & r2_hidden(X2,X4)
                      & r2_hidden(X1,X3)
                      & r2_orders_2(sK0,X1,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ r2_hidden(X1,X4)
                    & m1_orders_2(X4,sK0,X3)
                    & r2_hidden(X2,X4)
                    & r2_hidden(X1,X3)
                    & r2_orders_2(sK0,X1,X2)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(sK1,X4)
                  & m1_orders_2(X4,sK0,X3)
                  & r2_hidden(X2,X4)
                  & r2_hidden(sK1,X3)
                  & r2_orders_2(sK0,sK1,X2)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ r2_hidden(sK1,X4)
                & m1_orders_2(X4,sK0,X3)
                & r2_hidden(X2,X4)
                & r2_hidden(sK1,X3)
                & r2_orders_2(sK0,sK1,X2)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_hidden(sK1,X4)
              & m1_orders_2(X4,sK0,X3)
              & r2_hidden(sK2,X4)
              & r2_hidden(sK1,X3)
              & r2_orders_2(sK0,sK1,sK2)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ r2_hidden(sK1,X4)
            & m1_orders_2(X4,sK0,X3)
            & r2_hidden(sK2,X4)
            & r2_hidden(sK1,X3)
            & r2_orders_2(sK0,sK1,sK2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X4] :
          ( ~ r2_hidden(sK1,X4)
          & m1_orders_2(X4,sK0,sK3)
          & r2_hidden(sK2,X4)
          & r2_hidden(sK1,sK3)
          & r2_orders_2(sK0,sK1,sK2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X4] :
        ( ~ r2_hidden(sK1,X4)
        & m1_orders_2(X4,sK0,sK3)
        & r2_hidden(sK2,X4)
        & r2_hidden(sK1,sK3)
        & r2_orders_2(sK0,sK1,sK2)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r2_hidden(sK1,sK4)
      & m1_orders_2(sK4,sK0,sK3)
      & r2_hidden(sK2,sK4)
      & r2_hidden(sK1,sK3)
      & r2_orders_2(sK0,sK1,sK2)
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_hidden(X1,X4)
                      & m1_orders_2(X4,X0,X3)
                      & r2_hidden(X2,X4)
                      & r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_hidden(X1,X4)
                      & m1_orders_2(X4,X0,X3)
                      & r2_hidden(X2,X4)
                      & r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( ( m1_orders_2(X4,X0,X3)
                            & r2_hidden(X2,X4)
                            & r2_hidden(X1,X3)
                            & r2_orders_2(X0,X1,X2) )
                         => r2_hidden(X1,X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( ( m1_orders_2(X4,X0,X3)
                          & r2_hidden(X2,X4)
                          & r2_hidden(X1,X3)
                          & r2_orders_2(X0,X1,X2) )
                       => r2_hidden(X1,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_orders_2)).

fof(f323,plain,
    ( k1_xboole_0 = sK3
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f322,f27])).

fof(f27,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f322,plain,
    ( k1_xboole_0 = sK3
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f321,f28])).

fof(f28,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f321,plain,
    ( k1_xboole_0 = sK3
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f320,f29])).

fof(f29,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f320,plain,
    ( k1_xboole_0 = sK3
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f319,f30])).

fof(f30,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f319,plain,
    ( k1_xboole_0 = sK3
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f318,f33])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f318,plain,
    ( k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f317,f34])).

fof(f34,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f317,plain,
    ( k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f316,f38])).

fof(f38,plain,(
    m1_orders_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f316,plain,
    ( k1_xboole_0 = sK3
    | ~ m1_orders_2(sK4,sK0,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f315])).

fof(f315,plain,
    ( k1_xboole_0 = sK3
    | ~ m1_orders_2(sK4,sK0,sK3)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f312,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
                    & ( ( k3_orders_2(X0,X1,sK5(X0,X1,X2)) = X2
                        & r2_hidden(sK5(X0,X1,X2),X1)
                        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK5(X0,X1,X2)) = X2
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).

fof(f312,plain,
    ( ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f311,f39])).

fof(f39,plain,(
    ~ r2_hidden(sK1,sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f311,plain,
    ( k1_xboole_0 = sK3
    | r2_hidden(sK1,sK4)
    | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f310,f36])).

fof(f310,plain,
    ( k1_xboole_0 = sK3
    | ~ r2_hidden(sK1,sK3)
    | r2_hidden(sK1,sK4)
    | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f309,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f309,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k1_xboole_0 = sK3
    | ~ r2_hidden(sK1,sK3)
    | r2_hidden(sK1,sK4)
    | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f304])).

fof(f304,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k1_xboole_0 = sK3
    | ~ r2_hidden(sK1,sK3)
    | r2_hidden(sK1,sK4)
    | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f301,f257])).

fof(f257,plain,
    ( r2_orders_2(sK0,sK1,sK5(sK0,sK3,sK4))
    | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f256,f32])).

fof(f32,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f256,plain,
    ( k1_xboole_0 = sK3
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
    | r2_orders_2(sK0,sK1,sK5(sK0,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f251,f37])).

fof(f37,plain,(
    r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f251,plain,
    ( k1_xboole_0 = sK3
    | ~ r2_hidden(sK2,sK4)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
    | r2_orders_2(sK0,sK1,sK5(sK0,sK3,sK4)) ),
    inference(resolution,[],[f248,f156])).

fof(f156,plain,(
    ! [X0] :
      ( ~ r2_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_orders_2(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f155,f32])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,sK2,X0)
      | r2_orders_2(sK0,sK1,X0) ) ),
    inference(resolution,[],[f122,f35])).

fof(f35,plain,(
    r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f122,plain,(
    ! [X4,X5] :
      ( ~ r2_orders_2(sK0,sK1,X4)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X4,X5)
      | r2_orders_2(sK0,sK1,X5) ) ),
    inference(resolution,[],[f62,f31])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X0,X1)
      | r2_orders_2(sK0,X2,X1) ) ),
    inference(subsumption_resolution,[],[f61,f28])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(sK0,X0,X1)
      | ~ r2_orders_2(sK0,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_orders_2(sK0,X2,X1)
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f55,f29])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(sK0,X0,X1)
      | ~ r2_orders_2(sK0,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_orders_2(sK0,X2,X1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(resolution,[],[f30,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_orders_2(X0,X2,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_orders_2(X0,X1,X3)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_orders_2)).

fof(f248,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4))
      | k1_xboole_0 = sK3
      | ~ r2_hidden(X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | k1_xboole_0 = sK3
      | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_xboole_0 = sK3 ) ),
    inference(superposition,[],[f246,f159])).

fof(f159,plain,
    ( sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f158,f38])).

fof(f158,plain,
    ( k1_xboole_0 = sK3
    | ~ m1_orders_2(sK4,sK0,sK3)
    | sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)) ),
    inference(resolution,[],[f130,f34])).

fof(f130,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = sK3
      | ~ m1_orders_2(X0,sK0,sK3)
      | k3_orders_2(sK0,sK3,sK5(sK0,sK3,X0)) = X0 ) ),
    inference(resolution,[],[f70,f33])).

fof(f70,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X6
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X5,sK0,X6)
      | k3_orders_2(sK0,X6,sK5(sK0,X6,X5)) = X5 ) ),
    inference(subsumption_resolution,[],[f69,f26])).

fof(f69,plain,(
    ! [X6,X5] :
      ( ~ m1_orders_2(X5,sK0,X6)
      | k1_xboole_0 = X6
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_orders_2(sK0,X6,sK5(sK0,X6,X5)) = X5
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f68,f27])).

fof(f68,plain,(
    ! [X6,X5] :
      ( ~ m1_orders_2(X5,sK0,X6)
      | k1_xboole_0 = X6
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_orders_2(sK0,X6,sK5(sK0,X6,X5)) = X5
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f67,f28])).

fof(f67,plain,(
    ! [X6,X5] :
      ( ~ m1_orders_2(X5,sK0,X6)
      | k1_xboole_0 = X6
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_orders_2(sK0,X6,sK5(sK0,X6,X5)) = X5
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f57,f29])).

fof(f57,plain,(
    ! [X6,X5] :
      ( ~ m1_orders_2(X5,sK0,X6)
      | k1_xboole_0 = X6
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_orders_2(sK0,X6,sK5(sK0,X6,X5)) = X5
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f30,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k3_orders_2(X0,X1,sK5(X0,X1,X2)) = X2
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f246,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)))
      | k1_xboole_0 = sK3
      | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f244,f38])).

fof(f244,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4))
      | ~ m1_orders_2(sK4,sK0,sK3)
      | k1_xboole_0 = sK3
      | ~ r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f211,f33])).

fof(f211,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X2,sK5(sK0,X3,sK4))
      | ~ m1_orders_2(sK4,sK0,X3)
      | k1_xboole_0 = X3
      | ~ r2_hidden(X2,k3_orders_2(sK0,sK3,sK5(sK0,X3,sK4)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f140,f34])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_orders_2(sK0,X0,sK5(sK0,X1,X2))
      | ~ m1_orders_2(X2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f139,f26])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_orders_2(sK0,X0,sK5(sK0,X1,X2))
      | ~ m1_orders_2(X2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f138,f27])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_orders_2(sK0,X0,sK5(sK0,X1,X2))
      | ~ m1_orders_2(X2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f137,f28])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_orders_2(sK0,X0,sK5(sK0,X1,X2))
      | ~ m1_orders_2(X2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f136,f29])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_orders_2(sK0,X0,sK5(sK0,X1,X2))
      | ~ m1_orders_2(X2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f133,f30])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_orders_2(sK0,X0,sK5(sK0,X1,X2))
      | ~ m1_orders_2(X2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f108,f43])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k3_orders_2(sK0,sK3,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_orders_2(sK0,X0,X1) ) ),
    inference(resolution,[],[f74,f33])).

fof(f74,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X7,k3_orders_2(sK0,X8,X9))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | r2_orders_2(sK0,X7,X9) ) ),
    inference(subsumption_resolution,[],[f73,f26])).

fof(f73,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X7,k3_orders_2(sK0,X8,X9))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | r2_orders_2(sK0,X7,X9)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f72,f27])).

fof(f72,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X7,k3_orders_2(sK0,X8,X9))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | r2_orders_2(sK0,X7,X9)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f71,f28])).

fof(f71,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X7,k3_orders_2(sK0,X8,X9))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | r2_orders_2(sK0,X7,X9)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f58,f29])).

fof(f58,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X7,k3_orders_2(sK0,X8,X9))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | r2_orders_2(sK0,X7,X9)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f30,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_orders_2(X0,X1,X2)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(f301,plain,(
    ! [X0] :
      ( ~ r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_xboole_0 = sK3
      | ~ r2_hidden(X0,sK3)
      | r2_hidden(X0,sK4) ) ),
    inference(duplicate_literal_removal,[],[f300])).

fof(f300,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_xboole_0 = sK3
      | ~ r2_hidden(X0,sK3)
      | ~ r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4))
      | k1_xboole_0 = sK3 ) ),
    inference(superposition,[],[f297,f159])).

fof(f297,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_xboole_0 = sK3
      | ~ r2_hidden(X0,sK3)
      | ~ r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4)) ) ),
    inference(subsumption_resolution,[],[f295,f38])).

fof(f295,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)))
      | ~ m1_orders_2(sK4,sK0,sK3)
      | k1_xboole_0 = sK3
      | ~ r2_hidden(X0,sK3)
      | ~ r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4)) ) ),
    inference(resolution,[],[f236,f33])).

fof(f236,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X2,k3_orders_2(sK0,sK3,sK5(sK0,X3,sK4)))
      | ~ m1_orders_2(sK4,sK0,X3)
      | k1_xboole_0 = X3
      | ~ r2_hidden(X2,sK3)
      | ~ r2_orders_2(sK0,X2,sK5(sK0,X3,sK4)) ) ),
    inference(resolution,[],[f172,f34])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_orders_2(sK0,X0,sK5(sK0,X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2)))
      | ~ m1_orders_2(X2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X0,sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f171,f26])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_orders_2(sK0,X0,sK5(sK0,X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2)))
      | ~ m1_orders_2(X2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f170,f27])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_orders_2(sK0,X0,sK5(sK0,X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2)))
      | ~ m1_orders_2(X2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f169,f28])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_orders_2(sK0,X0,sK5(sK0,X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2)))
      | ~ m1_orders_2(X2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f168,f29])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_orders_2(sK0,X0,sK5(sK0,X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2)))
      | ~ m1_orders_2(X2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f165,f30])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_orders_2(sK0,X0,sK5(sK0,X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2)))
      | ~ m1_orders_2(X2,sK0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f143,f43])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK3)
      | ~ r2_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k3_orders_2(sK0,sK3,X1)) ) ),
    inference(resolution,[],[f82,f33])).

fof(f82,plain,(
    ! [X14,X15,X13] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_orders_2(sK0,X13,X15)
      | ~ r2_hidden(X13,X14)
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | r2_hidden(X13,k3_orders_2(sK0,X14,X15)) ) ),
    inference(subsumption_resolution,[],[f81,f26])).

fof(f81,plain,(
    ! [X14,X15,X13] :
      ( ~ r2_hidden(X13,X14)
      | ~ r2_orders_2(sK0,X13,X15)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | r2_hidden(X13,k3_orders_2(sK0,X14,X15))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f80,f27])).

fof(f80,plain,(
    ! [X14,X15,X13] :
      ( ~ r2_hidden(X13,X14)
      | ~ r2_orders_2(sK0,X13,X15)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | r2_hidden(X13,k3_orders_2(sK0,X14,X15))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f79,f28])).

fof(f79,plain,(
    ! [X14,X15,X13] :
      ( ~ r2_hidden(X13,X14)
      | ~ r2_orders_2(sK0,X13,X15)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | r2_hidden(X13,k3_orders_2(sK0,X14,X15))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f60,f29])).

fof(f60,plain,(
    ! [X14,X15,X13] :
      ( ~ r2_hidden(X13,X14)
      | ~ r2_orders_2(sK0,X13,X15)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | r2_hidden(X13,k3_orders_2(sK0,X14,X15))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f30,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X1,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f424,plain,(
    ~ r2_hidden(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f39,f403])).

fof(f403,plain,(
    k1_xboole_0 = sK4 ),
    inference(unit_resulting_resolution,[],[f26,f27,f28,f29,f30,f327,f34,f325,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X2
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f325,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f33,f324])).

fof(f327,plain,(
    m1_orders_2(sK4,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f38,f324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:37:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (32513)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (32523)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (32514)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (32521)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (32522)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (32522)Refutation not found, incomplete strategy% (32522)------------------------------
% 0.22/0.50  % (32522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (32522)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (32522)Memory used [KB]: 10618
% 0.22/0.50  % (32522)Time elapsed: 0.085 s
% 0.22/0.50  % (32522)------------------------------
% 0.22/0.50  % (32522)------------------------------
% 0.22/0.50  % (32515)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (32523)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f450,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f424,f326])).
% 0.22/0.50  fof(f326,plain,(
% 0.22/0.50    r2_hidden(sK1,k1_xboole_0)),
% 0.22/0.50    inference(backward_demodulation,[],[f36,f324])).
% 0.22/0.50  fof(f324,plain,(
% 0.22/0.50    k1_xboole_0 = sK3),
% 0.22/0.50    inference(subsumption_resolution,[],[f323,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ((((~r2_hidden(sK1,sK4) & m1_orders_2(sK4,sK0,sK3) & r2_hidden(sK2,sK4) & r2_hidden(sK1,sK3) & r2_orders_2(sK0,sK1,sK2) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f7,f18,f17,f16,f15,f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,sK0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(sK0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,sK0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(sK0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(sK1,X4) & m1_orders_2(X4,sK0,X3) & r2_hidden(X2,X4) & r2_hidden(sK1,X3) & r2_orders_2(sK0,sK1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ? [X2] : (? [X3] : (? [X4] : (~r2_hidden(sK1,X4) & m1_orders_2(X4,sK0,X3) & r2_hidden(X2,X4) & r2_hidden(sK1,X3) & r2_orders_2(sK0,sK1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,u1_struct_0(sK0))) => (? [X3] : (? [X4] : (~r2_hidden(sK1,X4) & m1_orders_2(X4,sK0,X3) & r2_hidden(sK2,X4) & r2_hidden(sK1,X3) & r2_orders_2(sK0,sK1,sK2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ? [X3] : (? [X4] : (~r2_hidden(sK1,X4) & m1_orders_2(X4,sK0,X3) & r2_hidden(sK2,X4) & r2_hidden(sK1,X3) & r2_orders_2(sK0,sK1,sK2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X4] : (~r2_hidden(sK1,X4) & m1_orders_2(X4,sK0,sK3) & r2_hidden(sK2,X4) & r2_hidden(sK1,sK3) & r2_orders_2(sK0,sK1,sK2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X4] : (~r2_hidden(sK1,X4) & m1_orders_2(X4,sK0,sK3) & r2_hidden(sK2,X4) & r2_hidden(sK1,sK3) & r2_orders_2(sK0,sK1,sK2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r2_hidden(sK1,sK4) & m1_orders_2(sK4,sK0,sK3) & r2_hidden(sK2,sK4) & r2_hidden(sK1,sK3) & r2_orders_2(sK0,sK1,sK2) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f7,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f6])).
% 0.22/0.50  fof(f6,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_hidden(X1,X4) & (m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) => r2_hidden(X1,X4)))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f4])).
% 0.22/0.50  fof(f4,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) => r2_hidden(X1,X4)))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_orders_2)).
% 0.22/0.50  fof(f323,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f322,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    v3_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f322,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f321,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    v4_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f321,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f320,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    v5_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f320,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f319,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    l1_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f319,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f318,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f318,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f317,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f317,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f316,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    m1_orders_2(sK4,sK0,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f316,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | ~m1_orders_2(sK4,sK0,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f315])).
% 0.22/0.50  fof(f315,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | ~m1_orders_2(sK4,sK0,sK3) | k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f312,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((k3_orders_2(X0,X1,sK5(X0,X1,X2)) = X2 & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (k3_orders_2(X0,X1,sK5(X0,X1,X2)) = X2 & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(rectify,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).
% 0.22/0.50  fof(f312,plain,(
% 0.22/0.50    ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | k1_xboole_0 = sK3),
% 0.22/0.50    inference(subsumption_resolution,[],[f311,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ~r2_hidden(sK1,sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f311,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | r2_hidden(sK1,sK4) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f310,f36])).
% 0.22/0.50  fof(f310,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | ~r2_hidden(sK1,sK3) | r2_hidden(sK1,sK4) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f309,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f309,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | k1_xboole_0 = sK3 | ~r2_hidden(sK1,sK3) | r2_hidden(sK1,sK4) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f304])).
% 0.22/0.50  fof(f304,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | k1_xboole_0 = sK3 | ~r2_hidden(sK1,sK3) | r2_hidden(sK1,sK4) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | k1_xboole_0 = sK3),
% 0.22/0.50    inference(resolution,[],[f301,f257])).
% 0.22/0.50  fof(f257,plain,(
% 0.22/0.50    r2_orders_2(sK0,sK1,sK5(sK0,sK3,sK4)) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | k1_xboole_0 = sK3),
% 0.22/0.50    inference(subsumption_resolution,[],[f256,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f256,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | r2_orders_2(sK0,sK1,sK5(sK0,sK3,sK4))),
% 0.22/0.50    inference(subsumption_resolution,[],[f251,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    r2_hidden(sK2,sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f251,plain,(
% 0.22/0.50    k1_xboole_0 = sK3 | ~r2_hidden(sK2,sK4) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | r2_orders_2(sK0,sK1,sK5(sK0,sK3,sK4))),
% 0.22/0.50    inference(resolution,[],[f248,f156])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,sK1,X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f155,f32])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK2,X0) | r2_orders_2(sK0,sK1,X0)) )),
% 0.22/0.50    inference(resolution,[],[f122,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    r2_orders_2(sK0,sK1,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    ( ! [X4,X5] : (~r2_orders_2(sK0,sK1,X4) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X4,X5) | r2_orders_2(sK0,sK1,X5)) )),
% 0.22/0.50    inference(resolution,[],[f62,f31])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X0,X1) | r2_orders_2(sK0,X2,X1)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f61,f28])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_orders_2(sK0,X0,X1) | ~r2_orders_2(sK0,X2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_orders_2(sK0,X2,X1) | ~v4_orders_2(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f55,f29])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_orders_2(sK0,X0,X1) | ~r2_orders_2(sK0,X2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_orders_2(sK0,X2,X1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f30,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r2_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_orders_2(X0,X1,X3) | ~v5_orders_2(X0) | ~v4_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_orders_2(X0,X1,X3) | ~r2_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_orders_2(X0,X1,X3) | (~r2_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2)) => r2_orders_2(X0,X1,X3))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_orders_2)).
% 0.22/0.50  fof(f248,plain,(
% 0.22/0.50    ( ! [X0] : (r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4)) | k1_xboole_0 = sK3 | ~r2_hidden(X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f247])).
% 0.22/0.51  fof(f247,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,sK4) | k1_xboole_0 = sK3 | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_xboole_0 = sK3) )),
% 0.22/0.51    inference(superposition,[],[f246,f159])).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)) | k1_xboole_0 = sK3),
% 0.22/0.51    inference(subsumption_resolution,[],[f158,f38])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    k1_xboole_0 = sK3 | ~m1_orders_2(sK4,sK0,sK3) | sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))),
% 0.22/0.51    inference(resolution,[],[f130,f34])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | ~m1_orders_2(X0,sK0,sK3) | k3_orders_2(sK0,sK3,sK5(sK0,sK3,X0)) = X0) )),
% 0.22/0.51    inference(resolution,[],[f70,f33])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X6,X5] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X6 | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X5,sK0,X6) | k3_orders_2(sK0,X6,sK5(sK0,X6,X5)) = X5) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f69,f26])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X6,X5] : (~m1_orders_2(X5,sK0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | k3_orders_2(sK0,X6,sK5(sK0,X6,X5)) = X5 | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f68,f27])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X6,X5] : (~m1_orders_2(X5,sK0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | k3_orders_2(sK0,X6,sK5(sK0,X6,X5)) = X5 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f67,f28])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X6,X5] : (~m1_orders_2(X5,sK0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | k3_orders_2(sK0,X6,sK5(sK0,X6,X5)) = X5 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f57,f29])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X6,X5] : (~m1_orders_2(X5,sK0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | k3_orders_2(sK0,X6,sK5(sK0,X6,X5)) = X5 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f30,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k3_orders_2(X0,X1,sK5(X0,X1,X2)) = X2 | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f246,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))) | k1_xboole_0 = sK3 | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f244,f38])).
% 0.22/0.51  fof(f244,plain,(
% 0.22/0.51    ( ! [X0] : (r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4)) | ~m1_orders_2(sK4,sK0,sK3) | k1_xboole_0 = sK3 | ~r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.51    inference(resolution,[],[f211,f33])).
% 0.22/0.51  fof(f211,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X2,sK5(sK0,X3,sK4)) | ~m1_orders_2(sK4,sK0,X3) | k1_xboole_0 = X3 | ~r2_hidden(X2,k3_orders_2(sK0,sK3,sK5(sK0,X3,sK4))) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 0.22/0.51    inference(resolution,[],[f140,f34])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_orders_2(X2,sK0,X1) | k1_xboole_0 = X1 | ~r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f139,f26])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_orders_2(X2,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f138,f27])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_orders_2(X2,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f137,f28])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_orders_2(X2,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f136,f29])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_orders_2(X2,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f133,f30])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_orders_2(X2,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f108,f43])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,k3_orders_2(sK0,sK3,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,X1)) )),
% 0.22/0.51    inference(resolution,[],[f74,f33])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X8,X7,X9] : (~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X7,k3_orders_2(sK0,X8,X9)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_orders_2(sK0,X7,X9)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f73,f26])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X8,X7,X9] : (~r2_hidden(X7,k3_orders_2(sK0,X8,X9)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_orders_2(sK0,X7,X9) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f72,f27])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X8,X7,X9] : (~r2_hidden(X7,k3_orders_2(sK0,X8,X9)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_orders_2(sK0,X7,X9) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f71,f28])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X8,X7,X9] : (~r2_hidden(X7,k3_orders_2(sK0,X8,X9)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_orders_2(sK0,X7,X9) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f58,f29])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X8,X7,X9] : (~r2_hidden(X7,k3_orders_2(sK0,X8,X9)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_orders_2(sK0,X7,X9) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f30,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_orders_2(X0,X1,X2) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).
% 0.22/0.51  fof(f301,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_xboole_0 = sK3 | ~r2_hidden(X0,sK3) | r2_hidden(X0,sK4)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f300])).
% 0.22/0.51  fof(f300,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_xboole_0 = sK3 | ~r2_hidden(X0,sK3) | ~r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4)) | k1_xboole_0 = sK3) )),
% 0.22/0.51    inference(superposition,[],[f297,f159])).
% 0.22/0.51  fof(f297,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_xboole_0 = sK3 | ~r2_hidden(X0,sK3) | ~r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f295,f38])).
% 0.22/0.51  fof(f295,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))) | ~m1_orders_2(sK4,sK0,sK3) | k1_xboole_0 = sK3 | ~r2_hidden(X0,sK3) | ~r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4))) )),
% 0.22/0.51    inference(resolution,[],[f236,f33])).
% 0.22/0.51  fof(f236,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_hidden(X2,k3_orders_2(sK0,sK3,sK5(sK0,X3,sK4))) | ~m1_orders_2(sK4,sK0,X3) | k1_xboole_0 = X3 | ~r2_hidden(X2,sK3) | ~r2_orders_2(sK0,X2,sK5(sK0,X3,sK4))) )),
% 0.22/0.51    inference(resolution,[],[f172,f34])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2))) | ~m1_orders_2(X2,sK0,X1) | k1_xboole_0 = X1 | ~r2_hidden(X0,sK3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f171,f26])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK3) | ~r2_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2))) | ~m1_orders_2(X2,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f170,f27])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK3) | ~r2_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2))) | ~m1_orders_2(X2,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f169,f28])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK3) | ~r2_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2))) | ~m1_orders_2(X2,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f168,f29])).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK3) | ~r2_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2))) | ~m1_orders_2(X2,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f165,f30])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK3) | ~r2_orders_2(sK0,X0,sK5(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k3_orders_2(sK0,sK3,sK5(sK0,X1,X2))) | ~m1_orders_2(X2,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f143,f43])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,sK3) | ~r2_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k3_orders_2(sK0,sK3,X1))) )),
% 0.22/0.51    inference(resolution,[],[f82,f33])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ( ! [X14,X15,X13] : (~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,X13,X15) | ~r2_hidden(X13,X14) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X13,u1_struct_0(sK0)) | r2_hidden(X13,k3_orders_2(sK0,X14,X15))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f81,f26])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X14,X15,X13] : (~r2_hidden(X13,X14) | ~r2_orders_2(sK0,X13,X15) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X13,u1_struct_0(sK0)) | r2_hidden(X13,k3_orders_2(sK0,X14,X15)) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f80,f27])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X14,X15,X13] : (~r2_hidden(X13,X14) | ~r2_orders_2(sK0,X13,X15) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X13,u1_struct_0(sK0)) | r2_hidden(X13,k3_orders_2(sK0,X14,X15)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f79,f28])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X14,X15,X13] : (~r2_hidden(X13,X14) | ~r2_orders_2(sK0,X13,X15) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X13,u1_struct_0(sK0)) | r2_hidden(X13,k3_orders_2(sK0,X14,X15)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f60,f29])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X14,X15,X13] : (~r2_hidden(X13,X14) | ~r2_orders_2(sK0,X13,X15) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X15,u1_struct_0(sK0)) | ~m1_subset_1(X13,u1_struct_0(sK0)) | r2_hidden(X13,k3_orders_2(sK0,X14,X15)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f30,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    r2_hidden(sK1,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f424,plain,(
% 0.22/0.51    ~r2_hidden(sK1,k1_xboole_0)),
% 0.22/0.51    inference(backward_demodulation,[],[f39,f403])).
% 0.22/0.51  fof(f403,plain,(
% 0.22/0.51    k1_xboole_0 = sK4),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f26,f27,f28,f29,f30,f327,f34,f325,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X2,X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X2 | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f325,plain,(
% 0.22/0.51    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(backward_demodulation,[],[f33,f324])).
% 0.22/0.51  fof(f327,plain,(
% 0.22/0.51    m1_orders_2(sK4,sK0,k1_xboole_0)),
% 0.22/0.51    inference(backward_demodulation,[],[f38,f324])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (32523)------------------------------
% 0.22/0.51  % (32523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (32523)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (32523)Memory used [KB]: 6524
% 0.22/0.51  % (32523)Time elapsed: 0.029 s
% 0.22/0.51  % (32523)------------------------------
% 0.22/0.51  % (32523)------------------------------
% 0.22/0.51  % (32510)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (32508)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (32507)Success in time 0.143 s
%------------------------------------------------------------------------------
