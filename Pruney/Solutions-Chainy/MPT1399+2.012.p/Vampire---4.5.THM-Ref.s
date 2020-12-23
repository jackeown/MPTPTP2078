%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:13 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 215 expanded)
%              Number of leaves         :   20 (  66 expanded)
%              Depth                    :   25
%              Number of atoms          :  399 (2075 expanded)
%              Number of equality atoms :   25 ( 162 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f401,plain,(
    $false ),
    inference(subsumption_resolution,[],[f400,f49])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( k1_xboole_0 = sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK2)
            | ~ r2_hidden(sK1,X3)
            | ~ v4_pre_topc(X3,sK0)
            | ~ v3_pre_topc(X3,sK0) )
          & ( ( r2_hidden(sK1,X3)
              & v4_pre_topc(X3,sK0)
              & v3_pre_topc(X3,sK0) )
            | ~ r2_hidden(X3,sK2) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK0)
                      | ~ v3_pre_topc(X3,sK0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK0)
                        & v3_pre_topc(X3,sK0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ v4_pre_topc(X3,sK0)
                    | ~ v3_pre_topc(X3,sK0) )
                  & ( ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,sK0)
                      & v3_pre_topc(X3,sK0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(sK1,X3)
                  | ~ v4_pre_topc(X3,sK0)
                  | ~ v3_pre_topc(X3,sK0) )
                & ( ( r2_hidden(sK1,X3)
                    & v4_pre_topc(X3,sK0)
                    & v3_pre_topc(X3,sK0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( k1_xboole_0 = X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(sK1,X3)
                | ~ v4_pre_topc(X3,sK0)
                | ~ v3_pre_topc(X3,sK0) )
              & ( ( r2_hidden(sK1,X3)
                  & v4_pre_topc(X3,sK0)
                  & v3_pre_topc(X3,sK0) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( k1_xboole_0 = sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK2)
              | ~ r2_hidden(sK1,X3)
              | ~ v4_pre_topc(X3,sK0)
              | ~ v3_pre_topc(X3,sK0) )
            & ( ( r2_hidden(sK1,X3)
                & v4_pre_topc(X3,sK0)
                & v3_pre_topc(X3,sK0) )
              | ~ r2_hidden(X3,sK2) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f400,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f399,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f399,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f398,f48])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f398,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f389,f262])).

fof(f262,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f111,f128])).

fof(f128,plain,(
    ! [X2] :
      ( v2_tops_1(u1_struct_0(X2),X2)
      | ~ v1_xboole_0(u1_struct_0(X2))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f66,f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f62,f60])).

fof(f60,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tops_1)).

fof(f111,plain,(
    ! [X0] :
      ( ~ v2_tops_1(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f110,f65])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f110,plain,(
    ! [X0] :
      ( ~ v2_tops_1(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f70,f64])).

fof(f64,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v2_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v2_tops_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ~ v2_tops_1(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_tops_1)).

fof(f389,plain,(
    v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f388,f48])).

fof(f388,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f385,f49])).

fof(f385,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f373,f136])).

fof(f136,plain,(
    ! [X0] :
      ( v4_pre_topc(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f133,f57])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f133,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v4_pre_topc(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f72,f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f373,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f371,f50])).

fof(f50,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f371,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f366,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f366,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ v4_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f356,f58])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f356,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ v4_pre_topc(k1_xboole_0,sK0)
    | ~ r1_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(resolution,[],[f301,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f301,plain,
    ( r2_hidden(u1_struct_0(sK0),k1_xboole_0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ v4_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f300,f48])).

fof(f300,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | r2_hidden(u1_struct_0(sK0),k1_xboole_0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f299,f49])).

fof(f299,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | r2_hidden(u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f249,f106])).

fof(f106,plain,(
    ! [X0] :
      ( v4_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f105,f65])).

fof(f105,plain,(
    ! [X0] :
      ( v4_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f71,f64])).

fof(f71,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f249,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ v4_pre_topc(k1_xboole_0,sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | r2_hidden(u1_struct_0(sK0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f248,f49])).

fof(f248,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | r2_hidden(u1_struct_0(sK0),k1_xboole_0) ),
    inference(resolution,[],[f143,f91])).

fof(f91,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | r2_hidden(u1_struct_0(sK0),k1_xboole_0) ),
    inference(resolution,[],[f77,f83])).

fof(f77,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | r2_hidden(X3,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f55,f56])).

fof(f56,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f45])).

fof(f55,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f143,plain,(
    ! [X0] :
      ( v3_pre_topc(u1_struct_0(X0),X0)
      | ~ v4_pre_topc(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f142,f61])).

fof(f142,plain,(
    ! [X0] :
      ( v3_pre_topc(u1_struct_0(X0),X0)
      | ~ v4_pre_topc(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f67,f82])).

fof(f82,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f76,f60])).

fof(f76,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f63,f59])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f63,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:27:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (819396609)
% 0.13/0.37  ipcrm: permission denied for id (819462148)
% 0.13/0.37  ipcrm: permission denied for id (819494917)
% 0.13/0.38  ipcrm: permission denied for id (819527686)
% 0.21/0.44  ipcrm: permission denied for id (819855408)
% 0.21/0.47  ipcrm: permission denied for id (819986502)
% 0.21/0.47  ipcrm: permission denied for id (820019273)
% 0.21/0.49  ipcrm: permission denied for id (820084824)
% 0.21/0.49  ipcrm: permission denied for id (820117598)
% 0.21/0.50  ipcrm: permission denied for id (820281452)
% 0.21/0.51  ipcrm: permission denied for id (820478071)
% 0.38/0.63  % (1594)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.38/0.63  % (1600)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.38/0.63  % (1603)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.38/0.63  % (1592)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.38/0.63  % (1595)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.38/0.63  % (1607)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.38/0.63  % (1604)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.38/0.63  % (1594)Refutation found. Thanks to Tanya!
% 0.38/0.63  % SZS status Theorem for theBenchmark
% 0.38/0.63  % (1605)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.38/0.64  % (1597)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.38/0.64  % (1596)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.38/0.64  % (1602)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.38/0.64  % (1598)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.38/0.64  % SZS output start Proof for theBenchmark
% 0.38/0.64  fof(f401,plain,(
% 0.38/0.64    $false),
% 0.38/0.64    inference(subsumption_resolution,[],[f400,f49])).
% 0.38/0.64  fof(f49,plain,(
% 0.38/0.64    l1_pre_topc(sK0)),
% 0.38/0.64    inference(cnf_transformation,[],[f45])).
% 0.38/0.64  fof(f45,plain,(
% 0.38/0.64    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.38/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f44,f43,f42])).
% 0.38/0.64  fof(f42,plain,(
% 0.38/0.64    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.38/0.64    introduced(choice_axiom,[])).
% 0.38/0.64  fof(f43,plain,(
% 0.38/0.64    ? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.38/0.64    introduced(choice_axiom,[])).
% 0.38/0.64  fof(f44,plain,(
% 0.38/0.64    ? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.38/0.64    introduced(choice_axiom,[])).
% 0.38/0.64  fof(f41,plain,(
% 0.38/0.64    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.38/0.64    inference(flattening,[],[f40])).
% 0.38/0.64  fof(f40,plain,(
% 0.38/0.64    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.38/0.64    inference(nnf_transformation,[],[f22])).
% 0.38/0.64  fof(f22,plain,(
% 0.38/0.64    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.38/0.64    inference(flattening,[],[f21])).
% 0.38/0.64  fof(f21,plain,(
% 0.38/0.64    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.38/0.64    inference(ennf_transformation,[],[f20])).
% 0.38/0.64  fof(f20,negated_conjecture,(
% 0.38/0.64    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.38/0.64    inference(negated_conjecture,[],[f19])).
% 0.38/0.64  fof(f19,conjecture,(
% 0.38/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.38/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.38/0.64  fof(f400,plain,(
% 0.38/0.64    ~l1_pre_topc(sK0)),
% 0.38/0.64    inference(subsumption_resolution,[],[f399,f47])).
% 0.38/0.64  fof(f47,plain,(
% 0.38/0.64    ~v2_struct_0(sK0)),
% 0.38/0.64    inference(cnf_transformation,[],[f45])).
% 0.38/0.64  fof(f399,plain,(
% 0.38/0.64    v2_struct_0(sK0) | ~l1_pre_topc(sK0)),
% 0.38/0.64    inference(subsumption_resolution,[],[f398,f48])).
% 0.38/0.64  fof(f48,plain,(
% 0.38/0.64    v2_pre_topc(sK0)),
% 0.38/0.64    inference(cnf_transformation,[],[f45])).
% 0.38/0.64  fof(f398,plain,(
% 0.38/0.64    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0)),
% 0.38/0.64    inference(resolution,[],[f389,f262])).
% 0.38/0.64  fof(f262,plain,(
% 0.38/0.64    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.38/0.64    inference(duplicate_literal_removal,[],[f260])).
% 0.38/0.64  fof(f260,plain,(
% 0.38/0.64    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.38/0.64    inference(resolution,[],[f111,f128])).
% 0.38/0.64  fof(f128,plain,(
% 0.38/0.64    ( ! [X2] : (v2_tops_1(u1_struct_0(X2),X2) | ~v1_xboole_0(u1_struct_0(X2)) | ~l1_pre_topc(X2)) )),
% 0.38/0.64    inference(resolution,[],[f66,f83])).
% 0.38/0.64  fof(f83,plain,(
% 0.38/0.64    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.38/0.64    inference(forward_demodulation,[],[f62,f60])).
% 0.38/0.64  fof(f60,plain,(
% 0.38/0.64    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.38/0.64    inference(cnf_transformation,[],[f5])).
% 0.38/0.64  fof(f5,axiom,(
% 0.38/0.64    ! [X0] : k2_subset_1(X0) = X0),
% 0.38/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.38/0.64  fof(f62,plain,(
% 0.38/0.64    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.38/0.64    inference(cnf_transformation,[],[f6])).
% 0.38/0.64  fof(f6,axiom,(
% 0.38/0.64    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.38/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.38/0.64  fof(f66,plain,(
% 0.38/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.38/0.64    inference(cnf_transformation,[],[f26])).
% 0.38/0.64  fof(f26,plain,(
% 0.38/0.64    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.38/0.64    inference(flattening,[],[f25])).
% 0.38/0.64  fof(f25,plain,(
% 0.38/0.64    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.38/0.64    inference(ennf_transformation,[],[f16])).
% 0.38/0.64  fof(f16,axiom,(
% 0.38/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v2_tops_1(X1,X0))))),
% 0.38/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tops_1)).
% 0.38/0.64  fof(f111,plain,(
% 0.38/0.64    ( ! [X0] : (~v2_tops_1(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.38/0.64    inference(subsumption_resolution,[],[f110,f65])).
% 0.38/0.64  fof(f65,plain,(
% 0.38/0.64    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.38/0.64    inference(cnf_transformation,[],[f24])).
% 0.38/0.64  fof(f24,plain,(
% 0.38/0.64    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.38/0.64    inference(ennf_transformation,[],[f14])).
% 0.38/0.64  fof(f14,axiom,(
% 0.38/0.64    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.38/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.38/0.64  fof(f110,plain,(
% 0.38/0.64    ( ! [X0] : (~v2_tops_1(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.38/0.64    inference(superposition,[],[f70,f64])).
% 0.38/0.64  fof(f64,plain,(
% 0.38/0.64    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.38/0.64    inference(cnf_transformation,[],[f23])).
% 0.38/0.64  fof(f23,plain,(
% 0.38/0.64    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.38/0.64    inference(ennf_transformation,[],[f13])).
% 0.38/0.64  fof(f13,axiom,(
% 0.38/0.64    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.38/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.38/0.64  fof(f70,plain,(
% 0.38/0.64    ( ! [X0] : (~v2_tops_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.38/0.64    inference(cnf_transformation,[],[f30])).
% 0.38/0.64  fof(f30,plain,(
% 0.38/0.64    ! [X0] : (~v2_tops_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.38/0.64    inference(flattening,[],[f29])).
% 0.38/0.64  fof(f29,plain,(
% 0.38/0.64    ! [X0] : (~v2_tops_1(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.38/0.64    inference(ennf_transformation,[],[f18])).
% 0.38/0.64  fof(f18,axiom,(
% 0.38/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ~v2_tops_1(k2_struct_0(X0),X0))),
% 0.38/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_tops_1)).
% 0.38/0.64  fof(f389,plain,(
% 0.38/0.64    v1_xboole_0(u1_struct_0(sK0))),
% 0.38/0.64    inference(subsumption_resolution,[],[f388,f48])).
% 0.38/0.64  fof(f388,plain,(
% 0.38/0.64    v1_xboole_0(u1_struct_0(sK0)) | ~v2_pre_topc(sK0)),
% 0.38/0.64    inference(subsumption_resolution,[],[f385,f49])).
% 0.38/0.64  fof(f385,plain,(
% 0.38/0.64    v1_xboole_0(u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.38/0.64    inference(resolution,[],[f373,f136])).
% 0.38/0.64  fof(f136,plain,(
% 0.38/0.64    ( ! [X0] : (v4_pre_topc(k1_xboole_0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.38/0.64    inference(subsumption_resolution,[],[f133,f57])).
% 0.38/0.64  fof(f57,plain,(
% 0.38/0.64    v1_xboole_0(k1_xboole_0)),
% 0.38/0.64    inference(cnf_transformation,[],[f1])).
% 0.38/0.64  fof(f1,axiom,(
% 0.38/0.64    v1_xboole_0(k1_xboole_0)),
% 0.38/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.38/0.64  fof(f133,plain,(
% 0.38/0.64    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | v4_pre_topc(k1_xboole_0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.38/0.64    inference(resolution,[],[f72,f61])).
% 0.38/0.64  fof(f61,plain,(
% 0.38/0.64    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.38/0.64    inference(cnf_transformation,[],[f8])).
% 0.38/0.64  fof(f8,axiom,(
% 0.38/0.64    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.38/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.38/0.64  fof(f72,plain,(
% 0.38/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.38/0.64    inference(cnf_transformation,[],[f34])).
% 0.38/0.64  fof(f34,plain,(
% 0.38/0.64    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.38/0.64    inference(flattening,[],[f33])).
% 0.38/0.64  fof(f33,plain,(
% 0.38/0.64    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.38/0.64    inference(ennf_transformation,[],[f12])).
% 0.38/0.64  fof(f12,axiom,(
% 0.38/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.38/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.38/0.64  fof(f373,plain,(
% 0.38/0.64    ~v4_pre_topc(k1_xboole_0,sK0) | v1_xboole_0(u1_struct_0(sK0))),
% 0.38/0.64    inference(subsumption_resolution,[],[f371,f50])).
% 0.38/0.64  fof(f50,plain,(
% 0.38/0.64    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.38/0.64    inference(cnf_transformation,[],[f45])).
% 0.38/0.64  fof(f371,plain,(
% 0.38/0.64    ~v4_pre_topc(k1_xboole_0,sK0) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.38/0.64    inference(resolution,[],[f366,f73])).
% 0.38/0.64  fof(f73,plain,(
% 0.38/0.64    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.38/0.64    inference(cnf_transformation,[],[f36])).
% 0.38/0.64  fof(f36,plain,(
% 0.38/0.64    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.38/0.64    inference(flattening,[],[f35])).
% 0.38/0.64  fof(f35,plain,(
% 0.38/0.64    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.38/0.64    inference(ennf_transformation,[],[f9])).
% 0.38/0.64  fof(f9,axiom,(
% 0.38/0.64    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.38/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.38/0.64  fof(f366,plain,(
% 0.38/0.64    ~r2_hidden(sK1,u1_struct_0(sK0)) | ~v4_pre_topc(k1_xboole_0,sK0)),
% 0.38/0.64    inference(subsumption_resolution,[],[f356,f58])).
% 0.38/0.64  fof(f58,plain,(
% 0.38/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.38/0.64    inference(cnf_transformation,[],[f3])).
% 0.38/0.64  fof(f3,axiom,(
% 0.38/0.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.38/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.38/0.64  fof(f356,plain,(
% 0.38/0.64    ~r2_hidden(sK1,u1_struct_0(sK0)) | ~v4_pre_topc(k1_xboole_0,sK0) | ~r1_tarski(k1_xboole_0,u1_struct_0(sK0))),
% 0.38/0.64    inference(resolution,[],[f301,f74])).
% 0.38/0.64  fof(f74,plain,(
% 0.38/0.64    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.38/0.64    inference(cnf_transformation,[],[f37])).
% 0.38/0.64  fof(f37,plain,(
% 0.38/0.64    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.38/0.64    inference(ennf_transformation,[],[f11])).
% 0.38/0.64  fof(f11,axiom,(
% 0.38/0.64    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.38/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.38/0.64  fof(f301,plain,(
% 0.38/0.64    r2_hidden(u1_struct_0(sK0),k1_xboole_0) | ~r2_hidden(sK1,u1_struct_0(sK0)) | ~v4_pre_topc(k1_xboole_0,sK0)),
% 0.38/0.64    inference(subsumption_resolution,[],[f300,f48])).
% 0.38/0.64  fof(f300,plain,(
% 0.38/0.64    ~v4_pre_topc(k1_xboole_0,sK0) | ~r2_hidden(sK1,u1_struct_0(sK0)) | r2_hidden(u1_struct_0(sK0),k1_xboole_0) | ~v2_pre_topc(sK0)),
% 0.38/0.64    inference(subsumption_resolution,[],[f299,f49])).
% 0.38/0.64  fof(f299,plain,(
% 0.38/0.64    ~v4_pre_topc(k1_xboole_0,sK0) | ~r2_hidden(sK1,u1_struct_0(sK0)) | r2_hidden(u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.38/0.64    inference(resolution,[],[f249,f106])).
% 0.38/0.64  fof(f106,plain,(
% 0.38/0.64    ( ! [X0] : (v4_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.38/0.64    inference(subsumption_resolution,[],[f105,f65])).
% 0.38/0.64  fof(f105,plain,(
% 0.38/0.64    ( ! [X0] : (v4_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~l1_struct_0(X0)) )),
% 0.38/0.64    inference(superposition,[],[f71,f64])).
% 0.38/0.64  fof(f71,plain,(
% 0.38/0.64    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.38/0.64    inference(cnf_transformation,[],[f32])).
% 0.38/0.64  fof(f32,plain,(
% 0.38/0.64    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.38/0.64    inference(flattening,[],[f31])).
% 0.38/0.64  fof(f31,plain,(
% 0.38/0.64    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.38/0.64    inference(ennf_transformation,[],[f15])).
% 0.38/0.64  fof(f15,axiom,(
% 0.38/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.38/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.38/0.64  fof(f249,plain,(
% 0.38/0.64    ~v4_pre_topc(u1_struct_0(sK0),sK0) | ~v4_pre_topc(k1_xboole_0,sK0) | ~r2_hidden(sK1,u1_struct_0(sK0)) | r2_hidden(u1_struct_0(sK0),k1_xboole_0)),
% 0.38/0.64    inference(subsumption_resolution,[],[f248,f49])).
% 0.38/0.64  fof(f248,plain,(
% 0.38/0.64    ~v4_pre_topc(k1_xboole_0,sK0) | ~l1_pre_topc(sK0) | ~v4_pre_topc(u1_struct_0(sK0),sK0) | ~r2_hidden(sK1,u1_struct_0(sK0)) | r2_hidden(u1_struct_0(sK0),k1_xboole_0)),
% 0.38/0.64    inference(resolution,[],[f143,f91])).
% 0.38/0.64  fof(f91,plain,(
% 0.38/0.64    ~v3_pre_topc(u1_struct_0(sK0),sK0) | ~v4_pre_topc(u1_struct_0(sK0),sK0) | ~r2_hidden(sK1,u1_struct_0(sK0)) | r2_hidden(u1_struct_0(sK0),k1_xboole_0)),
% 0.38/0.64    inference(resolution,[],[f77,f83])).
% 0.38/0.64  fof(f77,plain,(
% 0.38/0.64    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | r2_hidden(X3,k1_xboole_0)) )),
% 0.38/0.64    inference(forward_demodulation,[],[f55,f56])).
% 0.38/0.64  fof(f56,plain,(
% 0.38/0.64    k1_xboole_0 = sK2),
% 0.38/0.64    inference(cnf_transformation,[],[f45])).
% 0.38/0.64  fof(f55,plain,(
% 0.38/0.64    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.38/0.64    inference(cnf_transformation,[],[f45])).
% 0.38/0.64  fof(f143,plain,(
% 0.38/0.64    ( ! [X0] : (v3_pre_topc(u1_struct_0(X0),X0) | ~v4_pre_topc(k1_xboole_0,X0) | ~l1_pre_topc(X0)) )),
% 0.38/0.64    inference(subsumption_resolution,[],[f142,f61])).
% 0.38/0.64  fof(f142,plain,(
% 0.38/0.64    ( ! [X0] : (v3_pre_topc(u1_struct_0(X0),X0) | ~v4_pre_topc(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.38/0.64    inference(superposition,[],[f67,f82])).
% 0.38/0.64  fof(f82,plain,(
% 0.38/0.64    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.38/0.64    inference(backward_demodulation,[],[f76,f60])).
% 0.38/0.64  fof(f76,plain,(
% 0.38/0.64    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.38/0.64    inference(forward_demodulation,[],[f63,f59])).
% 0.38/0.64  fof(f59,plain,(
% 0.38/0.64    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.38/0.64    inference(cnf_transformation,[],[f4])).
% 0.38/0.64  fof(f4,axiom,(
% 0.38/0.64    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.38/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.38/0.64  fof(f63,plain,(
% 0.38/0.64    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.38/0.64    inference(cnf_transformation,[],[f7])).
% 0.38/0.64  fof(f7,axiom,(
% 0.38/0.64    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.38/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.38/0.64  fof(f67,plain,(
% 0.38/0.64    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.38/0.64    inference(cnf_transformation,[],[f46])).
% 0.38/0.64  fof(f46,plain,(
% 0.38/0.64    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.38/0.64    inference(nnf_transformation,[],[f27])).
% 0.38/0.64  fof(f27,plain,(
% 0.38/0.64    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.38/0.64    inference(ennf_transformation,[],[f17])).
% 0.38/0.64  fof(f17,axiom,(
% 0.38/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.38/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.38/0.64  % SZS output end Proof for theBenchmark
% 0.38/0.64  % (1594)------------------------------
% 0.38/0.64  % (1594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.64  % (1594)Termination reason: Refutation
% 0.38/0.64  
% 0.38/0.64  % (1594)Memory used [KB]: 1791
% 0.38/0.64  % (1594)Time elapsed: 0.059 s
% 0.38/0.64  % (1594)------------------------------
% 0.38/0.64  % (1594)------------------------------
% 0.38/0.64  % (1432)Success in time 0.282 s
%------------------------------------------------------------------------------
