%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t39_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:29 EDT 2019

% Result     : Theorem 114.12s
% Output     : Refutation 114.12s
% Verified   : 
% Statistics : Number of formulae       :  238 (32015 expanded)
%              Number of leaves         :   33 (9739 expanded)
%              Depth                    :   45
%              Number of atoms          :  798 (290833 expanded)
%              Number of equality atoms :   73 (3129 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112843,plain,(
    $false ),
    inference(subsumption_resolution,[],[f112807,f92415])).

fof(f92415,plain,(
    ~ r2_hidden(sK7(sK1,k3_subset_1(u1_struct_0(sK0),sK3)),k3_subset_1(u1_struct_0(sK0),sK3)) ),
    inference(resolution,[],[f92335,f187])).

fof(f187,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f127,f128])).

fof(f128,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f99])).

fof(f99,plain,(
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
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',d3_tarski)).

fof(f92335,plain,(
    ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK3)) ),
    inference(subsumption_resolution,[],[f83413,f92332])).

fof(f92332,plain,(
    ~ r1_tarski(sK3,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f92331,f91054])).

fof(f91054,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK3)) ),
    inference(superposition,[],[f86744,f83512])).

fof(f83512,plain,(
    k3_subset_1(u1_struct_0(sK0),sK3) = k4_xboole_0(u1_struct_0(sK0),sK3) ),
    inference(resolution,[],[f82776,f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',d5_subset_1)).

fof(f82776,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f138,f82773])).

fof(f82773,plain,(
    r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2793,f82711])).

fof(f82711,plain,(
    k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k1_xboole_0 ),
    inference(superposition,[],[f78024,f365])).

fof(f365,plain,(
    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f251,f178])).

fof(f251,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f226,f134])).

fof(f134,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,plain,
    ( ( ( r1_xboole_0(sK1,sK3)
        & r2_hidden(sK2,sK3)
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & ( ! [X4] :
          ( ~ r1_xboole_0(sK1,X4)
          | ~ r2_hidden(sK2,X4)
          | ~ v3_pre_topc(X4,sK0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f108,f112,f111,f110,f109])).

fof(f109,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,sK0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X1,X4)
                    | ~ r2_hidden(X2,X4)
                    | ~ v3_pre_topc(X4,sK0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f110,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X1,X4)
                    | ~ r2_hidden(X2,X4)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( r1_xboole_0(sK1,X3)
                  & r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,k2_pre_topc(X0,sK1)) )
            & ( ! [X4] :
                  ( ~ r1_xboole_0(sK1,X4)
                  | ~ r2_hidden(X2,X4)
                  | ~ v3_pre_topc(X4,X0)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X2,k2_pre_topc(X0,sK1)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( r1_xboole_0(X1,X3)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
          & ( ! [X4] :
                ( ~ r1_xboole_0(X1,X4)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X2,k2_pre_topc(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ? [X3] :
              ( r1_xboole_0(X1,X3)
              & r2_hidden(sK2,X3)
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK2,k2_pre_topc(X0,X1)) )
        & ( ! [X4] :
              ( ~ r1_xboole_0(X1,X4)
              | ~ r2_hidden(sK2,X4)
              | ~ v3_pre_topc(X4,X0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK2,k2_pre_topc(X0,X1)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( r1_xboole_0(X1,X3)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK3)
        & r2_hidden(X2,sK3)
        & v3_pre_topc(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f108,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X4] :
                    ( ~ r1_xboole_0(X1,X4)
                    | ~ r2_hidden(X2,X4)
                    | ~ v3_pre_topc(X4,X0)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f107])).

fof(f107,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f106])).

fof(f106,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r1_xboole_0(X1,X3)
                    & r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f67,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ~ ( r1_xboole_0(X1,X3)
                        & r2_hidden(X2,X3)
                        & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',t39_tops_1)).

fof(f226,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f135,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',dt_k2_pre_topc)).

fof(f135,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f113])).

fof(f78024,plain,(
    ! [X0] : k3_xboole_0(sK1,k4_xboole_0(X0,k2_pre_topc(sK0,sK1))) = k1_xboole_0 ),
    inference(resolution,[],[f41490,f161])).

fof(f161,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',t3_xboole_1)).

fof(f41490,plain,(
    ! [X8] : r1_tarski(k3_xboole_0(sK1,k4_xboole_0(X8,k2_pre_topc(sK0,sK1))),k1_xboole_0) ),
    inference(resolution,[],[f41114,f1217])).

fof(f1217,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(k2_pre_topc(sK0,sK1),X2)
      | r1_tarski(k3_xboole_0(sK1,X2),k1_xboole_0) ) ),
    inference(superposition,[],[f311,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',d7_xboole_0)).

fof(f311,plain,(
    ! [X2] : r1_tarski(k3_xboole_0(sK1,X2),k3_xboole_0(k2_pre_topc(sK0,sK1),X2)) ),
    inference(resolution,[],[f254,f168])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',t26_xboole_1)).

fof(f254,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f229,f134])).

fof(f229,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f135,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',t48_pre_topc)).

fof(f41114,plain,(
    ! [X2,X1] : r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f145,f40843])).

fof(f40843,plain,(
    ! [X35,X34] : k4_xboole_0(X34,k4_xboole_0(X35,X34)) = X34 ),
    inference(resolution,[],[f40370,f145])).

fof(f40370,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X5)
      | k4_xboole_0(X5,X4) = X5 ) ),
    inference(forward_demodulation,[],[f40198,f167])).

fof(f167,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',t3_boole)).

fof(f40198,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X5,k1_xboole_0) = k4_xboole_0(X5,X4)
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f3172,f142])).

fof(f3172,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k3_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f3147,f166])).

fof(f166,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',t1_boole)).

fof(f3147,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),k1_xboole_0) = k4_xboole_0(X3,k3_xboole_0(X4,X3)) ),
    inference(superposition,[],[f169,f2781])).

fof(f2781,plain,(
    ! [X4] : k4_xboole_0(X4,X4) = k1_xboole_0 ),
    inference(forward_demodulation,[],[f2747,f2614])).

fof(f2614,plain,(
    ! [X13] : k3_subset_1(X13,X13) = k1_xboole_0 ),
    inference(forward_demodulation,[],[f2568,f2595])).

fof(f2595,plain,(
    ! [X4] : k3_subset_1(X4,k1_xboole_0) = X4 ),
    inference(forward_demodulation,[],[f2563,f167])).

fof(f2563,plain,(
    ! [X4] : k3_subset_1(X4,k1_xboole_0) = k4_xboole_0(X4,k1_xboole_0) ),
    inference(resolution,[],[f2391,f178])).

fof(f2391,plain,(
    ! [X4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4)) ),
    inference(backward_demodulation,[],[f2334,f2329])).

fof(f2329,plain,(
    ! [X4] : m1_subset_1(k3_subset_1(sK1,sK1),k1_zfmisc_1(X4)) ),
    inference(resolution,[],[f2300,f184])).

fof(f184,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',t3_subset)).

fof(f2300,plain,(
    ! [X18] : r1_tarski(k3_subset_1(sK1,sK1),X18) ),
    inference(resolution,[],[f2266,f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f129])).

fof(f2266,plain,(
    ! [X7] : ~ r2_hidden(X7,k3_subset_1(sK1,sK1)) ),
    inference(subsumption_resolution,[],[f2263,f2193])).

fof(f2193,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,k3_subset_1(sK1,sK1)) ) ),
    inference(resolution,[],[f2164,f185])).

fof(f185,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f129])).

fof(f2164,plain,(
    r1_tarski(k3_subset_1(sK1,sK1),sK1) ),
    inference(resolution,[],[f2136,f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f125])).

fof(f2136,plain,(
    m1_subset_1(k3_subset_1(sK1,sK1),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f2104,f182])).

fof(f182,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',dt_k3_subset_1)).

fof(f2104,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f2096,f184])).

fof(f2096,plain,(
    r1_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f2091,f2090])).

fof(f2090,plain,
    ( r1_tarski(sK1,sK1)
    | r2_hidden(sK7(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f959,f186])).

fof(f959,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f238,f135])).

fof(f238,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X6),k3_subset_1(u1_struct_0(sK0),sK1))
      | r1_tarski(sK1,X6) ) ),
    inference(resolution,[],[f135,f180])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',t31_subset_1)).

fof(f2091,plain,
    ( r1_tarski(sK1,sK1)
    | ~ r2_hidden(sK7(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f959,f187])).

fof(f2263,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,k3_subset_1(sK1,sK1))
      | ~ r2_hidden(X7,sK1) ) ),
    inference(superposition,[],[f195,f2130])).

fof(f2130,plain,(
    k3_subset_1(sK1,sK1) = k4_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f2104,f178])).

fof(f195,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f173])).

fof(f173,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f123])).

fof(f123,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f121,f122])).

fof(f122,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f121,plain,(
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
    inference(rectify,[],[f120])).

fof(f120,plain,(
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
    inference(flattening,[],[f119])).

fof(f119,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',d5_xboole_0)).

fof(f2334,plain,(
    k3_subset_1(sK1,sK1) = k1_xboole_0 ),
    inference(resolution,[],[f2300,f161])).

fof(f2568,plain,(
    ! [X13] : k3_subset_1(X13,k3_subset_1(X13,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[],[f2391,f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',involutiveness_k3_subset_1)).

fof(f2747,plain,(
    ! [X4] : k3_subset_1(X4,X4) = k4_xboole_0(X4,X4) ),
    inference(resolution,[],[f2634,f178])).

fof(f2634,plain,(
    ! [X14] : m1_subset_1(X14,k1_zfmisc_1(X14)) ),
    inference(forward_demodulation,[],[f2569,f2595])).

fof(f2569,plain,(
    ! [X14] : m1_subset_1(k3_subset_1(X14,k1_xboole_0),k1_zfmisc_1(X14)) ),
    inference(resolution,[],[f2391,f182])).

fof(f169,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',t54_xboole_1)).

fof(f145,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',t79_xboole_1)).

fof(f2793,plain,
    ( k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) != k1_xboole_0
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f2127,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f114])).

fof(f2127,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1109,f2117])).

fof(f2117,plain,
    ( r2_hidden(sK2,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[],[f271,f365])).

fof(f271,plain,(
    ! [X2] :
      ( r2_hidden(sK2,k4_xboole_0(u1_struct_0(sK0),X2))
      | r2_hidden(sK2,X2) ) ),
    inference(resolution,[],[f221,f194])).

fof(f194,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f174])).

fof(f174,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f123])).

fof(f221,plain,(
    r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f219,f218])).

fof(f218,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f199,f217])).

fof(f217,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f134,f193])).

fof(f193,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',dt_l1_pre_topc)).

fof(f199,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f132,f160])).

fof(f160,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f62])).

fof(f62,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',fc2_struct_0)).

fof(f132,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f113])).

fof(f219,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f136,f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',t2_subset)).

fof(f136,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f113])).

fof(f1109,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ r2_hidden(sK2,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1100,f251])).

fof(f1100,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f307,f256])).

fof(f256,plain,(
    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f255,f133])).

fof(f133,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f113])).

fof(f255,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f230,f134])).

fof(f230,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f135,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f61])).

fof(f61,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',fc1_tops_1)).

fof(f307,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),X0))
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k3_subset_1(u1_struct_0(sK0),X0)) ) ),
    inference(subsumption_resolution,[],[f306,f182])).

fof(f306,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k3_subset_1(u1_struct_0(sK0),X0))
      | ~ r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),X0))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f305,f133])).

fof(f305,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k3_subset_1(u1_struct_0(sK0),X0))
      | ~ r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),X0))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f303,f134])).

fof(f303,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k3_subset_1(u1_struct_0(sK0),X0))
      | ~ r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),X0))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f137,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f63])).

fof(f63,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',fc2_tops_1)).

fof(f137,plain,(
    ! [X4] :
      ( ~ v3_pre_topc(X4,sK0)
      | ~ r2_hidden(sK2,X4)
      | ~ r1_xboole_0(sK1,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f113])).

fof(f138,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f113])).

fof(f86744,plain,(
    ! [X8] : ~ r1_tarski(k2_pre_topc(sK0,sK1),k4_xboole_0(X8,sK3)) ),
    inference(resolution,[],[f83851,f82773])).

fof(f83851,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK2,X4)
      | ~ r1_tarski(X4,k4_xboole_0(X5,sK3)) ) ),
    inference(resolution,[],[f83344,f185])).

fof(f83344,plain,(
    ! [X104] : ~ r2_hidden(sK2,k4_xboole_0(X104,sK3)) ),
    inference(resolution,[],[f82778,f195])).

fof(f82778,plain,(
    r2_hidden(sK2,sK3) ),
    inference(subsumption_resolution,[],[f140,f82773])).

fof(f140,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f113])).

fof(f92331,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ r1_tarski(sK3,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f92330,f82788])).

fof(f82788,plain,(
    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(subsumption_resolution,[],[f5166,f82773])).

fof(f5166,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3) ),
    inference(subsumption_resolution,[],[f5159,f138])).

fof(f5159,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) = k3_subset_1(u1_struct_0(sK0),sK3)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f747,f139])).

fof(f139,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f113])).

fof(f747,plain,(
    ! [X2] :
      ( ~ v3_pre_topc(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X2)) = k3_subset_1(u1_struct_0(sK0),X2) ) ),
    inference(subsumption_resolution,[],[f746,f182])).

fof(f746,plain,(
    ! [X2] :
      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X2)) = k3_subset_1(u1_struct_0(sK0),X2)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X2,sK0) ) ),
    inference(subsumption_resolution,[],[f745,f133])).

fof(f745,plain,(
    ! [X2] :
      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X2)) = k3_subset_1(u1_struct_0(sK0),X2)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X2,sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f740,f134])).

fof(f740,plain,(
    ! [X2] :
      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X2)) = k3_subset_1(u1_struct_0(sK0),X2)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X2,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f215,f147])).

fof(f147,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f64])).

fof(f64,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',fc3_tops_1)).

fof(f215,plain,(
    ! [X8] :
      ( ~ v4_pre_topc(X8,sK0)
      | k2_pre_topc(sK0,X8) = X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f134,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f54])).

fof(f54,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',t52_pre_topc)).

fof(f92330,plain,
    ( ~ r1_tarski(sK3,k3_subset_1(u1_struct_0(sK0),sK1))
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) ),
    inference(forward_demodulation,[],[f92138,f83517])).

fof(f83517,plain,(
    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = sK3 ),
    inference(resolution,[],[f82776,f181])).

fof(f92138,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)),k3_subset_1(u1_struct_0(sK0),sK1))
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) ),
    inference(resolution,[],[f83543,f7228])).

fof(f7228,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),sK1))
      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) ) ),
    inference(duplicate_literal_removal,[],[f7220])).

fof(f7220,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f866,f135])).

fof(f866,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X4))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k3_subset_1(X4,X3),k3_subset_1(X4,sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X3)) ) ),
    inference(resolution,[],[f252,f180])).

fof(f252,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f227,f134])).

fof(f227,plain,(
    ! [X0] :
      ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))
      | ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f135,f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',t49_pre_topc)).

fof(f83543,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f83417,f82788])).

fof(f83417,plain,(
    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f82776,f672])).

fof(f672,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X5)),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f211,f182])).

fof(f211,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,X3),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f134,f152])).

fof(f83413,plain,
    ( r1_tarski(sK3,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),sK3)) ),
    inference(resolution,[],[f82776,f444])).

fof(f444,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X7,k3_subset_1(u1_struct_0(sK0),sK1))
      | ~ r1_tarski(sK1,k3_subset_1(u1_struct_0(sK0),X7)) ) ),
    inference(forward_demodulation,[],[f416,f240])).

fof(f240,plain,(
    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(resolution,[],[f135,f181])).

fof(f416,plain,(
    ! [X7] :
      ( r1_tarski(X7,k3_subset_1(u1_struct_0(sK0),sK1))
      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),X7))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f241,f180])).

fof(f241,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f135,f182])).

fof(f112807,plain,(
    r2_hidden(sK7(sK1,k3_subset_1(u1_struct_0(sK0),sK3)),k3_subset_1(u1_struct_0(sK0),sK3)) ),
    inference(resolution,[],[f91059,f89778])).

fof(f89778,plain,(
    ! [X30] :
      ( ~ r2_hidden(X30,sK1)
      | r2_hidden(X30,k3_subset_1(u1_struct_0(sK0),sK3)) ) ),
    inference(subsumption_resolution,[],[f89771,f85214])).

fof(f85214,plain,(
    ! [X27] :
      ( ~ r2_hidden(X27,sK1)
      | ~ r2_hidden(X27,sK3) ) ),
    inference(superposition,[],[f195,f82791])).

fof(f82791,plain,(
    k4_xboole_0(sK1,sK3) = sK1 ),
    inference(subsumption_resolution,[],[f19017,f82773])).

fof(f19017,plain,
    ( k4_xboole_0(sK1,sK3) = sK1
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f18686,f283])).

fof(f283,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f141,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',symmetry_r1_xboole_0)).

fof(f141,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f113])).

fof(f18686,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(X2,sK1)
      | k4_xboole_0(sK1,X2) = sK1 ) ),
    inference(forward_demodulation,[],[f18651,f167])).

fof(f18651,plain,(
    ! [X2] :
      ( k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,X2)
      | ~ r1_xboole_0(X2,sK1) ) ),
    inference(superposition,[],[f2403,f142])).

fof(f2403,plain,(
    ! [X2] : k4_xboole_0(sK1,X2) = k4_xboole_0(sK1,k3_xboole_0(X2,sK1)) ),
    inference(forward_demodulation,[],[f2376,f166])).

fof(f2376,plain,(
    ! [X2] : k2_xboole_0(k4_xboole_0(sK1,X2),k1_xboole_0) = k4_xboole_0(sK1,k3_xboole_0(X2,sK1)) ),
    inference(backward_demodulation,[],[f2334,f2258])).

fof(f2258,plain,(
    ! [X2] : k2_xboole_0(k4_xboole_0(sK1,X2),k3_subset_1(sK1,sK1)) = k4_xboole_0(sK1,k3_xboole_0(X2,sK1)) ),
    inference(superposition,[],[f169,f2130])).

fof(f89771,plain,(
    ! [X30] :
      ( r2_hidden(X30,k3_subset_1(u1_struct_0(sK0),sK3))
      | r2_hidden(X30,sK3)
      | ~ r2_hidden(X30,sK1) ) ),
    inference(resolution,[],[f85164,f135])).

fof(f85164,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,k3_subset_1(u1_struct_0(sK0),sK3))
      | r2_hidden(X1,sK3)
      | ~ r2_hidden(X1,X2) ) ),
    inference(global_subsumption,[],[f948,f84649])).

fof(f84649,plain,(
    ! [X18] :
      ( ~ r2_hidden(X18,u1_struct_0(sK0))
      | r2_hidden(X18,sK3)
      | r2_hidden(X18,k3_subset_1(u1_struct_0(sK0),sK3)) ) ),
    inference(superposition,[],[f194,f83512])).

fof(f948,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f260,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t39_tops_1.p',t4_subset)).

fof(f260,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f218,f191])).

fof(f91059,plain,(
    r2_hidden(sK7(sK1,k3_subset_1(u1_struct_0(sK0),sK3)),sK1) ),
    inference(subsumption_resolution,[],[f83570,f91054])).

fof(f83570,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK3))
    | r2_hidden(sK7(sK1,k3_subset_1(u1_struct_0(sK0),sK3)),sK1) ),
    inference(forward_demodulation,[],[f83476,f82788])).

fof(f83476,plain,
    ( r2_hidden(sK7(sK1,k3_subset_1(u1_struct_0(sK0),sK3)),sK1)
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) ),
    inference(resolution,[],[f82776,f4137])).

fof(f4137,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK7(sK1,k3_subset_1(u1_struct_0(sK0),X5)),sK1)
      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X5))) ) ),
    inference(resolution,[],[f863,f182])).

fof(f863,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))
      | r2_hidden(sK7(sK1,X0),sK1) ) ),
    inference(resolution,[],[f252,f186])).
%------------------------------------------------------------------------------
