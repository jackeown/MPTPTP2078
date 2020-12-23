%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1888+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:48 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 485 expanded)
%              Number of clauses        :   74 ( 153 expanded)
%              Number of leaves         :   16 ( 124 expanded)
%              Depth                    :   22
%              Number of atoms          :  460 (2586 expanded)
%              Number of equality atoms :  154 ( 509 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
                | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
                  | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
          & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)))
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
            & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
                & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))
              & ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)))
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v3_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    & ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v3_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f39,f38,f37])).

fof(f62,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f41,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
               => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
      | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_874,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_882,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_876,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_881,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_884,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1825,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_881,c_884])).

cnf(c_5465,plain,
    ( k3_xboole_0(X0,X1) = X2
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_884])).

cnf(c_5539,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = X1
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_876,c_5465])).

cnf(c_8440,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_876,c_5539])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_879,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8625,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8440,c_879])).

cnf(c_369,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_12])).

cnf(c_370,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_371,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_8965,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8625,c_371])).

cnf(c_8974,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK1(X0,X1,k1_xboole_0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_882,c_8965])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21,negated_conjecture,
    ( v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_279,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_280,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X0,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_284,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_280,c_23,c_22,c_20])).

cnf(c_285,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X0,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) ),
    inference(renaming,[status(thm)],[c_284])).

cnf(c_872,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1))
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285])).

cnf(c_11162,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(X0,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)),k1_xboole_0))) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1))
    | k3_xboole_0(X0,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1))) = k1_xboole_0
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(X0,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)),k1_xboole_0),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8974,c_872])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_877,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_322,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_870,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_14,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_875,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1216,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_870,c_875])).

cnf(c_1802,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_1216])).

cnf(c_24,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_27,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_37,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_39,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_11,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_41,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_43,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_2737,plain,
    ( r2_hidden(X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1802,c_24,c_27,c_39,c_43])).

cnf(c_2738,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2737])).

cnf(c_2745,plain,
    ( k3_xboole_0(X0,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1))) = X2
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(X0,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)),X2),u1_struct_0(sK2)) = iProver_top
    | r2_hidden(sK1(X0,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)),X2),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_882,c_2738])).

cnf(c_8981,plain,
    ( k3_xboole_0(X0,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1))) = k1_xboole_0
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(X0,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)),k1_xboole_0),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2745,c_8965])).

cnf(c_12307,plain,
    ( m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | k3_xboole_0(X0,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1))) = k1_xboole_0
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(X0,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)),k1_xboole_0))) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11162,c_8981])).

cnf(c_12308,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(X0,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)),k1_xboole_0))) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1))
    | k3_xboole_0(X0,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1))) = k1_xboole_0
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12307])).

cnf(c_12316,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(X0,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)),k1_xboole_0))) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    | k3_xboole_0(X0,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_874,c_12308])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_873,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5469,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)),X1,X2))) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0))
    | k3_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)),X1) = X2
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)),X1,X2),u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_872])).

cnf(c_5472,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)),X1) = X2
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)),X1,X2),u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_2738])).

cnf(c_5496,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)),X1,X2))) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0))
    | k3_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)),X1) = X2
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5469,c_5472])).

cnf(c_5860,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),X0,X1))) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3))
    | k3_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),X0) = X1
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_873,c_5496])).

cnf(c_6443,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),X0,k1_xboole_0))) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3))
    | k3_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_876,c_5860])).

cnf(c_12595,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3))
    | k3_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12316,c_6443])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_17,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_255,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) != X0
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != X1
    | k3_xboole_0(X1,X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_256,plain,
    ( k3_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_255])).

cnf(c_15146,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12595,c_256])).

cnf(c_16,negated_conjecture,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_15161,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) ),
    inference(demodulation,[status(thm)],[c_15146,c_16])).

cnf(c_15162,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_15161])).


%------------------------------------------------------------------------------
