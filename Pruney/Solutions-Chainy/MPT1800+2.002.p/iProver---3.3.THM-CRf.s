%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:02 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  225 (3163 expanded)
%              Number of clauses        :  150 ( 709 expanded)
%              Number of leaves         :   23 ( 751 expanded)
%              Depth                    :   21
%              Number of atoms          :  880 (25739 expanded)
%              Number of equality atoms :  279 (4797 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,sK3)
          | ~ m1_pre_topc(sK3,X0)
          | ~ v1_tsep_1(sK3,X0) )
        & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,sK3)
          | ( m1_pre_topc(sK3,X0)
            & v1_tsep_1(sK3,X0) ) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
              | ~ m1_pre_topc(X1,X0)
              | ~ v1_tsep_1(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
              | ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) ) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,X1)
            | ~ m1_pre_topc(X1,sK2)
            | ~ v1_tsep_1(X1,sK2) )
          & ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,X1)
            | ( m1_pre_topc(X1,sK2)
              & v1_tsep_1(X1,sK2) ) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
      | ~ m1_pre_topc(sK3,sK2)
      | ~ v1_tsep_1(sK3,sK2) )
    & ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
      | ( m1_pre_topc(sK3,sK2)
        & v1_tsep_1(sK3,sK2) ) )
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f44,f46,f45])).

fof(f75,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f69,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f36])).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0,X1),X0)
        & u1_struct_0(X1) = sK1(X0,X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ( ~ v3_pre_topc(sK1(X0,X1),X0)
                & u1_struct_0(X1) = sK1(X0,X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f48,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(sK1(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_165,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_24])).

cnf(c_703,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_165])).

cnf(c_704,plain,
    ( v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_703])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_706,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_704,c_28,c_27,c_26,c_25])).

cnf(c_3422,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_706])).

cnf(c_5,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3435,plain,
    ( m1_subset_1(sK0(X0_51),k1_zfmisc_1(u1_struct_0(X0_51)))
    | ~ l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3967,plain,
    ( m1_subset_1(sK0(X0_51),k1_zfmisc_1(u1_struct_0(X0_51))) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3435])).

cnf(c_4303,plain,
    ( m1_subset_1(sK0(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3422,c_3967])).

cnf(c_29,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_30,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_31,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_733,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_165])).

cnf(c_734,plain,
    ( v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_733])).

cnf(c_735,plain,
    ( v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_734])).

cnf(c_4320,plain,
    ( m1_subset_1(sK0(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4303,c_29,c_30,c_31,c_735])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_2,c_15])).

cnf(c_868,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_473,c_28])).

cnf(c_869,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(X0,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k5_tmap_1(sK2,X0) = u1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_868])).

cnf(c_873,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(X0,sK2)
    | k5_tmap_1(sK2,X0) = u1_pre_topc(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_869,c_27,c_26])).

cnf(c_3413,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(X0_49,sK2)
    | k5_tmap_1(sK2,X0_49) = u1_pre_topc(sK2) ),
    inference(subtyping,[status(esa)],[c_873])).

cnf(c_3990,plain,
    ( k5_tmap_1(sK2,X0_49) = u1_pre_topc(sK2)
    | m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_pre_topc(X0_49,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3413])).

cnf(c_5020,plain,
    ( k5_tmap_1(sK2,sK0(k8_tmap_1(sK2,sK3))) = u1_pre_topc(sK2)
    | v3_pre_topc(sK0(k8_tmap_1(sK2,sK3)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4320,c_3990])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4,plain,
    ( v1_xboole_0(sK0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_391,plain,
    ( ~ m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(sK0(X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_3432,plain,
    ( ~ m1_subset_1(sK0(X0_51),k1_zfmisc_1(u1_struct_0(X1_51)))
    | v3_pre_topc(sK0(X0_51),X1_51)
    | ~ v2_pre_topc(X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_391])).

cnf(c_3970,plain,
    ( m1_subset_1(sK0(X0_51),k1_zfmisc_1(u1_struct_0(X1_51))) != iProver_top
    | v3_pre_topc(sK0(X0_51),X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3432])).

cnf(c_4332,plain,
    ( v3_pre_topc(sK0(k8_tmap_1(sK2,sK3)),sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4320,c_3970])).

cnf(c_6257,plain,
    ( k5_tmap_1(sK2,sK0(k8_tmap_1(sK2,sK3))) = u1_pre_topc(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5020,c_29,c_30,c_31,c_735,c_4332])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_946,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_28])).

cnf(c_947,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,X0)) = k6_tmap_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_946])).

cnf(c_951,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,X0)) = k6_tmap_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_947,c_27,c_26])).

cnf(c_3409,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2)))
    | g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,X0_49)) = k6_tmap_1(sK2,X0_49) ),
    inference(subtyping,[status(esa)],[c_951])).

cnf(c_3994,plain,
    ( g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,X0_49)) = k6_tmap_1(sK2,X0_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3409])).

cnf(c_4858,plain,
    ( g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,sK0(k8_tmap_1(sK2,sK3)))) = k6_tmap_1(sK2,sK0(k8_tmap_1(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_4320,c_3994])).

cnf(c_6260,plain,
    ( k6_tmap_1(sK2,sK0(k8_tmap_1(sK2,sK3))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(demodulation,[status(thm)],[c_6257,c_4858])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_192,plain,
    ( ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_20])).

cnf(c_193,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_192])).

cnf(c_23,negated_conjecture,
    ( v1_tsep_1(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_241,plain,
    ( v1_tsep_1(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_602,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_193,c_241])).

cnf(c_603,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v3_pre_topc(u1_struct_0(sK3),sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_605,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_603,c_26,c_24])).

cnf(c_3428,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_605])).

cnf(c_3973,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3428])).

cnf(c_3454,plain,
    ( X0_51 != X1_51
    | u1_struct_0(X0_51) = u1_struct_0(X1_51) ),
    theory(equality)).

cnf(c_3466,plain,
    ( sK2 != sK2
    | u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3454])).

cnf(c_3455,plain,
    ( u1_pre_topc(X0_51) = u1_pre_topc(X1_51)
    | X0_51 != X1_51 ),
    theory(equality)).

cnf(c_3467,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3455])).

cnf(c_3449,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_3481,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_3449])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_711,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(k8_tmap_1(X0,X1))
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_165])).

cnf(c_712,plain,
    ( v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_711])).

cnf(c_714,plain,
    ( v1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_712,c_28,c_27,c_26])).

cnf(c_763,plain,
    ( ~ l1_pre_topc(X0)
    | k8_tmap_1(sK2,sK3) != X0
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_714])).

cnf(c_764,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_763])).

cnf(c_766,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_764,c_28,c_27,c_26,c_734])).

cnf(c_3419,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_766])).

cnf(c_4458,plain,
    ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3449])).

cnf(c_3452,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_4403,plain,
    ( X0_51 != X1_51
    | k8_tmap_1(sK2,sK3) != X1_51
    | k8_tmap_1(sK2,sK3) = X0_51 ),
    inference(instantiation,[status(thm)],[c_3452])).

cnf(c_4457,plain,
    ( X0_51 != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) = X0_51
    | k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_4403])).

cnf(c_4561,plain,
    ( k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_4457])).

cnf(c_4263,plain,
    ( k8_tmap_1(sK2,sK3) != X0_51
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0_51
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3452])).

cnf(c_4631,plain,
    ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_4263])).

cnf(c_3456,plain,
    ( X0_52 != X1_52
    | g1_pre_topc(X0_49,X0_52) = g1_pre_topc(X1_49,X1_52)
    | X0_49 != X1_49 ),
    theory(equality)).

cnf(c_4751,plain,
    ( u1_pre_topc(sK2) != u1_pre_topc(k8_tmap_1(sK2,sK3))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
    | u1_struct_0(sK2) != u1_struct_0(k8_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3456])).

cnf(c_3451,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_4575,plain,
    ( X0_49 != X1_49
    | X0_49 = u1_struct_0(X0_51)
    | u1_struct_0(X0_51) != X1_49 ),
    inference(instantiation,[status(thm)],[c_3451])).

cnf(c_4707,plain,
    ( X0_49 = u1_struct_0(k8_tmap_1(sK2,sK3))
    | X0_49 != u1_struct_0(sK2)
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4575])).

cnf(c_4979,plain,
    ( u1_struct_0(X0_51) = u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(X0_51) != u1_struct_0(sK2)
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4707])).

cnf(c_4981,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = u1_struct_0(k8_tmap_1(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4979])).

cnf(c_692,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_165])).

cnf(c_693,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_695,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_693,c_26])).

cnf(c_3423,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_695])).

cnf(c_3977,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3423])).

cnf(c_5018,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2)
    | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3977,c_3990])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_177,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_20])).

cnf(c_178,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(renaming,[status(thm)],[c_177])).

cnf(c_684,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0))
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_178,c_165])).

cnf(c_685,plain,
    ( v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_684])).

cnf(c_687,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_685,c_28,c_27,c_26,c_25])).

cnf(c_3424,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_687])).

cnf(c_5040,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2)
    | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5018,c_3424])).

cnf(c_5046,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK2)
    | u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5040])).

cnf(c_3453,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_5093,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != X0_52
    | u1_pre_topc(sK2) != X0_52
    | u1_pre_topc(sK2) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3453])).

cnf(c_5540,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
    | u1_pre_topc(sK2) = u1_pre_topc(k8_tmap_1(sK2,sK3))
    | u1_pre_topc(sK2) != u1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5093])).

cnf(c_5681,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3973,c_3466,c_3467,c_3481,c_3428,c_3422,c_3419,c_4458,c_4561,c_4631,c_4751,c_4981,c_5046,c_5540])).

cnf(c_6265,plain,
    ( k6_tmap_1(sK2,sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_6260,c_5681])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_928,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_28])).

cnf(c_929,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_pre_topc(k6_tmap_1(sK2,X0)) = k5_tmap_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_928])).

cnf(c_933,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_pre_topc(k6_tmap_1(sK2,X0)) = k5_tmap_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_929,c_27,c_26])).

cnf(c_3410,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_pre_topc(k6_tmap_1(sK2,X0_49)) = k5_tmap_1(sK2,X0_49) ),
    inference(subtyping,[status(esa)],[c_933])).

cnf(c_3993,plain,
    ( u1_pre_topc(k6_tmap_1(sK2,X0_49)) = k5_tmap_1(sK2,X0_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3410])).

cnf(c_4597,plain,
    ( u1_pre_topc(k6_tmap_1(sK2,sK0(k8_tmap_1(sK2,sK3)))) = k5_tmap_1(sK2,sK0(k8_tmap_1(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_4320,c_3993])).

cnf(c_6261,plain,
    ( u1_pre_topc(k6_tmap_1(sK2,sK0(k8_tmap_1(sK2,sK3)))) = u1_pre_topc(sK2) ),
    inference(demodulation,[status(thm)],[c_6257,c_4597])).

cnf(c_6266,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2) ),
    inference(demodulation,[status(thm)],[c_6265,c_6261])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_528,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_7,c_193])).

cnf(c_656,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_528,c_165])).

cnf(c_657,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,sK3) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_659,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2)
    | sK1(sK2,sK3) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_657,c_26])).

cnf(c_3426,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2)
    | sK1(sK2,sK3) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_659])).

cnf(c_3975,plain,
    ( sK1(sK2,sK3) = u1_struct_0(sK3)
    | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3426])).

cnf(c_21,negated_conjecture,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v1_tsep_1(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_239,plain,
    ( ~ v1_tsep_1(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(prop_impl,[status(thm)],[c_24,c_21])).

cnf(c_577,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_239])).

cnf(c_578,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,sK3) = u1_struct_0(sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_577])).

cnf(c_580,plain,
    ( sK1(sK2,sK3) = u1_struct_0(sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_578,c_26,c_24])).

cnf(c_3430,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK3) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_580])).

cnf(c_5661,plain,
    ( sK1(sK2,sK3) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3975,c_3466,c_3467,c_3481,c_3430,c_3428,c_3422,c_3419,c_4458,c_4561,c_4631,c_4751,c_4981,c_5046,c_5540])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(sK1(X1,X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_588,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(sK1(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_239])).

cnf(c_589,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v3_pre_topc(sK1(sK2,sK3),sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_588])).

cnf(c_591,plain,
    ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_589,c_26,c_24])).

cnf(c_3429,plain,
    ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_591])).

cnf(c_3972,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | v3_pre_topc(sK1(sK2,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3429])).

cnf(c_5664,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5661,c_3972])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_450,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_14,c_1])).

cnf(c_889,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_450,c_28])).

cnf(c_890,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(X0,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k5_tmap_1(sK2,X0) != u1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_889])).

cnf(c_894,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(X0,sK2)
    | k5_tmap_1(sK2,X0) != u1_pre_topc(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_890,c_27,c_26])).

cnf(c_3412,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(X0_49,sK2)
    | k5_tmap_1(sK2,X0_49) != u1_pre_topc(sK2) ),
    inference(subtyping,[status(esa)],[c_894])).

cnf(c_3991,plain,
    ( k5_tmap_1(sK2,X0_49) != u1_pre_topc(sK2)
    | m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_pre_topc(X0_49,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3412])).

cnf(c_5163,plain,
    ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3424,c_3991])).

cnf(c_694,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6266,c_5681,c_5664,c_5163,c_694,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.01/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/0.99  
% 3.01/0.99  ------  iProver source info
% 3.01/0.99  
% 3.01/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.01/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/0.99  git: non_committed_changes: false
% 3.01/0.99  git: last_make_outside_of_git: false
% 3.01/0.99  
% 3.01/0.99  ------ 
% 3.01/0.99  
% 3.01/0.99  ------ Input Options
% 3.01/0.99  
% 3.01/0.99  --out_options                           all
% 3.01/0.99  --tptp_safe_out                         true
% 3.01/0.99  --problem_path                          ""
% 3.01/0.99  --include_path                          ""
% 3.01/0.99  --clausifier                            res/vclausify_rel
% 3.01/0.99  --clausifier_options                    --mode clausify
% 3.01/0.99  --stdin                                 false
% 3.01/0.99  --stats_out                             all
% 3.01/0.99  
% 3.01/0.99  ------ General Options
% 3.01/0.99  
% 3.01/0.99  --fof                                   false
% 3.01/0.99  --time_out_real                         305.
% 3.01/0.99  --time_out_virtual                      -1.
% 3.01/0.99  --symbol_type_check                     false
% 3.01/0.99  --clausify_out                          false
% 3.01/0.99  --sig_cnt_out                           false
% 3.01/0.99  --trig_cnt_out                          false
% 3.01/0.99  --trig_cnt_out_tolerance                1.
% 3.01/0.99  --trig_cnt_out_sk_spl                   false
% 3.01/0.99  --abstr_cl_out                          false
% 3.01/0.99  
% 3.01/0.99  ------ Global Options
% 3.01/0.99  
% 3.01/0.99  --schedule                              default
% 3.01/0.99  --add_important_lit                     false
% 3.01/0.99  --prop_solver_per_cl                    1000
% 3.01/0.99  --min_unsat_core                        false
% 3.01/0.99  --soft_assumptions                      false
% 3.01/0.99  --soft_lemma_size                       3
% 3.01/0.99  --prop_impl_unit_size                   0
% 3.01/0.99  --prop_impl_unit                        []
% 3.01/0.99  --share_sel_clauses                     true
% 3.01/0.99  --reset_solvers                         false
% 3.01/0.99  --bc_imp_inh                            [conj_cone]
% 3.01/0.99  --conj_cone_tolerance                   3.
% 3.01/0.99  --extra_neg_conj                        none
% 3.01/0.99  --large_theory_mode                     true
% 3.01/0.99  --prolific_symb_bound                   200
% 3.01/0.99  --lt_threshold                          2000
% 3.01/0.99  --clause_weak_htbl                      true
% 3.01/0.99  --gc_record_bc_elim                     false
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing Options
% 3.01/0.99  
% 3.01/0.99  --preprocessing_flag                    true
% 3.01/0.99  --time_out_prep_mult                    0.1
% 3.01/0.99  --splitting_mode                        input
% 3.01/0.99  --splitting_grd                         true
% 3.01/0.99  --splitting_cvd                         false
% 3.01/0.99  --splitting_cvd_svl                     false
% 3.01/0.99  --splitting_nvd                         32
% 3.01/0.99  --sub_typing                            true
% 3.01/0.99  --prep_gs_sim                           true
% 3.01/0.99  --prep_unflatten                        true
% 3.01/0.99  --prep_res_sim                          true
% 3.01/0.99  --prep_upred                            true
% 3.01/0.99  --prep_sem_filter                       exhaustive
% 3.01/0.99  --prep_sem_filter_out                   false
% 3.01/0.99  --pred_elim                             true
% 3.01/0.99  --res_sim_input                         true
% 3.01/0.99  --eq_ax_congr_red                       true
% 3.01/0.99  --pure_diseq_elim                       true
% 3.01/0.99  --brand_transform                       false
% 3.01/0.99  --non_eq_to_eq                          false
% 3.01/0.99  --prep_def_merge                        true
% 3.01/0.99  --prep_def_merge_prop_impl              false
% 3.01/0.99  --prep_def_merge_mbd                    true
% 3.01/0.99  --prep_def_merge_tr_red                 false
% 3.01/0.99  --prep_def_merge_tr_cl                  false
% 3.01/0.99  --smt_preprocessing                     true
% 3.01/0.99  --smt_ac_axioms                         fast
% 3.01/0.99  --preprocessed_out                      false
% 3.01/0.99  --preprocessed_stats                    false
% 3.01/0.99  
% 3.01/0.99  ------ Abstraction refinement Options
% 3.01/0.99  
% 3.01/0.99  --abstr_ref                             []
% 3.01/0.99  --abstr_ref_prep                        false
% 3.01/0.99  --abstr_ref_until_sat                   false
% 3.01/0.99  --abstr_ref_sig_restrict                funpre
% 3.01/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/0.99  --abstr_ref_under                       []
% 3.01/0.99  
% 3.01/0.99  ------ SAT Options
% 3.01/0.99  
% 3.01/0.99  --sat_mode                              false
% 3.01/0.99  --sat_fm_restart_options                ""
% 3.01/0.99  --sat_gr_def                            false
% 3.01/0.99  --sat_epr_types                         true
% 3.01/0.99  --sat_non_cyclic_types                  false
% 3.01/0.99  --sat_finite_models                     false
% 3.01/0.99  --sat_fm_lemmas                         false
% 3.01/0.99  --sat_fm_prep                           false
% 3.01/0.99  --sat_fm_uc_incr                        true
% 3.01/0.99  --sat_out_model                         small
% 3.01/0.99  --sat_out_clauses                       false
% 3.01/0.99  
% 3.01/0.99  ------ QBF Options
% 3.01/0.99  
% 3.01/0.99  --qbf_mode                              false
% 3.01/0.99  --qbf_elim_univ                         false
% 3.01/0.99  --qbf_dom_inst                          none
% 3.01/0.99  --qbf_dom_pre_inst                      false
% 3.01/0.99  --qbf_sk_in                             false
% 3.01/0.99  --qbf_pred_elim                         true
% 3.01/0.99  --qbf_split                             512
% 3.01/0.99  
% 3.01/0.99  ------ BMC1 Options
% 3.01/0.99  
% 3.01/0.99  --bmc1_incremental                      false
% 3.01/0.99  --bmc1_axioms                           reachable_all
% 3.01/0.99  --bmc1_min_bound                        0
% 3.01/0.99  --bmc1_max_bound                        -1
% 3.01/0.99  --bmc1_max_bound_default                -1
% 3.01/0.99  --bmc1_symbol_reachability              true
% 3.01/0.99  --bmc1_property_lemmas                  false
% 3.01/0.99  --bmc1_k_induction                      false
% 3.01/0.99  --bmc1_non_equiv_states                 false
% 3.01/0.99  --bmc1_deadlock                         false
% 3.01/0.99  --bmc1_ucm                              false
% 3.01/0.99  --bmc1_add_unsat_core                   none
% 3.01/0.99  --bmc1_unsat_core_children              false
% 3.01/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/0.99  --bmc1_out_stat                         full
% 3.01/0.99  --bmc1_ground_init                      false
% 3.01/0.99  --bmc1_pre_inst_next_state              false
% 3.01/0.99  --bmc1_pre_inst_state                   false
% 3.01/0.99  --bmc1_pre_inst_reach_state             false
% 3.01/0.99  --bmc1_out_unsat_core                   false
% 3.01/0.99  --bmc1_aig_witness_out                  false
% 3.01/0.99  --bmc1_verbose                          false
% 3.01/0.99  --bmc1_dump_clauses_tptp                false
% 3.01/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.01/0.99  --bmc1_dump_file                        -
% 3.01/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.01/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.01/0.99  --bmc1_ucm_extend_mode                  1
% 3.01/0.99  --bmc1_ucm_init_mode                    2
% 3.01/0.99  --bmc1_ucm_cone_mode                    none
% 3.01/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.01/0.99  --bmc1_ucm_relax_model                  4
% 3.01/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.01/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/0.99  --bmc1_ucm_layered_model                none
% 3.01/0.99  --bmc1_ucm_max_lemma_size               10
% 3.01/0.99  
% 3.01/0.99  ------ AIG Options
% 3.01/0.99  
% 3.01/0.99  --aig_mode                              false
% 3.01/0.99  
% 3.01/0.99  ------ Instantiation Options
% 3.01/0.99  
% 3.01/0.99  --instantiation_flag                    true
% 3.01/0.99  --inst_sos_flag                         false
% 3.01/0.99  --inst_sos_phase                        true
% 3.01/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel_side                     num_symb
% 3.01/0.99  --inst_solver_per_active                1400
% 3.01/0.99  --inst_solver_calls_frac                1.
% 3.01/0.99  --inst_passive_queue_type               priority_queues
% 3.01/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/0.99  --inst_passive_queues_freq              [25;2]
% 3.01/0.99  --inst_dismatching                      true
% 3.01/0.99  --inst_eager_unprocessed_to_passive     true
% 3.01/0.99  --inst_prop_sim_given                   true
% 3.01/0.99  --inst_prop_sim_new                     false
% 3.01/0.99  --inst_subs_new                         false
% 3.01/0.99  --inst_eq_res_simp                      false
% 3.01/0.99  --inst_subs_given                       false
% 3.01/0.99  --inst_orphan_elimination               true
% 3.01/0.99  --inst_learning_loop_flag               true
% 3.01/0.99  --inst_learning_start                   3000
% 3.01/0.99  --inst_learning_factor                  2
% 3.01/0.99  --inst_start_prop_sim_after_learn       3
% 3.01/0.99  --inst_sel_renew                        solver
% 3.01/0.99  --inst_lit_activity_flag                true
% 3.01/0.99  --inst_restr_to_given                   false
% 3.01/0.99  --inst_activity_threshold               500
% 3.01/0.99  --inst_out_proof                        true
% 3.01/0.99  
% 3.01/0.99  ------ Resolution Options
% 3.01/0.99  
% 3.01/0.99  --resolution_flag                       true
% 3.01/0.99  --res_lit_sel                           adaptive
% 3.01/0.99  --res_lit_sel_side                      none
% 3.01/0.99  --res_ordering                          kbo
% 3.01/0.99  --res_to_prop_solver                    active
% 3.01/0.99  --res_prop_simpl_new                    false
% 3.01/0.99  --res_prop_simpl_given                  true
% 3.01/0.99  --res_passive_queue_type                priority_queues
% 3.01/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/0.99  --res_passive_queues_freq               [15;5]
% 3.01/0.99  --res_forward_subs                      full
% 3.01/0.99  --res_backward_subs                     full
% 3.01/0.99  --res_forward_subs_resolution           true
% 3.01/0.99  --res_backward_subs_resolution          true
% 3.01/0.99  --res_orphan_elimination                true
% 3.01/0.99  --res_time_limit                        2.
% 3.01/0.99  --res_out_proof                         true
% 3.01/0.99  
% 3.01/0.99  ------ Superposition Options
% 3.01/0.99  
% 3.01/0.99  --superposition_flag                    true
% 3.01/0.99  --sup_passive_queue_type                priority_queues
% 3.01/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.01/0.99  --demod_completeness_check              fast
% 3.01/0.99  --demod_use_ground                      true
% 3.01/0.99  --sup_to_prop_solver                    passive
% 3.01/0.99  --sup_prop_simpl_new                    true
% 3.01/0.99  --sup_prop_simpl_given                  true
% 3.01/0.99  --sup_fun_splitting                     false
% 3.01/0.99  --sup_smt_interval                      50000
% 3.01/0.99  
% 3.01/0.99  ------ Superposition Simplification Setup
% 3.01/0.99  
% 3.01/0.99  --sup_indices_passive                   []
% 3.01/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_full_bw                           [BwDemod]
% 3.01/0.99  --sup_immed_triv                        [TrivRules]
% 3.01/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_immed_bw_main                     []
% 3.01/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.99  
% 3.01/0.99  ------ Combination Options
% 3.01/0.99  
% 3.01/0.99  --comb_res_mult                         3
% 3.01/0.99  --comb_sup_mult                         2
% 3.01/0.99  --comb_inst_mult                        10
% 3.01/0.99  
% 3.01/0.99  ------ Debug Options
% 3.01/0.99  
% 3.01/0.99  --dbg_backtrace                         false
% 3.01/0.99  --dbg_dump_prop_clauses                 false
% 3.01/0.99  --dbg_dump_prop_clauses_file            -
% 3.01/0.99  --dbg_out_stat                          false
% 3.01/0.99  ------ Parsing...
% 3.01/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing... gs_s  sp: 5 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/0.99  ------ Proving...
% 3.01/0.99  ------ Problem Properties 
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  clauses                                 32
% 3.01/0.99  conjectures                             2
% 3.01/0.99  EPR                                     7
% 3.01/0.99  Horn                                    29
% 3.01/0.99  unary                                   8
% 3.01/0.99  binary                                  11
% 3.01/0.99  lits                                    73
% 3.01/0.99  lits eq                                 19
% 3.01/0.99  fd_pure                                 0
% 3.01/0.99  fd_pseudo                               0
% 3.01/0.99  fd_cond                                 0
% 3.01/0.99  fd_pseudo_cond                          0
% 3.01/0.99  AC symbols                              0
% 3.01/0.99  
% 3.01/0.99  ------ Schedule dynamic 5 is on 
% 3.01/0.99  
% 3.01/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  ------ 
% 3.01/0.99  Current options:
% 3.01/0.99  ------ 
% 3.01/0.99  
% 3.01/0.99  ------ Input Options
% 3.01/0.99  
% 3.01/0.99  --out_options                           all
% 3.01/0.99  --tptp_safe_out                         true
% 3.01/0.99  --problem_path                          ""
% 3.01/0.99  --include_path                          ""
% 3.01/0.99  --clausifier                            res/vclausify_rel
% 3.01/0.99  --clausifier_options                    --mode clausify
% 3.01/0.99  --stdin                                 false
% 3.01/0.99  --stats_out                             all
% 3.01/0.99  
% 3.01/0.99  ------ General Options
% 3.01/0.99  
% 3.01/0.99  --fof                                   false
% 3.01/0.99  --time_out_real                         305.
% 3.01/0.99  --time_out_virtual                      -1.
% 3.01/0.99  --symbol_type_check                     false
% 3.01/0.99  --clausify_out                          false
% 3.01/0.99  --sig_cnt_out                           false
% 3.01/0.99  --trig_cnt_out                          false
% 3.01/0.99  --trig_cnt_out_tolerance                1.
% 3.01/0.99  --trig_cnt_out_sk_spl                   false
% 3.01/0.99  --abstr_cl_out                          false
% 3.01/0.99  
% 3.01/0.99  ------ Global Options
% 3.01/0.99  
% 3.01/0.99  --schedule                              default
% 3.01/0.99  --add_important_lit                     false
% 3.01/0.99  --prop_solver_per_cl                    1000
% 3.01/0.99  --min_unsat_core                        false
% 3.01/0.99  --soft_assumptions                      false
% 3.01/0.99  --soft_lemma_size                       3
% 3.01/0.99  --prop_impl_unit_size                   0
% 3.01/0.99  --prop_impl_unit                        []
% 3.01/0.99  --share_sel_clauses                     true
% 3.01/0.99  --reset_solvers                         false
% 3.01/0.99  --bc_imp_inh                            [conj_cone]
% 3.01/0.99  --conj_cone_tolerance                   3.
% 3.01/0.99  --extra_neg_conj                        none
% 3.01/0.99  --large_theory_mode                     true
% 3.01/0.99  --prolific_symb_bound                   200
% 3.01/0.99  --lt_threshold                          2000
% 3.01/0.99  --clause_weak_htbl                      true
% 3.01/0.99  --gc_record_bc_elim                     false
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing Options
% 3.01/0.99  
% 3.01/0.99  --preprocessing_flag                    true
% 3.01/0.99  --time_out_prep_mult                    0.1
% 3.01/0.99  --splitting_mode                        input
% 3.01/0.99  --splitting_grd                         true
% 3.01/0.99  --splitting_cvd                         false
% 3.01/0.99  --splitting_cvd_svl                     false
% 3.01/0.99  --splitting_nvd                         32
% 3.01/0.99  --sub_typing                            true
% 3.01/0.99  --prep_gs_sim                           true
% 3.01/0.99  --prep_unflatten                        true
% 3.01/0.99  --prep_res_sim                          true
% 3.01/0.99  --prep_upred                            true
% 3.01/0.99  --prep_sem_filter                       exhaustive
% 3.01/0.99  --prep_sem_filter_out                   false
% 3.01/0.99  --pred_elim                             true
% 3.01/0.99  --res_sim_input                         true
% 3.01/0.99  --eq_ax_congr_red                       true
% 3.01/0.99  --pure_diseq_elim                       true
% 3.01/0.99  --brand_transform                       false
% 3.01/0.99  --non_eq_to_eq                          false
% 3.01/0.99  --prep_def_merge                        true
% 3.01/0.99  --prep_def_merge_prop_impl              false
% 3.01/0.99  --prep_def_merge_mbd                    true
% 3.01/0.99  --prep_def_merge_tr_red                 false
% 3.01/0.99  --prep_def_merge_tr_cl                  false
% 3.01/0.99  --smt_preprocessing                     true
% 3.01/0.99  --smt_ac_axioms                         fast
% 3.01/0.99  --preprocessed_out                      false
% 3.01/0.99  --preprocessed_stats                    false
% 3.01/0.99  
% 3.01/0.99  ------ Abstraction refinement Options
% 3.01/0.99  
% 3.01/0.99  --abstr_ref                             []
% 3.01/0.99  --abstr_ref_prep                        false
% 3.01/0.99  --abstr_ref_until_sat                   false
% 3.01/0.99  --abstr_ref_sig_restrict                funpre
% 3.01/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/0.99  --abstr_ref_under                       []
% 3.01/0.99  
% 3.01/0.99  ------ SAT Options
% 3.01/0.99  
% 3.01/0.99  --sat_mode                              false
% 3.01/0.99  --sat_fm_restart_options                ""
% 3.01/0.99  --sat_gr_def                            false
% 3.01/0.99  --sat_epr_types                         true
% 3.01/0.99  --sat_non_cyclic_types                  false
% 3.01/0.99  --sat_finite_models                     false
% 3.01/0.99  --sat_fm_lemmas                         false
% 3.01/0.99  --sat_fm_prep                           false
% 3.01/0.99  --sat_fm_uc_incr                        true
% 3.01/0.99  --sat_out_model                         small
% 3.01/0.99  --sat_out_clauses                       false
% 3.01/0.99  
% 3.01/0.99  ------ QBF Options
% 3.01/0.99  
% 3.01/0.99  --qbf_mode                              false
% 3.01/0.99  --qbf_elim_univ                         false
% 3.01/0.99  --qbf_dom_inst                          none
% 3.01/0.99  --qbf_dom_pre_inst                      false
% 3.01/0.99  --qbf_sk_in                             false
% 3.01/0.99  --qbf_pred_elim                         true
% 3.01/0.99  --qbf_split                             512
% 3.01/0.99  
% 3.01/0.99  ------ BMC1 Options
% 3.01/0.99  
% 3.01/0.99  --bmc1_incremental                      false
% 3.01/0.99  --bmc1_axioms                           reachable_all
% 3.01/0.99  --bmc1_min_bound                        0
% 3.01/0.99  --bmc1_max_bound                        -1
% 3.01/0.99  --bmc1_max_bound_default                -1
% 3.01/0.99  --bmc1_symbol_reachability              true
% 3.01/0.99  --bmc1_property_lemmas                  false
% 3.01/0.99  --bmc1_k_induction                      false
% 3.01/0.99  --bmc1_non_equiv_states                 false
% 3.01/0.99  --bmc1_deadlock                         false
% 3.01/0.99  --bmc1_ucm                              false
% 3.01/0.99  --bmc1_add_unsat_core                   none
% 3.01/0.99  --bmc1_unsat_core_children              false
% 3.01/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/0.99  --bmc1_out_stat                         full
% 3.01/0.99  --bmc1_ground_init                      false
% 3.01/0.99  --bmc1_pre_inst_next_state              false
% 3.01/0.99  --bmc1_pre_inst_state                   false
% 3.01/0.99  --bmc1_pre_inst_reach_state             false
% 3.01/0.99  --bmc1_out_unsat_core                   false
% 3.01/0.99  --bmc1_aig_witness_out                  false
% 3.01/0.99  --bmc1_verbose                          false
% 3.01/0.99  --bmc1_dump_clauses_tptp                false
% 3.01/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.01/0.99  --bmc1_dump_file                        -
% 3.01/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.01/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.01/0.99  --bmc1_ucm_extend_mode                  1
% 3.01/0.99  --bmc1_ucm_init_mode                    2
% 3.01/0.99  --bmc1_ucm_cone_mode                    none
% 3.01/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.01/0.99  --bmc1_ucm_relax_model                  4
% 3.01/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.01/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/0.99  --bmc1_ucm_layered_model                none
% 3.01/0.99  --bmc1_ucm_max_lemma_size               10
% 3.01/0.99  
% 3.01/0.99  ------ AIG Options
% 3.01/0.99  
% 3.01/0.99  --aig_mode                              false
% 3.01/0.99  
% 3.01/0.99  ------ Instantiation Options
% 3.01/0.99  
% 3.01/0.99  --instantiation_flag                    true
% 3.01/0.99  --inst_sos_flag                         false
% 3.01/0.99  --inst_sos_phase                        true
% 3.01/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel_side                     none
% 3.01/0.99  --inst_solver_per_active                1400
% 3.01/0.99  --inst_solver_calls_frac                1.
% 3.01/0.99  --inst_passive_queue_type               priority_queues
% 3.01/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/0.99  --inst_passive_queues_freq              [25;2]
% 3.01/0.99  --inst_dismatching                      true
% 3.01/0.99  --inst_eager_unprocessed_to_passive     true
% 3.01/0.99  --inst_prop_sim_given                   true
% 3.01/0.99  --inst_prop_sim_new                     false
% 3.01/0.99  --inst_subs_new                         false
% 3.01/0.99  --inst_eq_res_simp                      false
% 3.01/0.99  --inst_subs_given                       false
% 3.01/0.99  --inst_orphan_elimination               true
% 3.01/0.99  --inst_learning_loop_flag               true
% 3.01/0.99  --inst_learning_start                   3000
% 3.01/0.99  --inst_learning_factor                  2
% 3.01/0.99  --inst_start_prop_sim_after_learn       3
% 3.01/0.99  --inst_sel_renew                        solver
% 3.01/0.99  --inst_lit_activity_flag                true
% 3.01/0.99  --inst_restr_to_given                   false
% 3.01/0.99  --inst_activity_threshold               500
% 3.01/0.99  --inst_out_proof                        true
% 3.01/0.99  
% 3.01/0.99  ------ Resolution Options
% 3.01/0.99  
% 3.01/0.99  --resolution_flag                       false
% 3.01/0.99  --res_lit_sel                           adaptive
% 3.01/0.99  --res_lit_sel_side                      none
% 3.01/0.99  --res_ordering                          kbo
% 3.01/0.99  --res_to_prop_solver                    active
% 3.01/0.99  --res_prop_simpl_new                    false
% 3.01/0.99  --res_prop_simpl_given                  true
% 3.01/0.99  --res_passive_queue_type                priority_queues
% 3.01/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/0.99  --res_passive_queues_freq               [15;5]
% 3.01/0.99  --res_forward_subs                      full
% 3.01/0.99  --res_backward_subs                     full
% 3.01/0.99  --res_forward_subs_resolution           true
% 3.01/0.99  --res_backward_subs_resolution          true
% 3.01/0.99  --res_orphan_elimination                true
% 3.01/0.99  --res_time_limit                        2.
% 3.01/0.99  --res_out_proof                         true
% 3.01/0.99  
% 3.01/0.99  ------ Superposition Options
% 3.01/0.99  
% 3.01/0.99  --superposition_flag                    true
% 3.01/0.99  --sup_passive_queue_type                priority_queues
% 3.01/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.01/0.99  --demod_completeness_check              fast
% 3.01/0.99  --demod_use_ground                      true
% 3.01/0.99  --sup_to_prop_solver                    passive
% 3.01/0.99  --sup_prop_simpl_new                    true
% 3.01/0.99  --sup_prop_simpl_given                  true
% 3.01/0.99  --sup_fun_splitting                     false
% 3.01/0.99  --sup_smt_interval                      50000
% 3.01/0.99  
% 3.01/0.99  ------ Superposition Simplification Setup
% 3.01/0.99  
% 3.01/0.99  --sup_indices_passive                   []
% 3.01/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_full_bw                           [BwDemod]
% 3.01/0.99  --sup_immed_triv                        [TrivRules]
% 3.01/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_immed_bw_main                     []
% 3.01/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.99  
% 3.01/0.99  ------ Combination Options
% 3.01/0.99  
% 3.01/0.99  --comb_res_mult                         3
% 3.01/0.99  --comb_sup_mult                         2
% 3.01/0.99  --comb_inst_mult                        10
% 3.01/0.99  
% 3.01/0.99  ------ Debug Options
% 3.01/0.99  
% 3.01/0.99  --dbg_backtrace                         false
% 3.01/0.99  --dbg_dump_prop_clauses                 false
% 3.01/0.99  --dbg_dump_prop_clauses_file            -
% 3.01/0.99  --dbg_out_stat                          false
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  ------ Proving...
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  % SZS status Theorem for theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  fof(f10,axiom,(
% 3.01/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f30,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : ((! [X2] : ((u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/0.99    inference(ennf_transformation,[],[f10])).
% 3.01/0.99  
% 3.01/0.99  fof(f31,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : ((! [X2] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/0.99    inference(flattening,[],[f30])).
% 3.01/0.99  
% 3.01/0.99  fof(f66,plain,(
% 3.01/0.99    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f31])).
% 3.01/0.99  
% 3.01/0.99  fof(f12,conjecture,(
% 3.01/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f13,negated_conjecture,(
% 3.01/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 3.01/0.99    inference(negated_conjecture,[],[f12])).
% 3.01/0.99  
% 3.01/0.99  fof(f33,plain,(
% 3.01/0.99    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.01/0.99    inference(ennf_transformation,[],[f13])).
% 3.01/0.99  
% 3.01/0.99  fof(f34,plain,(
% 3.01/0.99    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.01/0.99    inference(flattening,[],[f33])).
% 3.01/0.99  
% 3.01/0.99  fof(f43,plain,(
% 3.01/0.99    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.01/0.99    inference(nnf_transformation,[],[f34])).
% 3.01/0.99  
% 3.01/0.99  fof(f44,plain,(
% 3.01/0.99    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.01/0.99    inference(flattening,[],[f43])).
% 3.01/0.99  
% 3.01/0.99  fof(f46,plain,(
% 3.01/0.99    ( ! [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,sK3) | ~m1_pre_topc(sK3,X0) | ~v1_tsep_1(sK3,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,sK3) | (m1_pre_topc(sK3,X0) & v1_tsep_1(sK3,X0))) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f45,plain,(
% 3.01/0.99    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,X1) | ~m1_pre_topc(X1,sK2) | ~v1_tsep_1(X1,sK2)) & (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,X1) | (m1_pre_topc(X1,sK2) & v1_tsep_1(X1,sK2))) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f47,plain,(
% 3.01/0.99    ((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_tsep_1(sK3,sK2)) & (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) | (m1_pre_topc(sK3,sK2) & v1_tsep_1(sK3,sK2))) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.01/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f44,f46,f45])).
% 3.01/0.99  
% 3.01/0.99  fof(f75,plain,(
% 3.01/0.99    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) | m1_pre_topc(sK3,sK2)),
% 3.01/0.99    inference(cnf_transformation,[],[f47])).
% 3.01/0.99  
% 3.01/0.99  fof(f73,plain,(
% 3.01/0.99    m1_pre_topc(sK3,sK2)),
% 3.01/0.99    inference(cnf_transformation,[],[f47])).
% 3.01/0.99  
% 3.01/0.99  fof(f69,plain,(
% 3.01/0.99    ~v2_struct_0(sK2)),
% 3.01/0.99    inference(cnf_transformation,[],[f47])).
% 3.01/0.99  
% 3.01/0.99  fof(f70,plain,(
% 3.01/0.99    v2_pre_topc(sK2)),
% 3.01/0.99    inference(cnf_transformation,[],[f47])).
% 3.01/0.99  
% 3.01/0.99  fof(f71,plain,(
% 3.01/0.99    l1_pre_topc(sK2)),
% 3.01/0.99    inference(cnf_transformation,[],[f47])).
% 3.01/0.99  
% 3.01/0.99  fof(f72,plain,(
% 3.01/0.99    ~v2_struct_0(sK3)),
% 3.01/0.99    inference(cnf_transformation,[],[f47])).
% 3.01/0.99  
% 3.01/0.99  fof(f4,axiom,(
% 3.01/0.99    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f19,plain,(
% 3.01/0.99    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.01/0.99    inference(ennf_transformation,[],[f4])).
% 3.01/0.99  
% 3.01/0.99  fof(f36,plain,(
% 3.01/0.99    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f37,plain,(
% 3.01/0.99    ! [X0] : ((v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.01/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f36])).
% 3.01/0.99  
% 3.01/0.99  fof(f52,plain,(
% 3.01/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f37])).
% 3.01/0.99  
% 3.01/0.99  fof(f7,axiom,(
% 3.01/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f24,plain,(
% 3.01/0.99    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/0.99    inference(ennf_transformation,[],[f7])).
% 3.01/0.99  
% 3.01/0.99  fof(f25,plain,(
% 3.01/0.99    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/0.99    inference(flattening,[],[f24])).
% 3.01/0.99  
% 3.01/0.99  fof(f61,plain,(
% 3.01/0.99    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f25])).
% 3.01/0.99  
% 3.01/0.99  fof(f2,axiom,(
% 3.01/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f16,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.01/0.99    inference(ennf_transformation,[],[f2])).
% 3.01/0.99  
% 3.01/0.99  fof(f35,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.01/0.99    inference(nnf_transformation,[],[f16])).
% 3.01/0.99  
% 3.01/0.99  fof(f49,plain,(
% 3.01/0.99    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f35])).
% 3.01/0.99  
% 3.01/0.99  fof(f8,axiom,(
% 3.01/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f26,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/0.99    inference(ennf_transformation,[],[f8])).
% 3.01/0.99  
% 3.01/0.99  fof(f27,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/0.99    inference(flattening,[],[f26])).
% 3.01/0.99  
% 3.01/0.99  fof(f42,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/0.99    inference(nnf_transformation,[],[f27])).
% 3.01/0.99  
% 3.01/0.99  fof(f62,plain,(
% 3.01/0.99    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f42])).
% 3.01/0.99  
% 3.01/0.99  fof(f3,axiom,(
% 3.01/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f17,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.01/0.99    inference(ennf_transformation,[],[f3])).
% 3.01/0.99  
% 3.01/0.99  fof(f18,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.01/0.99    inference(flattening,[],[f17])).
% 3.01/0.99  
% 3.01/0.99  fof(f51,plain,(
% 3.01/0.99    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f18])).
% 3.01/0.99  
% 3.01/0.99  fof(f53,plain,(
% 3.01/0.99    ( ! [X0] : (v1_xboole_0(sK0(X0)) | ~l1_pre_topc(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f37])).
% 3.01/0.99  
% 3.01/0.99  fof(f6,axiom,(
% 3.01/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f22,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/0.99    inference(ennf_transformation,[],[f6])).
% 3.01/0.99  
% 3.01/0.99  fof(f23,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/0.99    inference(flattening,[],[f22])).
% 3.01/0.99  
% 3.01/0.99  fof(f58,plain,(
% 3.01/0.99    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f23])).
% 3.01/0.99  
% 3.01/0.99  fof(f5,axiom,(
% 3.01/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f20,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.01/0.99    inference(ennf_transformation,[],[f5])).
% 3.01/0.99  
% 3.01/0.99  fof(f21,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.01/0.99    inference(flattening,[],[f20])).
% 3.01/0.99  
% 3.01/0.99  fof(f38,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.01/0.99    inference(nnf_transformation,[],[f21])).
% 3.01/0.99  
% 3.01/0.99  fof(f39,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.01/0.99    inference(rectify,[],[f38])).
% 3.01/0.99  
% 3.01/0.99  fof(f40,plain,(
% 3.01/0.99    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK1(X0,X1),X0) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f41,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK1(X0,X1),X0) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.01/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 3.01/0.99  
% 3.01/0.99  fof(f54,plain,(
% 3.01/0.99    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f41])).
% 3.01/0.99  
% 3.01/0.99  fof(f77,plain,(
% 3.01/0.99    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.01/0.99    inference(equality_resolution,[],[f54])).
% 3.01/0.99  
% 3.01/0.99  fof(f11,axiom,(
% 3.01/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f32,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.01/0.99    inference(ennf_transformation,[],[f11])).
% 3.01/0.99  
% 3.01/0.99  fof(f68,plain,(
% 3.01/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f32])).
% 3.01/0.99  
% 3.01/0.99  fof(f74,plain,(
% 3.01/0.99    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) | v1_tsep_1(sK3,sK2)),
% 3.01/0.99    inference(cnf_transformation,[],[f47])).
% 3.01/0.99  
% 3.01/0.99  fof(f1,axiom,(
% 3.01/0.99    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f14,plain,(
% 3.01/0.99    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.01/0.99    inference(ennf_transformation,[],[f1])).
% 3.01/0.99  
% 3.01/0.99  fof(f15,plain,(
% 3.01/0.99    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.01/0.99    inference(flattening,[],[f14])).
% 3.01/0.99  
% 3.01/0.99  fof(f48,plain,(
% 3.01/0.99    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f15])).
% 3.01/0.99  
% 3.01/0.99  fof(f59,plain,(
% 3.01/0.99    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f25])).
% 3.01/0.99  
% 3.01/0.99  fof(f67,plain,(
% 3.01/0.99    ( ! [X2,X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f31])).
% 3.01/0.99  
% 3.01/0.99  fof(f78,plain,(
% 3.01/0.99    ( ! [X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/0.99    inference(equality_resolution,[],[f67])).
% 3.01/0.99  
% 3.01/0.99  fof(f9,axiom,(
% 3.01/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f28,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/0.99    inference(ennf_transformation,[],[f9])).
% 3.01/0.99  
% 3.01/0.99  fof(f29,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/0.99    inference(flattening,[],[f28])).
% 3.01/0.99  
% 3.01/0.99  fof(f65,plain,(
% 3.01/0.99    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f29])).
% 3.01/0.99  
% 3.01/0.99  fof(f56,plain,(
% 3.01/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | u1_struct_0(X1) = sK1(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f41])).
% 3.01/0.99  
% 3.01/0.99  fof(f76,plain,(
% 3.01/0.99    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_tsep_1(sK3,sK2)),
% 3.01/0.99    inference(cnf_transformation,[],[f47])).
% 3.01/0.99  
% 3.01/0.99  fof(f57,plain,(
% 3.01/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(sK1(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f41])).
% 3.01/0.99  
% 3.01/0.99  fof(f63,plain,(
% 3.01/0.99    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f42])).
% 3.01/0.99  
% 3.01/0.99  fof(f50,plain,(
% 3.01/0.99    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f35])).
% 3.01/0.99  
% 3.01/0.99  cnf(c_19,plain,
% 3.01/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.01/0.99      | v2_struct_0(X1)
% 3.01/0.99      | v2_struct_0(X0)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_22,negated_conjecture,
% 3.01/0.99      ( m1_pre_topc(sK3,sK2)
% 3.01/0.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 3.01/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_24,negated_conjecture,
% 3.01/0.99      ( m1_pre_topc(sK3,sK2) ),
% 3.01/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_165,negated_conjecture,
% 3.01/0.99      ( m1_pre_topc(sK3,sK2) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_22,c_24]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_703,plain,
% 3.01/0.99      ( v2_struct_0(X0)
% 3.01/0.99      | v2_struct_0(X1)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1)
% 3.01/0.99      | sK3 != X0
% 3.01/0.99      | sK2 != X1 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_165]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_704,plain,
% 3.01/0.99      ( v2_struct_0(sK3)
% 3.01/0.99      | v2_struct_0(sK2)
% 3.01/0.99      | ~ v2_pre_topc(sK2)
% 3.01/0.99      | ~ l1_pre_topc(sK2)
% 3.01/0.99      | u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_703]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_28,negated_conjecture,
% 3.01/0.99      ( ~ v2_struct_0(sK2) ),
% 3.01/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_27,negated_conjecture,
% 3.01/0.99      ( v2_pre_topc(sK2) ),
% 3.01/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_26,negated_conjecture,
% 3.01/0.99      ( l1_pre_topc(sK2) ),
% 3.01/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_25,negated_conjecture,
% 3.01/0.99      ( ~ v2_struct_0(sK3) ),
% 3.01/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_706,plain,
% 3.01/0.99      ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_704,c_28,c_27,c_26,c_25]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3422,plain,
% 3.01/0.99      ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_706]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_5,plain,
% 3.01/0.99      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/0.99      | ~ l1_pre_topc(X0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3435,plain,
% 3.01/0.99      ( m1_subset_1(sK0(X0_51),k1_zfmisc_1(u1_struct_0(X0_51)))
% 3.01/0.99      | ~ l1_pre_topc(X0_51) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3967,plain,
% 3.01/0.99      ( m1_subset_1(sK0(X0_51),k1_zfmisc_1(u1_struct_0(X0_51))) = iProver_top
% 3.01/0.99      | l1_pre_topc(X0_51) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_3435]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4303,plain,
% 3.01/0.99      ( m1_subset_1(sK0(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.01/0.99      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_3422,c_3967]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_29,plain,
% 3.01/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_30,plain,
% 3.01/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_31,plain,
% 3.01/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_11,plain,
% 3.01/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.01/0.99      | v2_struct_0(X1)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.01/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_733,plain,
% 3.01/0.99      ( v2_struct_0(X0)
% 3.01/0.99      | ~ v2_pre_topc(X0)
% 3.01/0.99      | ~ l1_pre_topc(X0)
% 3.01/0.99      | l1_pre_topc(k8_tmap_1(X0,X1))
% 3.01/0.99      | sK3 != X1
% 3.01/0.99      | sK2 != X0 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_165]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_734,plain,
% 3.01/0.99      ( v2_struct_0(sK2)
% 3.01/0.99      | ~ v2_pre_topc(sK2)
% 3.01/0.99      | l1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.01/0.99      | ~ l1_pre_topc(sK2) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_733]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_735,plain,
% 3.01/0.99      ( v2_struct_0(sK2) = iProver_top
% 3.01/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.01/0.99      | l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.01/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_734]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4320,plain,
% 3.01/0.99      ( m1_subset_1(sK0(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_4303,c_29,c_30,c_31,c_735]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/0.99      | r2_hidden(X0,u1_pre_topc(X1))
% 3.01/0.99      | ~ v3_pre_topc(X0,X1)
% 3.01/0.99      | ~ l1_pre_topc(X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_15,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/0.99      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.01/0.99      | v2_struct_0(X1)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_473,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/0.99      | ~ v3_pre_topc(X0,X1)
% 3.01/0.99      | v2_struct_0(X1)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 3.01/0.99      inference(resolution,[status(thm)],[c_2,c_15]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_868,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/0.99      | ~ v3_pre_topc(X0,X1)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
% 3.01/0.99      | sK2 != X1 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_473,c_28]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_869,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.01/0.99      | ~ v3_pre_topc(X0,sK2)
% 3.01/0.99      | ~ v2_pre_topc(sK2)
% 3.01/0.99      | ~ l1_pre_topc(sK2)
% 3.01/0.99      | k5_tmap_1(sK2,X0) = u1_pre_topc(sK2) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_868]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_873,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.01/0.99      | ~ v3_pre_topc(X0,sK2)
% 3.01/0.99      | k5_tmap_1(sK2,X0) = u1_pre_topc(sK2) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_869,c_27,c_26]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3413,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.01/0.99      | ~ v3_pre_topc(X0_49,sK2)
% 3.01/0.99      | k5_tmap_1(sK2,X0_49) = u1_pre_topc(sK2) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_873]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3990,plain,
% 3.01/0.99      ( k5_tmap_1(sK2,X0_49) = u1_pre_topc(sK2)
% 3.01/0.99      | m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.01/0.99      | v3_pre_topc(X0_49,sK2) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_3413]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_5020,plain,
% 3.01/0.99      ( k5_tmap_1(sK2,sK0(k8_tmap_1(sK2,sK3))) = u1_pre_topc(sK2)
% 3.01/0.99      | v3_pre_topc(sK0(k8_tmap_1(sK2,sK3)),sK2) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_4320,c_3990]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/0.99      | v3_pre_topc(X0,X1)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ v1_xboole_0(X0)
% 3.01/0.99      | ~ l1_pre_topc(X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4,plain,
% 3.01/0.99      ( v1_xboole_0(sK0(X0)) | ~ l1_pre_topc(X0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_390,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/0.99      | v3_pre_topc(X0,X1)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X2)
% 3.01/0.99      | sK0(X2) != X0 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_4]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_391,plain,
% 3.01/0.99      ( ~ m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/0.99      | v3_pre_topc(sK0(X0),X1)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X0) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_390]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3432,plain,
% 3.01/0.99      ( ~ m1_subset_1(sK0(X0_51),k1_zfmisc_1(u1_struct_0(X1_51)))
% 3.01/0.99      | v3_pre_topc(sK0(X0_51),X1_51)
% 3.01/0.99      | ~ v2_pre_topc(X1_51)
% 3.01/0.99      | ~ l1_pre_topc(X1_51)
% 3.01/0.99      | ~ l1_pre_topc(X0_51) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_391]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3970,plain,
% 3.01/0.99      ( m1_subset_1(sK0(X0_51),k1_zfmisc_1(u1_struct_0(X1_51))) != iProver_top
% 3.01/0.99      | v3_pre_topc(sK0(X0_51),X1_51) = iProver_top
% 3.01/0.99      | v2_pre_topc(X1_51) != iProver_top
% 3.01/0.99      | l1_pre_topc(X1_51) != iProver_top
% 3.01/0.99      | l1_pre_topc(X0_51) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_3432]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4332,plain,
% 3.01/0.99      ( v3_pre_topc(sK0(k8_tmap_1(sK2,sK3)),sK2) = iProver_top
% 3.01/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.01/0.99      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.01/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_4320,c_3970]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_6257,plain,
% 3.01/0.99      ( k5_tmap_1(sK2,sK0(k8_tmap_1(sK2,sK3))) = u1_pre_topc(sK2) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_5020,c_29,c_30,c_31,c_735,c_4332]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_10,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/0.99      | v2_struct_0(X1)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_946,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0)
% 3.01/0.99      | sK2 != X1 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_28]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_947,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.01/0.99      | ~ v2_pre_topc(sK2)
% 3.01/0.99      | ~ l1_pre_topc(sK2)
% 3.01/0.99      | g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,X0)) = k6_tmap_1(sK2,X0) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_946]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_951,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.01/0.99      | g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,X0)) = k6_tmap_1(sK2,X0) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_947,c_27,c_26]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3409,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.01/0.99      | g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,X0_49)) = k6_tmap_1(sK2,X0_49) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_951]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3994,plain,
% 3.01/0.99      ( g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,X0_49)) = k6_tmap_1(sK2,X0_49)
% 3.01/0.99      | m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_3409]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4858,plain,
% 3.01/0.99      ( g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,sK0(k8_tmap_1(sK2,sK3)))) = k6_tmap_1(sK2,sK0(k8_tmap_1(sK2,sK3))) ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_4320,c_3994]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_6260,plain,
% 3.01/0.99      ( k6_tmap_1(sK2,sK0(k8_tmap_1(sK2,sK3))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.01/0.99      inference(demodulation,[status(thm)],[c_6257,c_4858]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_9,plain,
% 3.01/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.01/0.99      | ~ v1_tsep_1(X0,X1)
% 3.01/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.01/0.99      | ~ l1_pre_topc(X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_20,plain,
% 3.01/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.01/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/0.99      | ~ l1_pre_topc(X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_192,plain,
% 3.01/0.99      ( ~ v1_tsep_1(X0,X1)
% 3.01/0.99      | ~ m1_pre_topc(X0,X1)
% 3.01/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.01/0.99      | ~ l1_pre_topc(X1) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_9,c_20]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_193,plain,
% 3.01/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.01/0.99      | ~ v1_tsep_1(X0,X1)
% 3.01/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.01/0.99      | ~ l1_pre_topc(X1) ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_192]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_23,negated_conjecture,
% 3.01/0.99      ( v1_tsep_1(sK3,sK2)
% 3.01/0.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 3.01/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_241,plain,
% 3.01/0.99      ( v1_tsep_1(sK3,sK2)
% 3.01/0.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 3.01/0.99      inference(prop_impl,[status(thm)],[c_23]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_602,plain,
% 3.01/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.01/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 3.01/0.99      | sK3 != X0
% 3.01/0.99      | sK2 != X1 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_193,c_241]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_603,plain,
% 3.01/0.99      ( ~ m1_pre_topc(sK3,sK2)
% 3.01/0.99      | v3_pre_topc(u1_struct_0(sK3),sK2)
% 3.01/0.99      | ~ l1_pre_topc(sK2)
% 3.01/0.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_602]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_605,plain,
% 3.01/0.99      ( v3_pre_topc(u1_struct_0(sK3),sK2)
% 3.01/0.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_603,c_26,c_24]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3428,plain,
% 3.01/0.99      ( v3_pre_topc(u1_struct_0(sK3),sK2)
% 3.01/0.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_605]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3973,plain,
% 3.01/0.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 3.01/0.99      | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_3428]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3454,plain,
% 3.01/0.99      ( X0_51 != X1_51 | u1_struct_0(X0_51) = u1_struct_0(X1_51) ),
% 3.01/0.99      theory(equality) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3466,plain,
% 3.01/0.99      ( sK2 != sK2 | u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_3454]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3455,plain,
% 3.01/0.99      ( u1_pre_topc(X0_51) = u1_pre_topc(X1_51) | X0_51 != X1_51 ),
% 3.01/0.99      theory(equality) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3467,plain,
% 3.01/0.99      ( u1_pre_topc(sK2) = u1_pre_topc(sK2) | sK2 != sK2 ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_3455]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3449,plain,( X0_51 = X0_51 ),theory(equality) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3481,plain,
% 3.01/0.99      ( sK2 = sK2 ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_3449]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_0,plain,
% 3.01/0.99      ( ~ l1_pre_topc(X0)
% 3.01/0.99      | ~ v1_pre_topc(X0)
% 3.01/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.01/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_13,plain,
% 3.01/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.01/0.99      | v2_struct_0(X1)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | v1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.01/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_711,plain,
% 3.01/0.99      ( v2_struct_0(X0)
% 3.01/0.99      | ~ v2_pre_topc(X0)
% 3.01/0.99      | ~ l1_pre_topc(X0)
% 3.01/0.99      | v1_pre_topc(k8_tmap_1(X0,X1))
% 3.01/0.99      | sK3 != X1
% 3.01/0.99      | sK2 != X0 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_165]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_712,plain,
% 3.01/0.99      ( v2_struct_0(sK2)
% 3.01/0.99      | ~ v2_pre_topc(sK2)
% 3.01/0.99      | ~ l1_pre_topc(sK2)
% 3.01/0.99      | v1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_711]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_714,plain,
% 3.01/0.99      ( v1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_712,c_28,c_27,c_26]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_763,plain,
% 3.01/0.99      ( ~ l1_pre_topc(X0)
% 3.01/0.99      | k8_tmap_1(sK2,sK3) != X0
% 3.01/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_714]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_764,plain,
% 3.01/0.99      ( ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.01/0.99      | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_763]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_766,plain,
% 3.01/0.99      ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_764,c_28,c_27,c_26,c_734]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3419,plain,
% 3.01/0.99      ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_766]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4458,plain,
% 3.01/0.99      ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK3) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_3449]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3452,plain,
% 3.01/0.99      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 3.01/0.99      theory(equality) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4403,plain,
% 3.01/0.99      ( X0_51 != X1_51
% 3.01/0.99      | k8_tmap_1(sK2,sK3) != X1_51
% 3.01/0.99      | k8_tmap_1(sK2,sK3) = X0_51 ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_3452]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4457,plain,
% 3.01/0.99      ( X0_51 != k8_tmap_1(sK2,sK3)
% 3.01/0.99      | k8_tmap_1(sK2,sK3) = X0_51
% 3.01/0.99      | k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_4403]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4561,plain,
% 3.01/0.99      ( k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3)
% 3.01/0.99      | k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
% 3.01/0.99      | g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) != k8_tmap_1(sK2,sK3) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_4457]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4263,plain,
% 3.01/0.99      ( k8_tmap_1(sK2,sK3) != X0_51
% 3.01/0.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0_51
% 3.01/0.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_3452]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4631,plain,
% 3.01/0.99      ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
% 3.01/0.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 3.01/0.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3))) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_4263]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3456,plain,
% 3.01/0.99      ( X0_52 != X1_52
% 3.01/0.99      | g1_pre_topc(X0_49,X0_52) = g1_pre_topc(X1_49,X1_52)
% 3.01/0.99      | X0_49 != X1_49 ),
% 3.01/0.99      theory(equality) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4751,plain,
% 3.01/0.99      ( u1_pre_topc(sK2) != u1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.01/0.99      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK2,sK3)),u1_pre_topc(k8_tmap_1(sK2,sK3)))
% 3.01/0.99      | u1_struct_0(sK2) != u1_struct_0(k8_tmap_1(sK2,sK3)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_3456]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3451,plain,
% 3.01/0.99      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 3.01/0.99      theory(equality) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4575,plain,
% 3.01/0.99      ( X0_49 != X1_49
% 3.01/0.99      | X0_49 = u1_struct_0(X0_51)
% 3.01/0.99      | u1_struct_0(X0_51) != X1_49 ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_3451]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4707,plain,
% 3.01/0.99      ( X0_49 = u1_struct_0(k8_tmap_1(sK2,sK3))
% 3.01/0.99      | X0_49 != u1_struct_0(sK2)
% 3.01/0.99      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(sK2) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_4575]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4979,plain,
% 3.01/0.99      ( u1_struct_0(X0_51) = u1_struct_0(k8_tmap_1(sK2,sK3))
% 3.01/0.99      | u1_struct_0(X0_51) != u1_struct_0(sK2)
% 3.01/0.99      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(sK2) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_4707]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4981,plain,
% 3.01/0.99      ( u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(sK2)
% 3.01/0.99      | u1_struct_0(sK2) = u1_struct_0(k8_tmap_1(sK2,sK3))
% 3.01/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_4979]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_692,plain,
% 3.01/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | sK3 != X0
% 3.01/0.99      | sK2 != X1 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_165]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_693,plain,
% 3.01/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.01/0.99      | ~ l1_pre_topc(sK2) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_692]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_695,plain,
% 3.01/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_693,c_26]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3423,plain,
% 3.01/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_695]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3977,plain,
% 3.01/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_3423]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_5018,plain,
% 3.01/0.99      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(sK2)
% 3.01/0.99      | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_3977,c_3990]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_18,plain,
% 3.01/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.01/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/0.99      | v2_struct_0(X1)
% 3.01/0.99      | v2_struct_0(X0)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.01/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_177,plain,
% 3.01/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.01/0.99      | v2_struct_0(X1)
% 3.01/0.99      | v2_struct_0(X0)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_18,c_20]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_178,plain,
% 3.01/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.01/0.99      | v2_struct_0(X0)
% 3.01/0.99      | v2_struct_0(X1)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_177]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_684,plain,
% 3.01/0.99      ( v2_struct_0(X0)
% 3.01/0.99      | v2_struct_0(X1)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0))
% 3.01/0.99      | sK3 != X0
% 3.01/0.99      | sK2 != X1 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_178,c_165]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_685,plain,
% 3.01/1.00      ( v2_struct_0(sK3)
% 3.01/1.00      | v2_struct_0(sK2)
% 3.01/1.00      | ~ v2_pre_topc(sK2)
% 3.01/1.00      | ~ l1_pre_topc(sK2)
% 3.01/1.00      | k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_684]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_687,plain,
% 3.01/1.00      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_685,c_28,c_27,c_26,c_25]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3424,plain,
% 3.01/1.00      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_687]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5040,plain,
% 3.01/1.00      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2)
% 3.01/1.00      | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_5018,c_3424]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5046,plain,
% 3.01/1.00      ( ~ v3_pre_topc(u1_struct_0(sK3),sK2)
% 3.01/1.00      | u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2) ),
% 3.01/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5040]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3453,plain,
% 3.01/1.00      ( X0_52 != X1_52 | X2_52 != X1_52 | X2_52 = X0_52 ),
% 3.01/1.00      theory(equality) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5093,plain,
% 3.01/1.00      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != X0_52
% 3.01/1.00      | u1_pre_topc(sK2) != X0_52
% 3.01/1.00      | u1_pre_topc(sK2) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_3453]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5540,plain,
% 3.01/1.00      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
% 3.01/1.00      | u1_pre_topc(sK2) = u1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.01/1.00      | u1_pre_topc(sK2) != u1_pre_topc(sK2) ),
% 3.01/1.00      inference(instantiation,[status(thm)],[c_5093]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5681,plain,
% 3.01/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_3973,c_3466,c_3467,c_3481,c_3428,c_3422,c_3419,c_4458,
% 3.01/1.00                 c_4561,c_4631,c_4751,c_4981,c_5046,c_5540]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6265,plain,
% 3.01/1.00      ( k6_tmap_1(sK2,sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
% 3.01/1.00      inference(light_normalisation,[status(thm)],[c_6260,c_5681]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_16,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_928,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
% 3.01/1.00      | sK2 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_28]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_929,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.01/1.00      | ~ v2_pre_topc(sK2)
% 3.01/1.00      | ~ l1_pre_topc(sK2)
% 3.01/1.00      | u1_pre_topc(k6_tmap_1(sK2,X0)) = k5_tmap_1(sK2,X0) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_928]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_933,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.01/1.00      | u1_pre_topc(k6_tmap_1(sK2,X0)) = k5_tmap_1(sK2,X0) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_929,c_27,c_26]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3410,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.01/1.00      | u1_pre_topc(k6_tmap_1(sK2,X0_49)) = k5_tmap_1(sK2,X0_49) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_933]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3993,plain,
% 3.01/1.00      ( u1_pre_topc(k6_tmap_1(sK2,X0_49)) = k5_tmap_1(sK2,X0_49)
% 3.01/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_3410]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_4597,plain,
% 3.01/1.00      ( u1_pre_topc(k6_tmap_1(sK2,sK0(k8_tmap_1(sK2,sK3)))) = k5_tmap_1(sK2,sK0(k8_tmap_1(sK2,sK3))) ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_4320,c_3993]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6261,plain,
% 3.01/1.00      ( u1_pre_topc(k6_tmap_1(sK2,sK0(k8_tmap_1(sK2,sK3)))) = u1_pre_topc(sK2) ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_6257,c_4597]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6266,plain,
% 3.01/1.00      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) = u1_pre_topc(sK2) ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_6265,c_6261]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_7,plain,
% 3.01/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | v1_tsep_1(X0,X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | sK1(X1,X0) = u1_struct_0(X0) ),
% 3.01/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_528,plain,
% 3.01/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | sK1(X1,X0) = u1_struct_0(X0) ),
% 3.01/1.00      inference(resolution,[status(thm)],[c_7,c_193]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_656,plain,
% 3.01/1.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | sK1(X1,X0) = u1_struct_0(X0)
% 3.01/1.00      | sK3 != X0
% 3.01/1.00      | sK2 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_528,c_165]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_657,plain,
% 3.01/1.00      ( v3_pre_topc(u1_struct_0(sK3),sK2)
% 3.01/1.00      | ~ l1_pre_topc(sK2)
% 3.01/1.00      | sK1(sK2,sK3) = u1_struct_0(sK3) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_656]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_659,plain,
% 3.01/1.00      ( v3_pre_topc(u1_struct_0(sK3),sK2)
% 3.01/1.00      | sK1(sK2,sK3) = u1_struct_0(sK3) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_657,c_26]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3426,plain,
% 3.01/1.00      ( v3_pre_topc(u1_struct_0(sK3),sK2)
% 3.01/1.00      | sK1(sK2,sK3) = u1_struct_0(sK3) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_659]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3975,plain,
% 3.01/1.00      ( sK1(sK2,sK3) = u1_struct_0(sK3)
% 3.01/1.00      | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_3426]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_21,negated_conjecture,
% 3.01/1.00      ( ~ m1_pre_topc(sK3,sK2)
% 3.01/1.00      | ~ v1_tsep_1(sK3,sK2)
% 3.01/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 3.01/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_239,plain,
% 3.01/1.00      ( ~ v1_tsep_1(sK3,sK2)
% 3.01/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 3.01/1.00      inference(prop_impl,[status(thm)],[c_24,c_21]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_577,plain,
% 3.01/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | sK1(X1,X0) = u1_struct_0(X0)
% 3.01/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 3.01/1.00      | sK3 != X0
% 3.01/1.00      | sK2 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_239]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_578,plain,
% 3.01/1.00      ( ~ m1_pre_topc(sK3,sK2)
% 3.01/1.00      | ~ l1_pre_topc(sK2)
% 3.01/1.00      | sK1(sK2,sK3) = u1_struct_0(sK3)
% 3.01/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_577]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_580,plain,
% 3.01/1.00      ( sK1(sK2,sK3) = u1_struct_0(sK3)
% 3.01/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_578,c_26,c_24]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3430,plain,
% 3.01/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 3.01/1.00      | sK1(sK2,sK3) = u1_struct_0(sK3) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_580]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5661,plain,
% 3.01/1.00      ( sK1(sK2,sK3) = u1_struct_0(sK3) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_3975,c_3466,c_3467,c_3481,c_3430,c_3428,c_3422,c_3419,
% 3.01/1.00                 c_4458,c_4561,c_4631,c_4751,c_4981,c_5046,c_5540]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_6,plain,
% 3.01/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | v1_tsep_1(X0,X1)
% 3.01/1.00      | ~ v3_pre_topc(sK1(X1,X0),X1)
% 3.01/1.00      | ~ l1_pre_topc(X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_588,plain,
% 3.01/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.01/1.00      | ~ v3_pre_topc(sK1(X1,X0),X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 3.01/1.00      | sK3 != X0
% 3.01/1.00      | sK2 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_239]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_589,plain,
% 3.01/1.00      ( ~ m1_pre_topc(sK3,sK2)
% 3.01/1.00      | ~ v3_pre_topc(sK1(sK2,sK3),sK2)
% 3.01/1.00      | ~ l1_pre_topc(sK2)
% 3.01/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_588]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_591,plain,
% 3.01/1.00      ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
% 3.01/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_589,c_26,c_24]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3429,plain,
% 3.01/1.00      ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
% 3.01/1.00      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_591]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3972,plain,
% 3.01/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 3.01/1.00      | v3_pre_topc(sK1(sK2,sK3),sK2) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_3429]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5664,plain,
% 3.01/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 3.01/1.00      | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
% 3.01/1.00      inference(demodulation,[status(thm)],[c_5661,c_3972]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_14,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | r2_hidden(X0,u1_pre_topc(X1))
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_1,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.01/1.00      | v3_pre_topc(X0,X1)
% 3.01/1.00      | ~ l1_pre_topc(X1) ),
% 3.01/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_450,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | v3_pre_topc(X0,X1)
% 3.01/1.00      | v2_struct_0(X1)
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
% 3.01/1.00      inference(resolution,[status(thm)],[c_14,c_1]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_889,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.01/1.00      | v3_pre_topc(X0,X1)
% 3.01/1.00      | ~ v2_pre_topc(X1)
% 3.01/1.00      | ~ l1_pre_topc(X1)
% 3.01/1.00      | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
% 3.01/1.00      | sK2 != X1 ),
% 3.01/1.00      inference(resolution_lifted,[status(thm)],[c_450,c_28]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_890,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.01/1.00      | v3_pre_topc(X0,sK2)
% 3.01/1.00      | ~ v2_pre_topc(sK2)
% 3.01/1.00      | ~ l1_pre_topc(sK2)
% 3.01/1.00      | k5_tmap_1(sK2,X0) != u1_pre_topc(sK2) ),
% 3.01/1.00      inference(unflattening,[status(thm)],[c_889]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_894,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.01/1.00      | v3_pre_topc(X0,sK2)
% 3.01/1.00      | k5_tmap_1(sK2,X0) != u1_pre_topc(sK2) ),
% 3.01/1.00      inference(global_propositional_subsumption,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_890,c_27,c_26]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3412,plain,
% 3.01/1.00      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.01/1.00      | v3_pre_topc(X0_49,sK2)
% 3.01/1.00      | k5_tmap_1(sK2,X0_49) != u1_pre_topc(sK2) ),
% 3.01/1.00      inference(subtyping,[status(esa)],[c_894]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_3991,plain,
% 3.01/1.00      ( k5_tmap_1(sK2,X0_49) != u1_pre_topc(sK2)
% 3.01/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.01/1.00      | v3_pre_topc(X0_49,sK2) = iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_3412]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_5163,plain,
% 3.01/1.00      ( u1_pre_topc(k8_tmap_1(sK2,sK3)) != u1_pre_topc(sK2)
% 3.01/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.01/1.00      | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
% 3.01/1.00      inference(superposition,[status(thm)],[c_3424,c_3991]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(c_694,plain,
% 3.01/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.01/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.01/1.00      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 3.01/1.00  
% 3.01/1.00  cnf(contradiction,plain,
% 3.01/1.00      ( $false ),
% 3.01/1.00      inference(minisat,
% 3.01/1.00                [status(thm)],
% 3.01/1.00                [c_6266,c_5681,c_5664,c_5163,c_694,c_31]) ).
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  ------                               Statistics
% 3.01/1.00  
% 3.01/1.00  ------ General
% 3.01/1.00  
% 3.01/1.00  abstr_ref_over_cycles:                  0
% 3.01/1.00  abstr_ref_under_cycles:                 0
% 3.01/1.00  gc_basic_clause_elim:                   0
% 3.01/1.00  forced_gc_time:                         0
% 3.01/1.00  parsing_time:                           0.012
% 3.01/1.00  unif_index_cands_time:                  0.
% 3.01/1.00  unif_index_add_time:                    0.
% 3.01/1.00  orderings_time:                         0.
% 3.01/1.00  out_proof_time:                         0.013
% 3.01/1.00  total_time:                             0.177
% 3.01/1.00  num_of_symbols:                         61
% 3.01/1.00  num_of_terms:                           2398
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing
% 3.01/1.00  
% 3.01/1.00  num_of_splits:                          5
% 3.01/1.00  num_of_split_atoms:                     5
% 3.01/1.00  num_of_reused_defs:                     0
% 3.01/1.00  num_eq_ax_congr_red:                    12
% 3.01/1.00  num_of_sem_filtered_clauses:            1
% 3.01/1.00  num_of_subtypes:                        4
% 3.01/1.00  monotx_restored_types:                  0
% 3.01/1.00  sat_num_of_epr_types:                   0
% 3.01/1.00  sat_num_of_non_cyclic_types:            0
% 3.01/1.00  sat_guarded_non_collapsed_types:        0
% 3.01/1.00  num_pure_diseq_elim:                    0
% 3.01/1.00  simp_replaced_by:                       0
% 3.01/1.00  res_preprocessed:                       158
% 3.01/1.00  prep_upred:                             0
% 3.01/1.00  prep_unflattend:                        123
% 3.01/1.00  smt_new_axioms:                         0
% 3.01/1.00  pred_elim_cands:                        4
% 3.01/1.00  pred_elim:                              6
% 3.01/1.00  pred_elim_cl:                           1
% 3.01/1.00  pred_elim_cycles:                       11
% 3.01/1.00  merged_defs:                            2
% 3.01/1.00  merged_defs_ncl:                        0
% 3.01/1.00  bin_hyper_res:                          2
% 3.01/1.00  prep_cycles:                            4
% 3.01/1.00  pred_elim_time:                         0.058
% 3.01/1.00  splitting_time:                         0.
% 3.01/1.00  sem_filter_time:                        0.
% 3.01/1.00  monotx_time:                            0.
% 3.01/1.00  subtype_inf_time:                       0.
% 3.01/1.00  
% 3.01/1.00  ------ Problem properties
% 3.01/1.00  
% 3.01/1.00  clauses:                                32
% 3.01/1.00  conjectures:                            2
% 3.01/1.00  epr:                                    7
% 3.01/1.00  horn:                                   29
% 3.01/1.00  ground:                                 20
% 3.01/1.00  unary:                                  8
% 3.01/1.00  binary:                                 11
% 3.01/1.00  lits:                                   73
% 3.01/1.00  lits_eq:                                19
% 3.01/1.00  fd_pure:                                0
% 3.01/1.00  fd_pseudo:                              0
% 3.01/1.00  fd_cond:                                0
% 3.01/1.00  fd_pseudo_cond:                         0
% 3.01/1.00  ac_symbols:                             0
% 3.01/1.00  
% 3.01/1.00  ------ Propositional Solver
% 3.01/1.00  
% 3.01/1.00  prop_solver_calls:                      29
% 3.01/1.00  prop_fast_solver_calls:                 1626
% 3.01/1.00  smt_solver_calls:                       0
% 3.01/1.00  smt_fast_solver_calls:                  0
% 3.01/1.00  prop_num_of_clauses:                    1139
% 3.01/1.00  prop_preprocess_simplified:             4979
% 3.01/1.00  prop_fo_subsumed:                       72
% 3.01/1.00  prop_solver_time:                       0.
% 3.01/1.00  smt_solver_time:                        0.
% 3.01/1.00  smt_fast_solver_time:                   0.
% 3.01/1.00  prop_fast_solver_time:                  0.
% 3.01/1.00  prop_unsat_core_time:                   0.
% 3.01/1.00  
% 3.01/1.00  ------ QBF
% 3.01/1.00  
% 3.01/1.00  qbf_q_res:                              0
% 3.01/1.00  qbf_num_tautologies:                    0
% 3.01/1.00  qbf_prep_cycles:                        0
% 3.01/1.00  
% 3.01/1.00  ------ BMC1
% 3.01/1.00  
% 3.01/1.00  bmc1_current_bound:                     -1
% 3.01/1.00  bmc1_last_solved_bound:                 -1
% 3.01/1.00  bmc1_unsat_core_size:                   -1
% 3.01/1.00  bmc1_unsat_core_parents_size:           -1
% 3.01/1.00  bmc1_merge_next_fun:                    0
% 3.01/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.01/1.00  
% 3.01/1.00  ------ Instantiation
% 3.01/1.00  
% 3.01/1.00  inst_num_of_clauses:                    338
% 3.01/1.00  inst_num_in_passive:                    17
% 3.01/1.00  inst_num_in_active:                     258
% 3.01/1.00  inst_num_in_unprocessed:                63
% 3.01/1.00  inst_num_of_loops:                      290
% 3.01/1.00  inst_num_of_learning_restarts:          0
% 3.01/1.00  inst_num_moves_active_passive:          25
% 3.01/1.00  inst_lit_activity:                      0
% 3.01/1.00  inst_lit_activity_moves:                0
% 3.01/1.00  inst_num_tautologies:                   0
% 3.01/1.00  inst_num_prop_implied:                  0
% 3.01/1.00  inst_num_existing_simplified:           0
% 3.01/1.00  inst_num_eq_res_simplified:             0
% 3.01/1.00  inst_num_child_elim:                    0
% 3.01/1.00  inst_num_of_dismatching_blockings:      194
% 3.01/1.00  inst_num_of_non_proper_insts:           454
% 3.01/1.00  inst_num_of_duplicates:                 0
% 3.01/1.00  inst_inst_num_from_inst_to_res:         0
% 3.01/1.00  inst_dismatching_checking_time:         0.
% 3.01/1.00  
% 3.01/1.00  ------ Resolution
% 3.01/1.00  
% 3.01/1.00  res_num_of_clauses:                     0
% 3.01/1.00  res_num_in_passive:                     0
% 3.01/1.00  res_num_in_active:                      0
% 3.01/1.00  res_num_of_loops:                       162
% 3.01/1.00  res_forward_subset_subsumed:            89
% 3.01/1.00  res_backward_subset_subsumed:           2
% 3.01/1.00  res_forward_subsumed:                   2
% 3.01/1.00  res_backward_subsumed:                  0
% 3.01/1.00  res_forward_subsumption_resolution:     0
% 3.01/1.00  res_backward_subsumption_resolution:    0
% 3.01/1.00  res_clause_to_clause_subsumption:       132
% 3.01/1.00  res_orphan_elimination:                 0
% 3.01/1.00  res_tautology_del:                      118
% 3.01/1.00  res_num_eq_res_simplified:              0
% 3.01/1.00  res_num_sel_changes:                    0
% 3.01/1.00  res_moves_from_active_to_pass:          0
% 3.01/1.00  
% 3.01/1.00  ------ Superposition
% 3.01/1.00  
% 3.01/1.00  sup_time_total:                         0.
% 3.01/1.00  sup_time_generating:                    0.
% 3.01/1.00  sup_time_sim_full:                      0.
% 3.01/1.00  sup_time_sim_immed:                     0.
% 3.01/1.00  
% 3.01/1.00  sup_num_of_clauses:                     62
% 3.01/1.00  sup_num_in_active:                      46
% 3.01/1.00  sup_num_in_passive:                     16
% 3.01/1.00  sup_num_of_loops:                       56
% 3.01/1.00  sup_fw_superposition:                   27
% 3.01/1.00  sup_bw_superposition:                   8
% 3.01/1.00  sup_immediate_simplified:               6
% 3.01/1.00  sup_given_eliminated:                   0
% 3.01/1.00  comparisons_done:                       0
% 3.01/1.00  comparisons_avoided:                    0
% 3.01/1.00  
% 3.01/1.00  ------ Simplifications
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  sim_fw_subset_subsumed:                 1
% 3.01/1.00  sim_bw_subset_subsumed:                 1
% 3.01/1.00  sim_fw_subsumed:                        0
% 3.01/1.00  sim_bw_subsumed:                        0
% 3.01/1.00  sim_fw_subsumption_res:                 0
% 3.01/1.00  sim_bw_subsumption_res:                 0
% 3.01/1.00  sim_tautology_del:                      1
% 3.01/1.00  sim_eq_tautology_del:                   3
% 3.01/1.00  sim_eq_res_simp:                        0
% 3.01/1.00  sim_fw_demodulated:                     1
% 3.01/1.00  sim_bw_demodulated:                     10
% 3.01/1.00  sim_light_normalised:                   6
% 3.01/1.00  sim_joinable_taut:                      0
% 3.01/1.00  sim_joinable_simp:                      0
% 3.01/1.00  sim_ac_normalised:                      0
% 3.01/1.00  sim_smt_subsumption:                    0
% 3.01/1.00  
%------------------------------------------------------------------------------
