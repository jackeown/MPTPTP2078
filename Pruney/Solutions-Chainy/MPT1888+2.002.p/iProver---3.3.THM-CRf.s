%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:30 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  191 (4430 expanded)
%              Number of clauses        :  123 (1311 expanded)
%              Number of leaves         :   18 (1260 expanded)
%              Depth                    :   28
%              Number of atoms          :  579 (24096 expanded)
%              Number of equality atoms :  198 (4173 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
          & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
        & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)))
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f44,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    & ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v3_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f43,f42,f41])).

fof(f64,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f56,f50])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f60,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))
      | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f50])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_547,plain,
    ( r1_xboole_0(X0_47,X1_47)
    | r2_hidden(sK1(X0_47,X1_47),X0_47) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_877,plain,
    ( r1_xboole_0(X0_47,X1_47) = iProver_top
    | r2_hidden(sK1(X0_47,X1_47),X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_538,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_885,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0_47,X1_47)
    | v1_xboole_0(X1_47)
    | k6_domain_1(X1_47,X0_47) = k2_tarski(X0_47,X0_47) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_882,plain,
    ( k6_domain_1(X0_47,X1_47) = k2_tarski(X1_47,X1_47)
    | m1_subset_1(X1_47,X0_47) != iProver_top
    | v1_xboole_0(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_2174,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_885,c_882])).

cnf(c_26,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_311,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(X0,k1_connsp_2(sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(X0,k1_connsp_2(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_311,c_21,c_18])).

cnf(c_536,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | r2_hidden(X0_47,k1_connsp_2(sK2,X0_47)) ),
    inference(subtyping,[status(esa)],[c_315])).

cnf(c_601,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_47,k1_connsp_2(sK2,X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_603,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,k1_connsp_2(sK2,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_550,plain,
    ( ~ r2_hidden(X0_47,X1_47)
    | ~ v1_xboole_0(X1_47) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_948,plain,
    ( ~ r2_hidden(X0_47,k1_connsp_2(sK2,X0_47))
    | ~ v1_xboole_0(k1_connsp_2(sK2,X0_47)) ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_949,plain,
    ( r2_hidden(X0_47,k1_connsp_2(sK2,X0_47)) != iProver_top
    | v1_xboole_0(k1_connsp_2(sK2,X0_47)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_948])).

cnf(c_951,plain,
    ( r2_hidden(sK3,k1_connsp_2(sK2,sK3)) != iProver_top
    | v1_xboole_0(k1_connsp_2(sK2,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_949])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_329,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_333,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_329,c_21,c_18])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | m1_subset_1(k1_connsp_2(sK2,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_333])).

cnf(c_888,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k1_connsp_2(sK2,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_545,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
    | ~ v1_xboole_0(X1_47)
    | v1_xboole_0(X0_47) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_879,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(X1_47)) != iProver_top
    | v1_xboole_0(X1_47) != iProver_top
    | v1_xboole_0(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_545])).

cnf(c_2061,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(k1_connsp_2(sK2,X0_47)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_888,c_879])).

cnf(c_2067,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(k1_connsp_2(sK2,sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2061])).

cnf(c_2414,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2174,c_26,c_603,c_951,c_2067])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_551,plain,
    ( r2_hidden(sK0(X0_47),X0_47)
    | v1_xboole_0(X0_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_873,plain,
    ( r2_hidden(sK0(X0_47),X0_47) = iProver_top
    | v1_xboole_0(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_551])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)))
    | ~ v3_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,negated_conjecture,
    ( v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_233,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X0,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) ),
    inference(unflattening,[status(thm)],[c_233])).

cnf(c_238,plain,
    ( ~ r2_hidden(X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_234,c_21,c_20,c_18])).

cnf(c_239,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) ),
    inference(renaming,[status(thm)],[c_238])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
    | ~ r2_hidden(X1_47,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1_47)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) ),
    inference(subtyping,[status(esa)],[c_239])).

cnf(c_886,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1_47))
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_47,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_1392,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47))))) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47))
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47))),u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47))) = iProver_top ),
    inference(superposition,[status(thm)],[c_873,c_886])).

cnf(c_2420,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3))))) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3))
    | m1_subset_1(sK0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2414,c_1392])).

cnf(c_2425,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))))) = k2_pre_topc(sK2,k2_tarski(sK3,sK3))
    | m1_subset_1(sK0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2420,c_2414])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_544,plain,
    ( ~ m1_subset_1(X0_47,X1_47)
    | r2_hidden(X0_47,X1_47)
    | v1_xboole_0(X1_47) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_880,plain,
    ( m1_subset_1(X0_47,X1_47) != iProver_top
    | r2_hidden(X0_47,X1_47) = iProver_top
    | v1_xboole_0(X1_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_2044,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_885,c_880])).

cnf(c_874,plain,
    ( r2_hidden(X0_47,X1_47) != iProver_top
    | v1_xboole_0(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_550])).

cnf(c_1552,plain,
    ( r1_xboole_0(X0_47,X1_47) = iProver_top
    | v1_xboole_0(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_874])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_539,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_884,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_2173,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_884,c_882])).

cnf(c_27,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1351,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_542])).

cnf(c_1352,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4)
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1351])).

cnf(c_2356,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2173,c_26,c_27,c_603,c_951,c_1352,c_2067])).

cnf(c_15,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_540,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_883,plain,
    ( r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_2359,plain,
    ( r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2356,c_883])).

cnf(c_2416,plain,
    ( r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2414,c_2359])).

cnf(c_2804,plain,
    ( v1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1552,c_2416])).

cnf(c_2422,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3))
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2414,c_886])).

cnf(c_2423,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) = k2_pre_topc(sK2,k2_tarski(sK3,sK3))
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2422,c_2414])).

cnf(c_3290,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) = k2_pre_topc(sK2,k2_tarski(sK3,sK3))
    | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2423,c_26])).

cnf(c_3291,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) = k2_pre_topc(sK2,k2_tarski(sK3,sK3))
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3290])).

cnf(c_3296,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))))) = k2_pre_topc(sK2,k2_tarski(sK3,sK3))
    | m1_subset_1(sK0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))),u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_873,c_3291])).

cnf(c_5,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_546,plain,
    ( m1_subset_1(k2_tarski(X0_47,X0_47),k1_zfmisc_1(X1_47))
    | ~ r2_hidden(X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_878,plain,
    ( m1_subset_1(k2_tarski(X0_47,X0_47),k1_zfmisc_1(X1_47)) = iProver_top
    | r2_hidden(X0_47,X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_pre_topc(sK2,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_353])).

cnf(c_889,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_543,plain,
    ( m1_subset_1(X0_47,X1_47)
    | ~ m1_subset_1(X2_47,k1_zfmisc_1(X1_47))
    | ~ r2_hidden(X0_47,X2_47) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_881,plain,
    ( m1_subset_1(X0_47,X1_47) = iProver_top
    | m1_subset_1(X2_47,k1_zfmisc_1(X1_47)) != iProver_top
    | r2_hidden(X0_47,X2_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_543])).

cnf(c_2190,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0_47,k2_pre_topc(sK2,X1_47)) != iProver_top ),
    inference(superposition,[status(thm)],[c_889,c_881])).

cnf(c_3024,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(X1_47,X1_47))) != iProver_top
    | r2_hidden(X1_47,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_878,c_2190])).

cnf(c_4420,plain,
    ( m1_subset_1(sK0(k2_pre_topc(sK2,k2_tarski(X0_47,X0_47))),u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0_47,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(k2_pre_topc(sK2,k2_tarski(X0_47,X0_47))) = iProver_top ),
    inference(superposition,[status(thm)],[c_873,c_3024])).

cnf(c_4428,plain,
    ( m1_subset_1(sK0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))),u1_struct_0(sK2)) = iProver_top
    | r2_hidden(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4420])).

cnf(c_4675,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))))) = k2_pre_topc(sK2,k2_tarski(sK3,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2425,c_26,c_603,c_951,c_2044,c_2067,c_2804,c_3296,c_4428])).

cnf(c_4678,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4675,c_889])).

cnf(c_933,plain,
    ( m1_subset_1(k2_pre_topc(sK2,k2_tarski(X0_47,X0_47)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(X0_47,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_934,plain,
    ( m1_subset_1(k2_pre_topc(sK2,k2_tarski(X0_47,X0_47)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k2_tarski(X0_47,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_933])).

cnf(c_936,plain,
    ( m1_subset_1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_934])).

cnf(c_1209,plain,
    ( m1_subset_1(k2_tarski(X0_47,X0_47),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0_47,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_1210,plain,
    ( m1_subset_1(k2_tarski(X0_47,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r2_hidden(X0_47,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1209])).

cnf(c_1212,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r2_hidden(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1210])).

cnf(c_4763,plain,
    ( m1_subset_1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4678,c_26,c_603,c_936,c_951,c_1212,c_2044,c_2067])).

cnf(c_4771,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4763,c_881])).

cnf(c_5087,plain,
    ( m1_subset_1(sK1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),X0_47),u1_struct_0(sK2)) = iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),X0_47) = iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_4771])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_548,plain,
    ( r1_xboole_0(X0_47,X1_47)
    | r2_hidden(sK1(X0_47,X1_47),X1_47) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_876,plain,
    ( r1_xboole_0(X0_47,X1_47) = iProver_top
    | r2_hidden(sK1(X0_47,X1_47),X1_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_548])).

cnf(c_2366,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2356,c_886])).

cnf(c_2367,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2366,c_2356])).

cnf(c_3129,plain,
    ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
    | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2367,c_27])).

cnf(c_3130,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3129])).

cnf(c_3136,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(X0_47,k2_pre_topc(sK2,k2_tarski(sK4,sK4))))) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
    | m1_subset_1(sK1(X0_47,k2_pre_topc(sK2,k2_tarski(sK4,sK4))),u1_struct_0(sK2)) != iProver_top
    | r1_xboole_0(X0_47,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_876,c_3130])).

cnf(c_12010,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))))) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
    | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5087,c_3136])).

cnf(c_1553,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)),X1_47))) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47))
    | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)),X1_47),u1_struct_0(sK2)) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)),X1_47) = iProver_top ),
    inference(superposition,[status(thm)],[c_877,c_886])).

cnf(c_2419,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),X0_47))) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3))
    | m1_subset_1(sK1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),X0_47),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),X0_47) = iProver_top ),
    inference(superposition,[status(thm)],[c_2414,c_1553])).

cnf(c_2426,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),X0_47))) = k2_pre_topc(sK2,k2_tarski(sK3,sK3))
    | m1_subset_1(sK1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),X0_47),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),X0_47) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2419,c_2414])).

cnf(c_5333,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),X0_47))) = k2_pre_topc(sK2,k2_tarski(sK3,sK3))
    | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),X0_47) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2426,c_26,c_5087])).

cnf(c_5340,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))))) = k2_pre_topc(sK2,k2_tarski(sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_5333,c_2416])).

cnf(c_12017,plain,
    ( k2_pre_topc(sK2,k2_tarski(sK4,sK4)) = k2_pre_topc(sK2,k2_tarski(sK3,sK3))
    | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12010,c_5340])).

cnf(c_14,negated_conjecture,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_541,negated_conjecture,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2360,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k2_tarski(sK4,sK4)) ),
    inference(demodulation,[status(thm)],[c_2356,c_541])).

cnf(c_2417,plain,
    ( k2_pre_topc(sK2,k2_tarski(sK4,sK4)) != k2_pre_topc(sK2,k2_tarski(sK3,sK3)) ),
    inference(demodulation,[status(thm)],[c_2414,c_2360])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12017,c_2417,c_2416])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:32:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.52/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.52/0.99  
% 3.52/0.99  ------  iProver source info
% 3.52/0.99  
% 3.52/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.52/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.52/0.99  git: non_committed_changes: false
% 3.52/0.99  git: last_make_outside_of_git: false
% 3.52/0.99  
% 3.52/0.99  ------ 
% 3.52/0.99  
% 3.52/0.99  ------ Input Options
% 3.52/0.99  
% 3.52/0.99  --out_options                           all
% 3.52/0.99  --tptp_safe_out                         true
% 3.52/0.99  --problem_path                          ""
% 3.52/0.99  --include_path                          ""
% 3.52/0.99  --clausifier                            res/vclausify_rel
% 3.52/0.99  --clausifier_options                    ""
% 3.52/0.99  --stdin                                 false
% 3.52/0.99  --stats_out                             all
% 3.52/0.99  
% 3.52/0.99  ------ General Options
% 3.52/0.99  
% 3.52/0.99  --fof                                   false
% 3.52/0.99  --time_out_real                         305.
% 3.52/0.99  --time_out_virtual                      -1.
% 3.52/0.99  --symbol_type_check                     false
% 3.52/0.99  --clausify_out                          false
% 3.52/0.99  --sig_cnt_out                           false
% 3.52/0.99  --trig_cnt_out                          false
% 3.52/0.99  --trig_cnt_out_tolerance                1.
% 3.52/0.99  --trig_cnt_out_sk_spl                   false
% 3.52/0.99  --abstr_cl_out                          false
% 3.52/0.99  
% 3.52/0.99  ------ Global Options
% 3.52/0.99  
% 3.52/0.99  --schedule                              default
% 3.52/0.99  --add_important_lit                     false
% 3.52/0.99  --prop_solver_per_cl                    1000
% 3.52/0.99  --min_unsat_core                        false
% 3.52/0.99  --soft_assumptions                      false
% 3.52/0.99  --soft_lemma_size                       3
% 3.52/0.99  --prop_impl_unit_size                   0
% 3.52/0.99  --prop_impl_unit                        []
% 3.52/0.99  --share_sel_clauses                     true
% 3.52/0.99  --reset_solvers                         false
% 3.52/0.99  --bc_imp_inh                            [conj_cone]
% 3.52/0.99  --conj_cone_tolerance                   3.
% 3.52/0.99  --extra_neg_conj                        none
% 3.52/0.99  --large_theory_mode                     true
% 3.52/0.99  --prolific_symb_bound                   200
% 3.52/0.99  --lt_threshold                          2000
% 3.52/0.99  --clause_weak_htbl                      true
% 3.52/0.99  --gc_record_bc_elim                     false
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing Options
% 3.52/0.99  
% 3.52/0.99  --preprocessing_flag                    true
% 3.52/0.99  --time_out_prep_mult                    0.1
% 3.52/0.99  --splitting_mode                        input
% 3.52/0.99  --splitting_grd                         true
% 3.52/0.99  --splitting_cvd                         false
% 3.52/0.99  --splitting_cvd_svl                     false
% 3.52/0.99  --splitting_nvd                         32
% 3.52/0.99  --sub_typing                            true
% 3.52/0.99  --prep_gs_sim                           true
% 3.52/0.99  --prep_unflatten                        true
% 3.52/0.99  --prep_res_sim                          true
% 3.52/0.99  --prep_upred                            true
% 3.52/0.99  --prep_sem_filter                       exhaustive
% 3.52/0.99  --prep_sem_filter_out                   false
% 3.52/0.99  --pred_elim                             true
% 3.52/0.99  --res_sim_input                         true
% 3.52/0.99  --eq_ax_congr_red                       true
% 3.52/0.99  --pure_diseq_elim                       true
% 3.52/0.99  --brand_transform                       false
% 3.52/0.99  --non_eq_to_eq                          false
% 3.52/0.99  --prep_def_merge                        true
% 3.52/0.99  --prep_def_merge_prop_impl              false
% 3.52/0.99  --prep_def_merge_mbd                    true
% 3.52/0.99  --prep_def_merge_tr_red                 false
% 3.52/0.99  --prep_def_merge_tr_cl                  false
% 3.52/0.99  --smt_preprocessing                     true
% 3.52/0.99  --smt_ac_axioms                         fast
% 3.52/0.99  --preprocessed_out                      false
% 3.52/0.99  --preprocessed_stats                    false
% 3.52/0.99  
% 3.52/0.99  ------ Abstraction refinement Options
% 3.52/0.99  
% 3.52/0.99  --abstr_ref                             []
% 3.52/0.99  --abstr_ref_prep                        false
% 3.52/0.99  --abstr_ref_until_sat                   false
% 3.52/0.99  --abstr_ref_sig_restrict                funpre
% 3.52/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/0.99  --abstr_ref_under                       []
% 3.52/0.99  
% 3.52/0.99  ------ SAT Options
% 3.52/0.99  
% 3.52/0.99  --sat_mode                              false
% 3.52/0.99  --sat_fm_restart_options                ""
% 3.52/0.99  --sat_gr_def                            false
% 3.52/0.99  --sat_epr_types                         true
% 3.52/0.99  --sat_non_cyclic_types                  false
% 3.52/0.99  --sat_finite_models                     false
% 3.52/0.99  --sat_fm_lemmas                         false
% 3.52/0.99  --sat_fm_prep                           false
% 3.52/0.99  --sat_fm_uc_incr                        true
% 3.52/0.99  --sat_out_model                         small
% 3.52/0.99  --sat_out_clauses                       false
% 3.52/0.99  
% 3.52/0.99  ------ QBF Options
% 3.52/0.99  
% 3.52/0.99  --qbf_mode                              false
% 3.52/0.99  --qbf_elim_univ                         false
% 3.52/0.99  --qbf_dom_inst                          none
% 3.52/0.99  --qbf_dom_pre_inst                      false
% 3.52/0.99  --qbf_sk_in                             false
% 3.52/0.99  --qbf_pred_elim                         true
% 3.52/0.99  --qbf_split                             512
% 3.52/0.99  
% 3.52/0.99  ------ BMC1 Options
% 3.52/0.99  
% 3.52/0.99  --bmc1_incremental                      false
% 3.52/0.99  --bmc1_axioms                           reachable_all
% 3.52/0.99  --bmc1_min_bound                        0
% 3.52/0.99  --bmc1_max_bound                        -1
% 3.52/0.99  --bmc1_max_bound_default                -1
% 3.52/0.99  --bmc1_symbol_reachability              true
% 3.52/0.99  --bmc1_property_lemmas                  false
% 3.52/0.99  --bmc1_k_induction                      false
% 3.52/0.99  --bmc1_non_equiv_states                 false
% 3.52/0.99  --bmc1_deadlock                         false
% 3.52/0.99  --bmc1_ucm                              false
% 3.52/0.99  --bmc1_add_unsat_core                   none
% 3.52/0.99  --bmc1_unsat_core_children              false
% 3.52/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/0.99  --bmc1_out_stat                         full
% 3.52/0.99  --bmc1_ground_init                      false
% 3.52/0.99  --bmc1_pre_inst_next_state              false
% 3.52/0.99  --bmc1_pre_inst_state                   false
% 3.52/0.99  --bmc1_pre_inst_reach_state             false
% 3.52/0.99  --bmc1_out_unsat_core                   false
% 3.52/0.99  --bmc1_aig_witness_out                  false
% 3.52/0.99  --bmc1_verbose                          false
% 3.52/0.99  --bmc1_dump_clauses_tptp                false
% 3.52/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.52/0.99  --bmc1_dump_file                        -
% 3.52/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.52/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.52/0.99  --bmc1_ucm_extend_mode                  1
% 3.52/0.99  --bmc1_ucm_init_mode                    2
% 3.52/0.99  --bmc1_ucm_cone_mode                    none
% 3.52/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.52/0.99  --bmc1_ucm_relax_model                  4
% 3.52/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.52/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/0.99  --bmc1_ucm_layered_model                none
% 3.52/0.99  --bmc1_ucm_max_lemma_size               10
% 3.52/0.99  
% 3.52/0.99  ------ AIG Options
% 3.52/0.99  
% 3.52/0.99  --aig_mode                              false
% 3.52/0.99  
% 3.52/0.99  ------ Instantiation Options
% 3.52/0.99  
% 3.52/0.99  --instantiation_flag                    true
% 3.52/0.99  --inst_sos_flag                         true
% 3.52/0.99  --inst_sos_phase                        true
% 3.52/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/0.99  --inst_lit_sel_side                     num_symb
% 3.52/0.99  --inst_solver_per_active                1400
% 3.52/0.99  --inst_solver_calls_frac                1.
% 3.52/0.99  --inst_passive_queue_type               priority_queues
% 3.52/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/0.99  --inst_passive_queues_freq              [25;2]
% 3.52/0.99  --inst_dismatching                      true
% 3.52/0.99  --inst_eager_unprocessed_to_passive     true
% 3.52/0.99  --inst_prop_sim_given                   true
% 3.52/0.99  --inst_prop_sim_new                     false
% 3.52/0.99  --inst_subs_new                         false
% 3.52/0.99  --inst_eq_res_simp                      false
% 3.52/0.99  --inst_subs_given                       false
% 3.52/0.99  --inst_orphan_elimination               true
% 3.52/0.99  --inst_learning_loop_flag               true
% 3.52/0.99  --inst_learning_start                   3000
% 3.52/0.99  --inst_learning_factor                  2
% 3.52/0.99  --inst_start_prop_sim_after_learn       3
% 3.52/0.99  --inst_sel_renew                        solver
% 3.52/0.99  --inst_lit_activity_flag                true
% 3.52/0.99  --inst_restr_to_given                   false
% 3.52/0.99  --inst_activity_threshold               500
% 3.52/0.99  --inst_out_proof                        true
% 3.52/0.99  
% 3.52/0.99  ------ Resolution Options
% 3.52/0.99  
% 3.52/0.99  --resolution_flag                       true
% 3.52/0.99  --res_lit_sel                           adaptive
% 3.52/0.99  --res_lit_sel_side                      none
% 3.52/0.99  --res_ordering                          kbo
% 3.52/0.99  --res_to_prop_solver                    active
% 3.52/0.99  --res_prop_simpl_new                    false
% 3.52/0.99  --res_prop_simpl_given                  true
% 3.52/0.99  --res_passive_queue_type                priority_queues
% 3.52/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/0.99  --res_passive_queues_freq               [15;5]
% 3.52/0.99  --res_forward_subs                      full
% 3.52/0.99  --res_backward_subs                     full
% 3.52/0.99  --res_forward_subs_resolution           true
% 3.52/0.99  --res_backward_subs_resolution          true
% 3.52/0.99  --res_orphan_elimination                true
% 3.52/0.99  --res_time_limit                        2.
% 3.52/0.99  --res_out_proof                         true
% 3.52/0.99  
% 3.52/0.99  ------ Superposition Options
% 3.52/0.99  
% 3.52/0.99  --superposition_flag                    true
% 3.52/0.99  --sup_passive_queue_type                priority_queues
% 3.52/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.52/0.99  --demod_completeness_check              fast
% 3.52/0.99  --demod_use_ground                      true
% 3.52/0.99  --sup_to_prop_solver                    passive
% 3.52/0.99  --sup_prop_simpl_new                    true
% 3.52/0.99  --sup_prop_simpl_given                  true
% 3.52/0.99  --sup_fun_splitting                     true
% 3.52/0.99  --sup_smt_interval                      50000
% 3.52/0.99  
% 3.52/0.99  ------ Superposition Simplification Setup
% 3.52/0.99  
% 3.52/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.52/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.52/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.52/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.52/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.52/0.99  --sup_immed_triv                        [TrivRules]
% 3.52/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.99  --sup_immed_bw_main                     []
% 3.52/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.52/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.99  --sup_input_bw                          []
% 3.52/0.99  
% 3.52/0.99  ------ Combination Options
% 3.52/0.99  
% 3.52/0.99  --comb_res_mult                         3
% 3.52/0.99  --comb_sup_mult                         2
% 3.52/0.99  --comb_inst_mult                        10
% 3.52/0.99  
% 3.52/0.99  ------ Debug Options
% 3.52/0.99  
% 3.52/0.99  --dbg_backtrace                         false
% 3.52/0.99  --dbg_dump_prop_clauses                 false
% 3.52/0.99  --dbg_dump_prop_clauses_file            -
% 3.52/0.99  --dbg_out_stat                          false
% 3.52/0.99  ------ Parsing...
% 3.52/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.52/0.99  ------ Proving...
% 3.52/0.99  ------ Problem Properties 
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  clauses                                 18
% 3.52/0.99  conjectures                             4
% 3.52/0.99  EPR                                     3
% 3.52/0.99  Horn                                    13
% 3.52/0.99  unary                                   4
% 3.52/0.99  binary                                  8
% 3.52/0.99  lits                                    39
% 3.52/0.99  lits eq                                 3
% 3.52/0.99  fd_pure                                 0
% 3.52/0.99  fd_pseudo                               0
% 3.52/0.99  fd_cond                                 0
% 3.52/0.99  fd_pseudo_cond                          0
% 3.52/0.99  AC symbols                              0
% 3.52/0.99  
% 3.52/0.99  ------ Schedule dynamic 5 is on 
% 3.52/0.99  
% 3.52/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ 
% 3.52/0.99  Current options:
% 3.52/0.99  ------ 
% 3.52/0.99  
% 3.52/0.99  ------ Input Options
% 3.52/0.99  
% 3.52/0.99  --out_options                           all
% 3.52/0.99  --tptp_safe_out                         true
% 3.52/0.99  --problem_path                          ""
% 3.52/0.99  --include_path                          ""
% 3.52/0.99  --clausifier                            res/vclausify_rel
% 3.52/0.99  --clausifier_options                    ""
% 3.52/0.99  --stdin                                 false
% 3.52/0.99  --stats_out                             all
% 3.52/0.99  
% 3.52/0.99  ------ General Options
% 3.52/0.99  
% 3.52/0.99  --fof                                   false
% 3.52/0.99  --time_out_real                         305.
% 3.52/0.99  --time_out_virtual                      -1.
% 3.52/0.99  --symbol_type_check                     false
% 3.52/0.99  --clausify_out                          false
% 3.52/0.99  --sig_cnt_out                           false
% 3.52/0.99  --trig_cnt_out                          false
% 3.52/0.99  --trig_cnt_out_tolerance                1.
% 3.52/0.99  --trig_cnt_out_sk_spl                   false
% 3.52/0.99  --abstr_cl_out                          false
% 3.52/0.99  
% 3.52/0.99  ------ Global Options
% 3.52/0.99  
% 3.52/0.99  --schedule                              default
% 3.52/0.99  --add_important_lit                     false
% 3.52/0.99  --prop_solver_per_cl                    1000
% 3.52/0.99  --min_unsat_core                        false
% 3.52/0.99  --soft_assumptions                      false
% 3.52/0.99  --soft_lemma_size                       3
% 3.52/0.99  --prop_impl_unit_size                   0
% 3.52/0.99  --prop_impl_unit                        []
% 3.52/0.99  --share_sel_clauses                     true
% 3.52/0.99  --reset_solvers                         false
% 3.52/0.99  --bc_imp_inh                            [conj_cone]
% 3.52/0.99  --conj_cone_tolerance                   3.
% 3.52/0.99  --extra_neg_conj                        none
% 3.52/0.99  --large_theory_mode                     true
% 3.52/0.99  --prolific_symb_bound                   200
% 3.52/0.99  --lt_threshold                          2000
% 3.52/0.99  --clause_weak_htbl                      true
% 3.52/0.99  --gc_record_bc_elim                     false
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing Options
% 3.52/0.99  
% 3.52/0.99  --preprocessing_flag                    true
% 3.52/0.99  --time_out_prep_mult                    0.1
% 3.52/0.99  --splitting_mode                        input
% 3.52/0.99  --splitting_grd                         true
% 3.52/0.99  --splitting_cvd                         false
% 3.52/0.99  --splitting_cvd_svl                     false
% 3.52/0.99  --splitting_nvd                         32
% 3.52/0.99  --sub_typing                            true
% 3.52/0.99  --prep_gs_sim                           true
% 3.52/0.99  --prep_unflatten                        true
% 3.52/0.99  --prep_res_sim                          true
% 3.52/0.99  --prep_upred                            true
% 3.52/0.99  --prep_sem_filter                       exhaustive
% 3.52/0.99  --prep_sem_filter_out                   false
% 3.52/0.99  --pred_elim                             true
% 3.52/0.99  --res_sim_input                         true
% 3.52/0.99  --eq_ax_congr_red                       true
% 3.52/0.99  --pure_diseq_elim                       true
% 3.52/0.99  --brand_transform                       false
% 3.52/0.99  --non_eq_to_eq                          false
% 3.52/0.99  --prep_def_merge                        true
% 3.52/0.99  --prep_def_merge_prop_impl              false
% 3.52/0.99  --prep_def_merge_mbd                    true
% 3.52/0.99  --prep_def_merge_tr_red                 false
% 3.52/0.99  --prep_def_merge_tr_cl                  false
% 3.52/0.99  --smt_preprocessing                     true
% 3.52/0.99  --smt_ac_axioms                         fast
% 3.52/0.99  --preprocessed_out                      false
% 3.52/0.99  --preprocessed_stats                    false
% 3.52/0.99  
% 3.52/0.99  ------ Abstraction refinement Options
% 3.52/0.99  
% 3.52/0.99  --abstr_ref                             []
% 3.52/0.99  --abstr_ref_prep                        false
% 3.52/0.99  --abstr_ref_until_sat                   false
% 3.52/0.99  --abstr_ref_sig_restrict                funpre
% 3.52/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/0.99  --abstr_ref_under                       []
% 3.52/0.99  
% 3.52/0.99  ------ SAT Options
% 3.52/0.99  
% 3.52/0.99  --sat_mode                              false
% 3.52/0.99  --sat_fm_restart_options                ""
% 3.52/0.99  --sat_gr_def                            false
% 3.52/0.99  --sat_epr_types                         true
% 3.52/0.99  --sat_non_cyclic_types                  false
% 3.52/0.99  --sat_finite_models                     false
% 3.52/0.99  --sat_fm_lemmas                         false
% 3.52/0.99  --sat_fm_prep                           false
% 3.52/0.99  --sat_fm_uc_incr                        true
% 3.52/0.99  --sat_out_model                         small
% 3.52/0.99  --sat_out_clauses                       false
% 3.52/0.99  
% 3.52/0.99  ------ QBF Options
% 3.52/0.99  
% 3.52/0.99  --qbf_mode                              false
% 3.52/0.99  --qbf_elim_univ                         false
% 3.52/0.99  --qbf_dom_inst                          none
% 3.52/0.99  --qbf_dom_pre_inst                      false
% 3.52/0.99  --qbf_sk_in                             false
% 3.52/0.99  --qbf_pred_elim                         true
% 3.52/0.99  --qbf_split                             512
% 3.52/0.99  
% 3.52/0.99  ------ BMC1 Options
% 3.52/0.99  
% 3.52/0.99  --bmc1_incremental                      false
% 3.52/0.99  --bmc1_axioms                           reachable_all
% 3.52/0.99  --bmc1_min_bound                        0
% 3.52/0.99  --bmc1_max_bound                        -1
% 3.52/0.99  --bmc1_max_bound_default                -1
% 3.52/0.99  --bmc1_symbol_reachability              true
% 3.52/0.99  --bmc1_property_lemmas                  false
% 3.52/0.99  --bmc1_k_induction                      false
% 3.52/0.99  --bmc1_non_equiv_states                 false
% 3.52/0.99  --bmc1_deadlock                         false
% 3.52/0.99  --bmc1_ucm                              false
% 3.52/0.99  --bmc1_add_unsat_core                   none
% 3.52/0.99  --bmc1_unsat_core_children              false
% 3.52/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/0.99  --bmc1_out_stat                         full
% 3.52/0.99  --bmc1_ground_init                      false
% 3.52/0.99  --bmc1_pre_inst_next_state              false
% 3.52/0.99  --bmc1_pre_inst_state                   false
% 3.52/0.99  --bmc1_pre_inst_reach_state             false
% 3.52/0.99  --bmc1_out_unsat_core                   false
% 3.52/0.99  --bmc1_aig_witness_out                  false
% 3.52/0.99  --bmc1_verbose                          false
% 3.52/0.99  --bmc1_dump_clauses_tptp                false
% 3.52/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.52/0.99  --bmc1_dump_file                        -
% 3.52/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.52/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.52/0.99  --bmc1_ucm_extend_mode                  1
% 3.52/0.99  --bmc1_ucm_init_mode                    2
% 3.52/0.99  --bmc1_ucm_cone_mode                    none
% 3.52/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.52/0.99  --bmc1_ucm_relax_model                  4
% 3.52/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.52/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/0.99  --bmc1_ucm_layered_model                none
% 3.52/0.99  --bmc1_ucm_max_lemma_size               10
% 3.52/0.99  
% 3.52/0.99  ------ AIG Options
% 3.52/0.99  
% 3.52/0.99  --aig_mode                              false
% 3.52/0.99  
% 3.52/0.99  ------ Instantiation Options
% 3.52/0.99  
% 3.52/0.99  --instantiation_flag                    true
% 3.52/0.99  --inst_sos_flag                         true
% 3.52/0.99  --inst_sos_phase                        true
% 3.52/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/0.99  --inst_lit_sel_side                     none
% 3.52/0.99  --inst_solver_per_active                1400
% 3.52/0.99  --inst_solver_calls_frac                1.
% 3.52/0.99  --inst_passive_queue_type               priority_queues
% 3.52/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/0.99  --inst_passive_queues_freq              [25;2]
% 3.52/0.99  --inst_dismatching                      true
% 3.52/0.99  --inst_eager_unprocessed_to_passive     true
% 3.52/0.99  --inst_prop_sim_given                   true
% 3.52/0.99  --inst_prop_sim_new                     false
% 3.52/0.99  --inst_subs_new                         false
% 3.52/0.99  --inst_eq_res_simp                      false
% 3.52/0.99  --inst_subs_given                       false
% 3.52/0.99  --inst_orphan_elimination               true
% 3.52/0.99  --inst_learning_loop_flag               true
% 3.52/0.99  --inst_learning_start                   3000
% 3.52/0.99  --inst_learning_factor                  2
% 3.52/0.99  --inst_start_prop_sim_after_learn       3
% 3.52/0.99  --inst_sel_renew                        solver
% 3.52/0.99  --inst_lit_activity_flag                true
% 3.52/0.99  --inst_restr_to_given                   false
% 3.52/0.99  --inst_activity_threshold               500
% 3.52/0.99  --inst_out_proof                        true
% 3.52/0.99  
% 3.52/0.99  ------ Resolution Options
% 3.52/0.99  
% 3.52/0.99  --resolution_flag                       false
% 3.52/0.99  --res_lit_sel                           adaptive
% 3.52/0.99  --res_lit_sel_side                      none
% 3.52/0.99  --res_ordering                          kbo
% 3.52/0.99  --res_to_prop_solver                    active
% 3.52/0.99  --res_prop_simpl_new                    false
% 3.52/0.99  --res_prop_simpl_given                  true
% 3.52/0.99  --res_passive_queue_type                priority_queues
% 3.52/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/0.99  --res_passive_queues_freq               [15;5]
% 3.52/0.99  --res_forward_subs                      full
% 3.52/0.99  --res_backward_subs                     full
% 3.52/0.99  --res_forward_subs_resolution           true
% 3.52/0.99  --res_backward_subs_resolution          true
% 3.52/0.99  --res_orphan_elimination                true
% 3.52/0.99  --res_time_limit                        2.
% 3.52/0.99  --res_out_proof                         true
% 3.52/0.99  
% 3.52/0.99  ------ Superposition Options
% 3.52/0.99  
% 3.52/0.99  --superposition_flag                    true
% 3.52/0.99  --sup_passive_queue_type                priority_queues
% 3.52/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.52/0.99  --demod_completeness_check              fast
% 3.52/0.99  --demod_use_ground                      true
% 3.52/0.99  --sup_to_prop_solver                    passive
% 3.52/0.99  --sup_prop_simpl_new                    true
% 3.52/0.99  --sup_prop_simpl_given                  true
% 3.52/0.99  --sup_fun_splitting                     true
% 3.52/0.99  --sup_smt_interval                      50000
% 3.52/0.99  
% 3.52/0.99  ------ Superposition Simplification Setup
% 3.52/0.99  
% 3.52/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.52/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.52/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.52/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.52/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.52/0.99  --sup_immed_triv                        [TrivRules]
% 3.52/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.99  --sup_immed_bw_main                     []
% 3.52/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.52/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.99  --sup_input_bw                          []
% 3.52/0.99  
% 3.52/0.99  ------ Combination Options
% 3.52/0.99  
% 3.52/0.99  --comb_res_mult                         3
% 3.52/0.99  --comb_sup_mult                         2
% 3.52/0.99  --comb_inst_mult                        10
% 3.52/0.99  
% 3.52/0.99  ------ Debug Options
% 3.52/0.99  
% 3.52/0.99  --dbg_backtrace                         false
% 3.52/0.99  --dbg_dump_prop_clauses                 false
% 3.52/0.99  --dbg_dump_prop_clauses_file            -
% 3.52/0.99  --dbg_out_stat                          false
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ Proving...
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  % SZS status Theorem for theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  fof(f2,axiom,(
% 3.52/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f15,plain,(
% 3.52/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.52/0.99    inference(rectify,[],[f2])).
% 3.52/0.99  
% 3.52/0.99  fof(f16,plain,(
% 3.52/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.52/0.99    inference(ennf_transformation,[],[f15])).
% 3.52/0.99  
% 3.52/0.99  fof(f39,plain,(
% 3.52/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.52/0.99    introduced(choice_axiom,[])).
% 3.52/0.99  
% 3.52/0.99  fof(f40,plain,(
% 3.52/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f39])).
% 3.52/0.99  
% 3.52/0.99  fof(f47,plain,(
% 3.52/0.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f40])).
% 3.52/0.99  
% 3.52/0.99  fof(f13,conjecture,(
% 3.52/0.99    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 3.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f14,negated_conjecture,(
% 3.52/0.99    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 3.52/0.99    inference(negated_conjecture,[],[f13])).
% 3.52/0.99  
% 3.52/0.99  fof(f33,plain,(
% 3.52/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.52/0.99    inference(ennf_transformation,[],[f14])).
% 3.52/0.99  
% 3.52/0.99  fof(f34,plain,(
% 3.52/0.99    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.52/0.99    inference(flattening,[],[f33])).
% 3.52/0.99  
% 3.52/0.99  fof(f43,plain,(
% 3.52/0.99    ( ! [X0,X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 3.52/0.99    introduced(choice_axiom,[])).
% 3.52/0.99  
% 3.52/0.99  fof(f42,plain,(
% 3.52/0.99    ( ! [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK3)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 3.52/0.99    introduced(choice_axiom,[])).
% 3.52/0.99  
% 3.52/0.99  fof(f41,plain,(
% 3.52/0.99    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)) & ~r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.52/0.99    introduced(choice_axiom,[])).
% 3.52/0.99  
% 3.52/0.99  fof(f44,plain,(
% 3.52/0.99    ((k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) & ~r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f43,f42,f41])).
% 3.52/0.99  
% 3.52/0.99  fof(f64,plain,(
% 3.52/0.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 3.52/0.99    inference(cnf_transformation,[],[f44])).
% 3.52/0.99  
% 3.52/0.99  fof(f9,axiom,(
% 3.52/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f25,plain,(
% 3.52/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.52/0.99    inference(ennf_transformation,[],[f9])).
% 3.52/0.99  
% 3.52/0.99  fof(f26,plain,(
% 3.52/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.52/0.99    inference(flattening,[],[f25])).
% 3.52/0.99  
% 3.52/0.99  fof(f56,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f26])).
% 3.52/0.99  
% 3.52/0.99  fof(f3,axiom,(
% 3.52/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f50,plain,(
% 3.52/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f3])).
% 3.52/0.99  
% 3.52/0.99  fof(f69,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.52/0.99    inference(definition_unfolding,[],[f56,f50])).
% 3.52/0.99  
% 3.52/0.99  fof(f11,axiom,(
% 3.52/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 3.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f29,plain,(
% 3.52/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.52/0.99    inference(ennf_transformation,[],[f11])).
% 3.52/0.99  
% 3.52/0.99  fof(f30,plain,(
% 3.52/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.52/0.99    inference(flattening,[],[f29])).
% 3.52/0.99  
% 3.52/0.99  fof(f58,plain,(
% 3.52/0.99    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f30])).
% 3.52/0.99  
% 3.52/0.99  fof(f61,plain,(
% 3.52/0.99    v2_pre_topc(sK2)),
% 3.52/0.99    inference(cnf_transformation,[],[f44])).
% 3.52/0.99  
% 3.52/0.99  fof(f60,plain,(
% 3.52/0.99    ~v2_struct_0(sK2)),
% 3.52/0.99    inference(cnf_transformation,[],[f44])).
% 3.52/0.99  
% 3.52/0.99  fof(f63,plain,(
% 3.52/0.99    l1_pre_topc(sK2)),
% 3.52/0.99    inference(cnf_transformation,[],[f44])).
% 3.52/0.99  
% 3.52/0.99  fof(f1,axiom,(
% 3.52/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f35,plain,(
% 3.52/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.52/0.99    inference(nnf_transformation,[],[f1])).
% 3.52/0.99  
% 3.52/0.99  fof(f36,plain,(
% 3.52/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.52/0.99    inference(rectify,[],[f35])).
% 3.52/0.99  
% 3.52/0.99  fof(f37,plain,(
% 3.52/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.52/0.99    introduced(choice_axiom,[])).
% 3.52/0.99  
% 3.52/0.99  fof(f38,plain,(
% 3.52/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 3.52/0.99  
% 3.52/0.99  fof(f45,plain,(
% 3.52/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f38])).
% 3.52/0.99  
% 3.52/0.99  fof(f10,axiom,(
% 3.52/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f27,plain,(
% 3.52/0.99    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.52/0.99    inference(ennf_transformation,[],[f10])).
% 3.52/0.99  
% 3.52/0.99  fof(f28,plain,(
% 3.52/0.99    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.52/0.99    inference(flattening,[],[f27])).
% 3.52/0.99  
% 3.52/0.99  fof(f57,plain,(
% 3.52/0.99    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f28])).
% 3.52/0.99  
% 3.52/0.99  fof(f5,axiom,(
% 3.52/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f18,plain,(
% 3.52/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.52/0.99    inference(ennf_transformation,[],[f5])).
% 3.52/0.99  
% 3.52/0.99  fof(f52,plain,(
% 3.52/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f18])).
% 3.52/0.99  
% 3.52/0.99  fof(f46,plain,(
% 3.52/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f38])).
% 3.52/0.99  
% 3.52/0.99  fof(f12,axiom,(
% 3.52/0.99    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))),
% 3.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f31,plain,(
% 3.52/0.99    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.52/0.99    inference(ennf_transformation,[],[f12])).
% 3.52/0.99  
% 3.52/0.99  fof(f32,plain,(
% 3.52/0.99    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.52/0.99    inference(flattening,[],[f31])).
% 3.52/0.99  
% 3.52/0.99  fof(f59,plain,(
% 3.52/0.99    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f32])).
% 3.52/0.99  
% 3.52/0.99  fof(f62,plain,(
% 3.52/0.99    v3_tdlat_3(sK2)),
% 3.52/0.99    inference(cnf_transformation,[],[f44])).
% 3.52/0.99  
% 3.52/0.99  fof(f6,axiom,(
% 3.52/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f19,plain,(
% 3.52/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.52/0.99    inference(ennf_transformation,[],[f6])).
% 3.52/0.99  
% 3.52/0.99  fof(f20,plain,(
% 3.52/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.52/0.99    inference(flattening,[],[f19])).
% 3.52/0.99  
% 3.52/0.99  fof(f53,plain,(
% 3.52/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f20])).
% 3.52/0.99  
% 3.52/0.99  fof(f65,plain,(
% 3.52/0.99    m1_subset_1(sK4,u1_struct_0(sK2))),
% 3.52/0.99    inference(cnf_transformation,[],[f44])).
% 3.52/0.99  
% 3.52/0.99  fof(f66,plain,(
% 3.52/0.99    ~r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))),
% 3.52/0.99    inference(cnf_transformation,[],[f44])).
% 3.52/0.99  
% 3.52/0.99  fof(f4,axiom,(
% 3.52/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 3.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f17,plain,(
% 3.52/0.99    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 3.52/0.99    inference(ennf_transformation,[],[f4])).
% 3.52/0.99  
% 3.52/0.99  fof(f51,plain,(
% 3.52/0.99    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f17])).
% 3.52/0.99  
% 3.52/0.99  fof(f68,plain,(
% 3.52/0.99    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.52/0.99    inference(definition_unfolding,[],[f51,f50])).
% 3.52/0.99  
% 3.52/0.99  fof(f8,axiom,(
% 3.52/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f23,plain,(
% 3.52/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.52/0.99    inference(ennf_transformation,[],[f8])).
% 3.52/0.99  
% 3.52/0.99  fof(f24,plain,(
% 3.52/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.52/0.99    inference(flattening,[],[f23])).
% 3.52/0.99  
% 3.52/0.99  fof(f55,plain,(
% 3.52/0.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f24])).
% 3.52/0.99  
% 3.52/0.99  fof(f7,axiom,(
% 3.52/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f21,plain,(
% 3.52/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.52/0.99    inference(ennf_transformation,[],[f7])).
% 3.52/0.99  
% 3.52/0.99  fof(f22,plain,(
% 3.52/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.52/0.99    inference(flattening,[],[f21])).
% 3.52/0.99  
% 3.52/0.99  fof(f54,plain,(
% 3.52/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f22])).
% 3.52/0.99  
% 3.52/0.99  fof(f48,plain,(
% 3.52/0.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f40])).
% 3.52/0.99  
% 3.52/0.99  fof(f67,plain,(
% 3.52/0.99    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))),
% 3.52/0.99    inference(cnf_transformation,[],[f44])).
% 3.52/0.99  
% 3.52/0.99  cnf(c_4,plain,
% 3.52/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.52/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_547,plain,
% 3.52/0.99      ( r1_xboole_0(X0_47,X1_47) | r2_hidden(sK1(X0_47,X1_47),X0_47) ),
% 3.52/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_877,plain,
% 3.52/0.99      ( r1_xboole_0(X0_47,X1_47) = iProver_top
% 3.52/0.99      | r2_hidden(sK1(X0_47,X1_47),X0_47) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_17,negated_conjecture,
% 3.52/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.52/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_538,negated_conjecture,
% 3.52/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.52/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_885,plain,
% 3.52/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_538]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_10,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,X1)
% 3.52/0.99      | v1_xboole_0(X1)
% 3.52/0.99      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 3.52/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_542,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0_47,X1_47)
% 3.52/0.99      | v1_xboole_0(X1_47)
% 3.52/0.99      | k6_domain_1(X1_47,X0_47) = k2_tarski(X0_47,X0_47) ),
% 3.52/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_882,plain,
% 3.52/0.99      ( k6_domain_1(X0_47,X1_47) = k2_tarski(X1_47,X1_47)
% 3.52/0.99      | m1_subset_1(X1_47,X0_47) != iProver_top
% 3.52/0.99      | v1_xboole_0(X0_47) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_542]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2174,plain,
% 3.52/0.99      ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)
% 3.52/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_885,c_882]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_26,plain,
% 3.52/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_12,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.52/0.99      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 3.52/0.99      | v2_struct_0(X1)
% 3.52/0.99      | ~ v2_pre_topc(X1)
% 3.52/0.99      | ~ l1_pre_topc(X1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_20,negated_conjecture,
% 3.52/0.99      ( v2_pre_topc(sK2) ),
% 3.52/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_310,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.52/0.99      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 3.52/0.99      | v2_struct_0(X1)
% 3.52/0.99      | ~ l1_pre_topc(X1)
% 3.52/0.99      | sK2 != X1 ),
% 3.52/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_311,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.52/0.99      | r2_hidden(X0,k1_connsp_2(sK2,X0))
% 3.52/0.99      | v2_struct_0(sK2)
% 3.52/0.99      | ~ l1_pre_topc(sK2) ),
% 3.52/0.99      inference(unflattening,[status(thm)],[c_310]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_21,negated_conjecture,
% 3.52/0.99      ( ~ v2_struct_0(sK2) ),
% 3.52/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_18,negated_conjecture,
% 3.52/0.99      ( l1_pre_topc(sK2) ),
% 3.52/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_315,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.52/0.99      | r2_hidden(X0,k1_connsp_2(sK2,X0)) ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_311,c_21,c_18]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_536,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 3.52/0.99      | r2_hidden(X0_47,k1_connsp_2(sK2,X0_47)) ),
% 3.52/0.99      inference(subtyping,[status(esa)],[c_315]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_601,plain,
% 3.52/0.99      ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | r2_hidden(X0_47,k1_connsp_2(sK2,X0_47)) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_603,plain,
% 3.52/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | r2_hidden(sK3,k1_connsp_2(sK2,sK3)) = iProver_top ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_601]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1,plain,
% 3.52/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_550,plain,
% 3.52/0.99      ( ~ r2_hidden(X0_47,X1_47) | ~ v1_xboole_0(X1_47) ),
% 3.52/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_948,plain,
% 3.52/0.99      ( ~ r2_hidden(X0_47,k1_connsp_2(sK2,X0_47))
% 3.52/0.99      | ~ v1_xboole_0(k1_connsp_2(sK2,X0_47)) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_550]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_949,plain,
% 3.52/0.99      ( r2_hidden(X0_47,k1_connsp_2(sK2,X0_47)) != iProver_top
% 3.52/0.99      | v1_xboole_0(k1_connsp_2(sK2,X0_47)) != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_948]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_951,plain,
% 3.52/0.99      ( r2_hidden(sK3,k1_connsp_2(sK2,sK3)) != iProver_top
% 3.52/0.99      | v1_xboole_0(k1_connsp_2(sK2,sK3)) != iProver_top ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_949]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_11,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.52/0.99      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.52/0.99      | v2_struct_0(X1)
% 3.52/0.99      | ~ v2_pre_topc(X1)
% 3.52/0.99      | ~ l1_pre_topc(X1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_328,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.52/0.99      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.52/0.99      | v2_struct_0(X1)
% 3.52/0.99      | ~ l1_pre_topc(X1)
% 3.52/0.99      | sK2 != X1 ),
% 3.52/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_329,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.52/0.99      | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.52/0.99      | v2_struct_0(sK2)
% 3.52/0.99      | ~ l1_pre_topc(sK2) ),
% 3.52/0.99      inference(unflattening,[status(thm)],[c_328]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_333,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.52/0.99      | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_329,c_21,c_18]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_535,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 3.52/0.99      | m1_subset_1(k1_connsp_2(sK2,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.52/0.99      inference(subtyping,[status(esa)],[c_333]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_888,plain,
% 3.52/0.99      ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | m1_subset_1(k1_connsp_2(sK2,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_535]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_6,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.52/0.99      | ~ v1_xboole_0(X1)
% 3.52/0.99      | v1_xboole_0(X0) ),
% 3.52/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_545,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
% 3.52/0.99      | ~ v1_xboole_0(X1_47)
% 3.52/0.99      | v1_xboole_0(X0_47) ),
% 3.52/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_879,plain,
% 3.52/0.99      ( m1_subset_1(X0_47,k1_zfmisc_1(X1_47)) != iProver_top
% 3.52/0.99      | v1_xboole_0(X1_47) != iProver_top
% 3.52/0.99      | v1_xboole_0(X0_47) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_545]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2061,plain,
% 3.52/0.99      ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | v1_xboole_0(k1_connsp_2(sK2,X0_47)) = iProver_top
% 3.52/0.99      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_888,c_879]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2067,plain,
% 3.52/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | v1_xboole_0(k1_connsp_2(sK2,sK3)) = iProver_top
% 3.52/0.99      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_2061]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2414,plain,
% 3.52/0.99      ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_2174,c_26,c_603,c_951,c_2067]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_0,plain,
% 3.52/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.52/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_551,plain,
% 3.52/0.99      ( r2_hidden(sK0(X0_47),X0_47) | v1_xboole_0(X0_47) ),
% 3.52/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_873,plain,
% 3.52/0.99      ( r2_hidden(sK0(X0_47),X0_47) = iProver_top
% 3.52/0.99      | v1_xboole_0(X0_47) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_551]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_13,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.52/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.52/0.99      | ~ r2_hidden(X0,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)))
% 3.52/0.99      | ~ v3_tdlat_3(X1)
% 3.52/0.99      | v2_struct_0(X1)
% 3.52/0.99      | ~ v2_pre_topc(X1)
% 3.52/0.99      | ~ l1_pre_topc(X1)
% 3.52/0.99      | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) ),
% 3.52/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_19,negated_conjecture,
% 3.52/0.99      ( v3_tdlat_3(sK2) ),
% 3.52/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_233,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.52/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.52/0.99      | ~ r2_hidden(X0,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)))
% 3.52/0.99      | v2_struct_0(X1)
% 3.52/0.99      | ~ v2_pre_topc(X1)
% 3.52/0.99      | ~ l1_pre_topc(X1)
% 3.52/0.99      | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X0)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))
% 3.52/0.99      | sK2 != X1 ),
% 3.52/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_234,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.52/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.52/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)))
% 3.52/0.99      | v2_struct_0(sK2)
% 3.52/0.99      | ~ v2_pre_topc(sK2)
% 3.52/0.99      | ~ l1_pre_topc(sK2)
% 3.52/0.99      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) ),
% 3.52/0.99      inference(unflattening,[status(thm)],[c_233]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_238,plain,
% 3.52/0.99      ( ~ r2_hidden(X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)))
% 3.52/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.52/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.52/0.99      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_234,c_21,c_20,c_18]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_239,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.52/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.52/0.99      | ~ r2_hidden(X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)))
% 3.52/0.99      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) ),
% 3.52/0.99      inference(renaming,[status(thm)],[c_238]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_537,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0_47,u1_struct_0(sK2))
% 3.52/0.99      | ~ m1_subset_1(X1_47,u1_struct_0(sK2))
% 3.52/0.99      | ~ r2_hidden(X1_47,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)))
% 3.52/0.99      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1_47)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) ),
% 3.52/0.99      inference(subtyping,[status(esa)],[c_239]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_886,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1_47))
% 3.52/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | m1_subset_1(X1_47,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | r2_hidden(X0_47,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1_47))) != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1392,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47))))) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47))
% 3.52/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | m1_subset_1(sK0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47))),u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | v1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47))) = iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_873,c_886]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2420,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3))))) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3))
% 3.52/0.99      | m1_subset_1(sK0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))),u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | v1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) = iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_2414,c_1392]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2425,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))))) = k2_pre_topc(sK2,k2_tarski(sK3,sK3))
% 3.52/0.99      | m1_subset_1(sK0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))),u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | v1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))) = iProver_top ),
% 3.52/0.99      inference(light_normalisation,[status(thm)],[c_2420,c_2414]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_7,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_544,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0_47,X1_47)
% 3.52/0.99      | r2_hidden(X0_47,X1_47)
% 3.52/0.99      | v1_xboole_0(X1_47) ),
% 3.52/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_880,plain,
% 3.52/0.99      ( m1_subset_1(X0_47,X1_47) != iProver_top
% 3.52/0.99      | r2_hidden(X0_47,X1_47) = iProver_top
% 3.52/0.99      | v1_xboole_0(X1_47) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_544]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2044,plain,
% 3.52/0.99      ( r2_hidden(sK3,u1_struct_0(sK2)) = iProver_top
% 3.52/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_885,c_880]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_874,plain,
% 3.52/0.99      ( r2_hidden(X0_47,X1_47) != iProver_top
% 3.52/0.99      | v1_xboole_0(X1_47) != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_550]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1552,plain,
% 3.52/0.99      ( r1_xboole_0(X0_47,X1_47) = iProver_top
% 3.52/0.99      | v1_xboole_0(X0_47) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_877,c_874]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_16,negated_conjecture,
% 3.52/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 3.52/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_539,negated_conjecture,
% 3.52/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 3.52/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_884,plain,
% 3.52/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2173,plain,
% 3.52/0.99      ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4)
% 3.52/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_884,c_882]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_27,plain,
% 3.52/0.99      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1351,plain,
% 3.52/0.99      ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 3.52/0.99      | v1_xboole_0(u1_struct_0(sK2))
% 3.52/0.99      | k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_542]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1352,plain,
% 3.52/0.99      ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4)
% 3.52/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1351]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2356,plain,
% 3.52/0.99      ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_2173,c_26,c_27,c_603,c_951,c_1352,c_2067]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_15,negated_conjecture,
% 3.52/0.99      ( ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
% 3.52/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_540,negated_conjecture,
% 3.52/0.99      ( ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
% 3.52/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_883,plain,
% 3.52/0.99      ( r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_540]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2359,plain,
% 3.52/0.99      ( r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
% 3.52/0.99      inference(demodulation,[status(thm)],[c_2356,c_883]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2416,plain,
% 3.52/0.99      ( r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
% 3.52/0.99      inference(demodulation,[status(thm)],[c_2414,c_2359]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2804,plain,
% 3.52/0.99      ( v1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_1552,c_2416]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2422,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3))
% 3.52/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_2414,c_886]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2423,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) = k2_pre_topc(sK2,k2_tarski(sK3,sK3))
% 3.52/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) != iProver_top ),
% 3.52/0.99      inference(light_normalisation,[status(thm)],[c_2422,c_2414]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3290,plain,
% 3.52/0.99      ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) = k2_pre_topc(sK2,k2_tarski(sK3,sK3))
% 3.52/0.99      | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) != iProver_top ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_2423,c_26]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3291,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) = k2_pre_topc(sK2,k2_tarski(sK3,sK3))
% 3.52/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) != iProver_top ),
% 3.52/0.99      inference(renaming,[status(thm)],[c_3290]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3296,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))))) = k2_pre_topc(sK2,k2_tarski(sK3,sK3))
% 3.52/0.99      | m1_subset_1(sK0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))),u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | v1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))) = iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_873,c_3291]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_5,plain,
% 3.52/0.99      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
% 3.52/0.99      | ~ r2_hidden(X0,X1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_546,plain,
% 3.52/0.99      ( m1_subset_1(k2_tarski(X0_47,X0_47),k1_zfmisc_1(X1_47))
% 3.52/0.99      | ~ r2_hidden(X0_47,X1_47) ),
% 3.52/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_878,plain,
% 3.52/0.99      ( m1_subset_1(k2_tarski(X0_47,X0_47),k1_zfmisc_1(X1_47)) = iProver_top
% 3.52/0.99      | r2_hidden(X0_47,X1_47) != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_546]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_9,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.52/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.52/0.99      | ~ l1_pre_topc(X1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_352,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.52/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.52/0.99      | sK2 != X1 ),
% 3.52/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_353,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.52/0.99      | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.52/0.99      inference(unflattening,[status(thm)],[c_352]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_534,plain,
% 3.52/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.52/0.99      | m1_subset_1(k2_pre_topc(sK2,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.52/0.99      inference(subtyping,[status(esa)],[c_353]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_889,plain,
% 3.52/0.99      ( m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.52/0.99      | m1_subset_1(k2_pre_topc(sK2,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_8,plain,
% 3.52/0.99      ( m1_subset_1(X0,X1)
% 3.52/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.52/0.99      | ~ r2_hidden(X0,X2) ),
% 3.52/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_543,plain,
% 3.52/0.99      ( m1_subset_1(X0_47,X1_47)
% 3.52/0.99      | ~ m1_subset_1(X2_47,k1_zfmisc_1(X1_47))
% 3.52/0.99      | ~ r2_hidden(X0_47,X2_47) ),
% 3.52/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_881,plain,
% 3.52/0.99      ( m1_subset_1(X0_47,X1_47) = iProver_top
% 3.52/0.99      | m1_subset_1(X2_47,k1_zfmisc_1(X1_47)) != iProver_top
% 3.52/0.99      | r2_hidden(X0_47,X2_47) != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_543]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2190,plain,
% 3.52/0.99      ( m1_subset_1(X0_47,u1_struct_0(sK2)) = iProver_top
% 3.52/0.99      | m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.52/0.99      | r2_hidden(X0_47,k2_pre_topc(sK2,X1_47)) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_889,c_881]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3024,plain,
% 3.52/0.99      ( m1_subset_1(X0_47,u1_struct_0(sK2)) = iProver_top
% 3.52/0.99      | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(X1_47,X1_47))) != iProver_top
% 3.52/0.99      | r2_hidden(X1_47,u1_struct_0(sK2)) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_878,c_2190]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_4420,plain,
% 3.52/0.99      ( m1_subset_1(sK0(k2_pre_topc(sK2,k2_tarski(X0_47,X0_47))),u1_struct_0(sK2)) = iProver_top
% 3.52/0.99      | r2_hidden(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | v1_xboole_0(k2_pre_topc(sK2,k2_tarski(X0_47,X0_47))) = iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_873,c_3024]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_4428,plain,
% 3.52/0.99      ( m1_subset_1(sK0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))),u1_struct_0(sK2)) = iProver_top
% 3.52/0.99      | r2_hidden(sK3,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | v1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))) = iProver_top ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_4420]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_4675,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK0(k2_pre_topc(sK2,k2_tarski(sK3,sK3))))) = k2_pre_topc(sK2,k2_tarski(sK3,sK3)) ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_2425,c_26,c_603,c_951,c_2044,c_2067,c_2804,c_3296,
% 3.52/0.99                 c_4428]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_4678,plain,
% 3.52/0.99      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.52/0.99      | m1_subset_1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_4675,c_889]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_933,plain,
% 3.52/0.99      ( m1_subset_1(k2_pre_topc(sK2,k2_tarski(X0_47,X0_47)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.52/0.99      | ~ m1_subset_1(k2_tarski(X0_47,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_534]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_934,plain,
% 3.52/0.99      ( m1_subset_1(k2_pre_topc(sK2,k2_tarski(X0_47,X0_47)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.52/0.99      | m1_subset_1(k2_tarski(X0_47,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_933]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_936,plain,
% 3.52/0.99      ( m1_subset_1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.52/0.99      | m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_934]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1209,plain,
% 3.52/0.99      ( m1_subset_1(k2_tarski(X0_47,X0_47),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.52/0.99      | ~ r2_hidden(X0_47,u1_struct_0(sK2)) ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_546]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1210,plain,
% 3.52/0.99      ( m1_subset_1(k2_tarski(X0_47,X0_47),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.52/0.99      | r2_hidden(X0_47,u1_struct_0(sK2)) != iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1209]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1212,plain,
% 3.52/0.99      ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.52/0.99      | r2_hidden(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.52/0.99      inference(instantiation,[status(thm)],[c_1210]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_4763,plain,
% 3.52/0.99      ( m1_subset_1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_4678,c_26,c_603,c_936,c_951,c_1212,c_2044,c_2067]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_4771,plain,
% 3.52/0.99      ( m1_subset_1(X0_47,u1_struct_0(sK2)) = iProver_top
% 3.52/0.99      | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_4763,c_881]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_5087,plain,
% 3.52/0.99      ( m1_subset_1(sK1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),X0_47),u1_struct_0(sK2)) = iProver_top
% 3.52/0.99      | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),X0_47) = iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_877,c_4771]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3,plain,
% 3.52/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 3.52/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_548,plain,
% 3.52/0.99      ( r1_xboole_0(X0_47,X1_47) | r2_hidden(sK1(X0_47,X1_47),X1_47) ),
% 3.52/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_876,plain,
% 3.52/0.99      ( r1_xboole_0(X0_47,X1_47) = iProver_top
% 3.52/0.99      | r2_hidden(sK1(X0_47,X1_47),X1_47) = iProver_top ),
% 3.52/0.99      inference(predicate_to_equality,[status(thm)],[c_548]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2366,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
% 3.52/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_2356,c_886]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2367,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
% 3.52/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
% 3.52/0.99      inference(light_normalisation,[status(thm)],[c_2366,c_2356]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3129,plain,
% 3.52/0.99      ( m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
% 3.52/0.99      | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_2367,c_27]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3130,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
% 3.52/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | r2_hidden(X0_47,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != iProver_top ),
% 3.52/0.99      inference(renaming,[status(thm)],[c_3129]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_3136,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(X0_47,k2_pre_topc(sK2,k2_tarski(sK4,sK4))))) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
% 3.52/0.99      | m1_subset_1(sK1(X0_47,k2_pre_topc(sK2,k2_tarski(sK4,sK4))),u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | r1_xboole_0(X0_47,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) = iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_876,c_3130]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_12010,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))))) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
% 3.52/0.99      | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) = iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_5087,c_3136]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_1553,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)),X1_47))) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47))
% 3.52/0.99      | m1_subset_1(X0_47,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | m1_subset_1(sK1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)),X1_47),u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0_47)),X1_47) = iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_877,c_886]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2419,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),X0_47))) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3))
% 3.52/0.99      | m1_subset_1(sK1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),X0_47),u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),X0_47) = iProver_top ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_2414,c_1553]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2426,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),X0_47))) = k2_pre_topc(sK2,k2_tarski(sK3,sK3))
% 3.52/0.99      | m1_subset_1(sK1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),X0_47),u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.52/0.99      | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),X0_47) = iProver_top ),
% 3.52/0.99      inference(light_normalisation,[status(thm)],[c_2419,c_2414]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_5333,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),X0_47))) = k2_pre_topc(sK2,k2_tarski(sK3,sK3))
% 3.52/0.99      | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),X0_47) = iProver_top ),
% 3.52/0.99      inference(global_propositional_subsumption,
% 3.52/0.99                [status(thm)],
% 3.52/0.99                [c_2426,c_26,c_5087]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_5340,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))))) = k2_pre_topc(sK2,k2_tarski(sK3,sK3)) ),
% 3.52/0.99      inference(superposition,[status(thm)],[c_5333,c_2416]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_12017,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k2_tarski(sK4,sK4)) = k2_pre_topc(sK2,k2_tarski(sK3,sK3))
% 3.52/0.99      | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) = iProver_top ),
% 3.52/0.99      inference(light_normalisation,[status(thm)],[c_12010,c_5340]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_14,negated_conjecture,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
% 3.52/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_541,negated_conjecture,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
% 3.52/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2360,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k2_tarski(sK4,sK4)) ),
% 3.52/0.99      inference(demodulation,[status(thm)],[c_2356,c_541]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(c_2417,plain,
% 3.52/0.99      ( k2_pre_topc(sK2,k2_tarski(sK4,sK4)) != k2_pre_topc(sK2,k2_tarski(sK3,sK3)) ),
% 3.52/0.99      inference(demodulation,[status(thm)],[c_2414,c_2360]) ).
% 3.52/0.99  
% 3.52/0.99  cnf(contradiction,plain,
% 3.52/0.99      ( $false ),
% 3.52/0.99      inference(minisat,[status(thm)],[c_12017,c_2417,c_2416]) ).
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  ------                               Statistics
% 3.52/0.99  
% 3.52/0.99  ------ General
% 3.52/0.99  
% 3.52/0.99  abstr_ref_over_cycles:                  0
% 3.52/0.99  abstr_ref_under_cycles:                 0
% 3.52/0.99  gc_basic_clause_elim:                   0
% 3.52/0.99  forced_gc_time:                         0
% 3.52/0.99  parsing_time:                           0.01
% 3.52/0.99  unif_index_cands_time:                  0.
% 3.52/0.99  unif_index_add_time:                    0.
% 3.52/0.99  orderings_time:                         0.
% 3.52/0.99  out_proof_time:                         0.015
% 3.52/0.99  total_time:                             0.493
% 3.52/0.99  num_of_symbols:                         52
% 3.52/0.99  num_of_terms:                           17056
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing
% 3.52/0.99  
% 3.52/0.99  num_of_splits:                          0
% 3.52/0.99  num_of_split_atoms:                     0
% 3.52/0.99  num_of_reused_defs:                     0
% 3.52/0.99  num_eq_ax_congr_red:                    25
% 3.52/0.99  num_of_sem_filtered_clauses:            1
% 3.52/0.99  num_of_subtypes:                        2
% 3.52/0.99  monotx_restored_types:                  0
% 3.52/0.99  sat_num_of_epr_types:                   0
% 3.52/0.99  sat_num_of_non_cyclic_types:            0
% 3.52/0.99  sat_guarded_non_collapsed_types:        0
% 3.52/0.99  num_pure_diseq_elim:                    0
% 3.52/0.99  simp_replaced_by:                       0
% 3.52/0.99  res_preprocessed:                       93
% 3.52/0.99  prep_upred:                             0
% 3.52/0.99  prep_unflattend:                        12
% 3.52/0.99  smt_new_axioms:                         0
% 3.52/0.99  pred_elim_cands:                        4
% 3.52/0.99  pred_elim:                              4
% 3.52/0.99  pred_elim_cl:                           4
% 3.52/0.99  pred_elim_cycles:                       7
% 3.52/0.99  merged_defs:                            0
% 3.52/0.99  merged_defs_ncl:                        0
% 3.52/0.99  bin_hyper_res:                          0
% 3.52/0.99  prep_cycles:                            4
% 3.52/0.99  pred_elim_time:                         0.004
% 3.52/0.99  splitting_time:                         0.
% 3.52/0.99  sem_filter_time:                        0.
% 3.52/0.99  monotx_time:                            0.
% 3.52/0.99  subtype_inf_time:                       0.
% 3.52/0.99  
% 3.52/0.99  ------ Problem properties
% 3.52/0.99  
% 3.52/0.99  clauses:                                18
% 3.52/0.99  conjectures:                            4
% 3.52/0.99  epr:                                    3
% 3.52/0.99  horn:                                   13
% 3.52/0.99  ground:                                 4
% 3.52/0.99  unary:                                  4
% 3.52/0.99  binary:                                 8
% 3.52/0.99  lits:                                   39
% 3.52/0.99  lits_eq:                                3
% 3.52/0.99  fd_pure:                                0
% 3.52/0.99  fd_pseudo:                              0
% 3.52/0.99  fd_cond:                                0
% 3.52/0.99  fd_pseudo_cond:                         0
% 3.52/0.99  ac_symbols:                             0
% 3.52/0.99  
% 3.52/0.99  ------ Propositional Solver
% 3.52/0.99  
% 3.52/0.99  prop_solver_calls:                      31
% 3.52/0.99  prop_fast_solver_calls:                 1036
% 3.52/0.99  smt_solver_calls:                       0
% 3.52/0.99  smt_fast_solver_calls:                  0
% 3.52/0.99  prop_num_of_clauses:                    6899
% 3.52/0.99  prop_preprocess_simplified:             9303
% 3.52/0.99  prop_fo_subsumed:                       53
% 3.52/0.99  prop_solver_time:                       0.
% 3.52/0.99  smt_solver_time:                        0.
% 3.52/0.99  smt_fast_solver_time:                   0.
% 3.52/0.99  prop_fast_solver_time:                  0.
% 3.52/0.99  prop_unsat_core_time:                   0.
% 3.52/0.99  
% 3.52/0.99  ------ QBF
% 3.52/0.99  
% 3.52/0.99  qbf_q_res:                              0
% 3.52/0.99  qbf_num_tautologies:                    0
% 3.52/0.99  qbf_prep_cycles:                        0
% 3.52/0.99  
% 3.52/0.99  ------ BMC1
% 3.52/0.99  
% 3.52/0.99  bmc1_current_bound:                     -1
% 3.52/0.99  bmc1_last_solved_bound:                 -1
% 3.52/0.99  bmc1_unsat_core_size:                   -1
% 3.52/0.99  bmc1_unsat_core_parents_size:           -1
% 3.52/0.99  bmc1_merge_next_fun:                    0
% 3.52/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.52/0.99  
% 3.52/0.99  ------ Instantiation
% 3.52/0.99  
% 3.52/0.99  inst_num_of_clauses:                    1283
% 3.52/0.99  inst_num_in_passive:                    395
% 3.52/0.99  inst_num_in_active:                     768
% 3.52/0.99  inst_num_in_unprocessed:                120
% 3.52/0.99  inst_num_of_loops:                      850
% 3.52/0.99  inst_num_of_learning_restarts:          0
% 3.52/0.99  inst_num_moves_active_passive:          79
% 3.52/0.99  inst_lit_activity:                      0
% 3.52/0.99  inst_lit_activity_moves:                0
% 3.52/0.99  inst_num_tautologies:                   0
% 3.52/0.99  inst_num_prop_implied:                  0
% 3.52/0.99  inst_num_existing_simplified:           0
% 3.52/0.99  inst_num_eq_res_simplified:             0
% 3.52/0.99  inst_num_child_elim:                    0
% 3.52/0.99  inst_num_of_dismatching_blockings:      795
% 3.52/0.99  inst_num_of_non_proper_insts:           1948
% 3.52/0.99  inst_num_of_duplicates:                 0
% 3.52/0.99  inst_inst_num_from_inst_to_res:         0
% 3.52/0.99  inst_dismatching_checking_time:         0.
% 3.52/0.99  
% 3.52/0.99  ------ Resolution
% 3.52/0.99  
% 3.52/0.99  res_num_of_clauses:                     0
% 3.52/0.99  res_num_in_passive:                     0
% 3.52/0.99  res_num_in_active:                      0
% 3.52/0.99  res_num_of_loops:                       97
% 3.52/0.99  res_forward_subset_subsumed:            107
% 3.52/0.99  res_backward_subset_subsumed:           0
% 3.52/0.99  res_forward_subsumed:                   0
% 3.52/0.99  res_backward_subsumed:                  0
% 3.52/0.99  res_forward_subsumption_resolution:     0
% 3.52/0.99  res_backward_subsumption_resolution:    0
% 3.52/0.99  res_clause_to_clause_subsumption:       2585
% 3.52/0.99  res_orphan_elimination:                 0
% 3.52/0.99  res_tautology_del:                      181
% 3.52/0.99  res_num_eq_res_simplified:              0
% 3.52/0.99  res_num_sel_changes:                    0
% 3.52/0.99  res_moves_from_active_to_pass:          0
% 3.52/0.99  
% 3.52/0.99  ------ Superposition
% 3.52/0.99  
% 3.52/0.99  sup_time_total:                         0.
% 3.52/0.99  sup_time_generating:                    0.
% 3.52/0.99  sup_time_sim_full:                      0.
% 3.52/0.99  sup_time_sim_immed:                     0.
% 3.52/0.99  
% 3.52/0.99  sup_num_of_clauses:                     892
% 3.52/0.99  sup_num_in_active:                      164
% 3.52/0.99  sup_num_in_passive:                     728
% 3.52/0.99  sup_num_of_loops:                       168
% 3.52/0.99  sup_fw_superposition:                   435
% 3.52/0.99  sup_bw_superposition:                   527
% 3.52/0.99  sup_immediate_simplified:               113
% 3.52/0.99  sup_given_eliminated:                   0
% 3.52/0.99  comparisons_done:                       0
% 3.52/0.99  comparisons_avoided:                    0
% 3.52/0.99  
% 3.52/0.99  ------ Simplifications
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  sim_fw_subset_subsumed:                 17
% 3.52/0.99  sim_bw_subset_subsumed:                 6
% 3.52/0.99  sim_fw_subsumed:                        21
% 3.52/0.99  sim_bw_subsumed:                        0
% 3.52/0.99  sim_fw_subsumption_res:                 0
% 3.52/0.99  sim_bw_subsumption_res:                 0
% 3.52/0.99  sim_tautology_del:                      10
% 3.52/0.99  sim_eq_tautology_del:                   1
% 3.52/0.99  sim_eq_res_simp:                        0
% 3.52/0.99  sim_fw_demodulated:                     0
% 3.52/0.99  sim_bw_demodulated:                     5
% 3.52/0.99  sim_light_normalised:                   81
% 3.52/0.99  sim_joinable_taut:                      0
% 3.52/0.99  sim_joinable_simp:                      0
% 3.52/0.99  sim_ac_normalised:                      0
% 3.52/0.99  sim_smt_subsumption:                    0
% 3.52/0.99  
%------------------------------------------------------------------------------
